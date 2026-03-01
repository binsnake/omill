/// @file OllvmPlugin.cpp
/// LLVM pass plugin for per-function OLLVM obfuscation via annotations.
///
/// Load with: clang -fpass-plugin=OllvmPlugin.dll ...
/// Or:        opt -load-pass-plugin=OllvmPlugin.dll -passes=ollvm-obfuscate ...
///
/// Default-enable passes for ALL functions via environment variable:
///   set OLLVM_DEFAULTS=flatten,indirect-calls,opaque-constants
///   set OLLVM_SEED=42
///   clang -fpass-plugin=OllvmPlugin.dll -O2 ...
///
/// Or via pass parameters:
///   opt -passes='ollvm-obfuscate<seed=42;defaults=all>' ...
///
/// OLLVM_NONE annotation opts a function out of everything, including defaults.
///
/// Annotate functions in source with OLLVM_FLATTEN, OLLVM_SUBSTITUTE, etc.

#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Passes/PassPlugin.h>
#include <llvm/Support/raw_ostream.h>

#include <cstdint>
#include <cstdlib>
#include <random>
#include <string>
#include <vector>

#include "BogusControlFlow.h"
#include "ConstantUnfolding.h"
#include "Flattening.h"
#include "OpaquePredicates.h"
#include "StringEncryption.h"
#include "Substitution.h"
#include "Vectorize.h"

#ifdef OLLVM_HAS_PRIVATE
#include "AntiSymbolic.h"
#include "CFIPoisoning.h"
#include "DeadMemorySemantics.h"
#include "EncodeLiterals.h"
#include "EntangleArithmetic.h"
#include "IndirectCalls.h"
#include "OpaqueAddressing.h"
#include "OpaqueConstants.h"
#endif

namespace {

// ---------------------------------------------------------------------------
// Annotation helpers
// ---------------------------------------------------------------------------

/// Collect all annotation strings attached to @p F via llvm.global.annotations.
static std::vector<llvm::StringRef>
collectAnnotations(llvm::Function &F) {
  std::vector<llvm::StringRef> result;
  auto *GA = F.getParent()->getNamedGlobal("llvm.global.annotations");
  if (!GA || !GA->hasInitializer())
    return result;
  auto *CA = llvm::dyn_cast<llvm::ConstantArray>(GA->getInitializer());
  if (!CA)
    return result;
  for (unsigned i = 0, e = CA->getNumOperands(); i < e; ++i) {
    auto *CS = llvm::dyn_cast<llvm::ConstantStruct>(CA->getOperand(i));
    if (!CS || CS->getNumOperands() < 2)
      continue;
    auto *annotatedFn = llvm::dyn_cast<llvm::Function>(
        CS->getOperand(0)->stripPointerCasts());
    if (annotatedFn != &F)
      continue;
    auto *annoGV = llvm::dyn_cast<llvm::GlobalVariable>(
        CS->getOperand(1)->stripPointerCasts());
    if (!annoGV || !annoGV->hasInitializer())
      continue;
    if (auto *cda =
            llvm::dyn_cast<llvm::ConstantDataArray>(annoGV->getInitializer())) {
      result.push_back(cda->getAsString().rtrim('\0'));
    }
  }
  return result;
}

/// Return true when @p annos contains @p key.
static bool hasAnno(const std::vector<llvm::StringRef> &annos,
                    llvm::StringRef key) {
  for (auto &a : annos)
    if (a == key)
      return true;
  return false;
}

// ---------------------------------------------------------------------------
// Seed derivation (same splitmix as ollvm-obf/main.cpp)
// ---------------------------------------------------------------------------

static uint32_t mixSeed(uint32_t base, uint32_t salt) {
  uint32_t x = base ^ salt;
  x ^= x >> 16;
  x *= 0x7feb352du;
  x ^= x >> 15;
  x *= 0x846ca68bu;
  x ^= x >> 16;
  return x;
}

// ---------------------------------------------------------------------------
// FnFlags — per-function pass selection
// ---------------------------------------------------------------------------

struct FnFlags {
  bool flatten = false;
  bool substitute = false;
  bool stringEncrypt = false;
  bool constUnfold = false;
  bool vectorize = false;
  bool opaquePred = false;
  bool bogusCf = false;
#ifdef OLLVM_HAS_PRIVATE
  bool deadMemory = false;
  bool opaqueAddr = false;
  bool entangleArith = false;
  bool opaqueConst = false;
  bool encodeLit = false;
  bool indirectCalls = false;
  bool cfiPoison = false;
  bool antiSym = false;
#endif

  bool any() const {
    bool r = flatten || substitute || stringEncrypt || constUnfold ||
             vectorize || opaquePred || bogusCf;
#ifdef OLLVM_HAS_PRIVATE
    r = r || deadMemory || opaqueAddr || entangleArith || opaqueConst ||
         encodeLit || indirectCalls || cfiPoison || antiSym;
#endif
    return r;
  }

  FnFlags operator|(const FnFlags &o) const {
    FnFlags r;
    r.flatten       = flatten       || o.flatten;
    r.substitute    = substitute    || o.substitute;
    r.stringEncrypt = stringEncrypt || o.stringEncrypt;
    r.constUnfold   = constUnfold   || o.constUnfold;
    r.vectorize     = vectorize     || o.vectorize;
    r.opaquePred    = opaquePred    || o.opaquePred;
    r.bogusCf       = bogusCf       || o.bogusCf;
#ifdef OLLVM_HAS_PRIVATE
    r.deadMemory    = deadMemory    || o.deadMemory;
    r.opaqueAddr    = opaqueAddr    || o.opaqueAddr;
    r.entangleArith = entangleArith || o.entangleArith;
    r.opaqueConst   = opaqueConst   || o.opaqueConst;
    r.encodeLit     = encodeLit     || o.encodeLit;
    r.indirectCalls = indirectCalls || o.indirectCalls;
    r.cfiPoison     = cfiPoison     || o.cfiPoison;
    r.antiSym       = antiSym       || o.antiSym;
#endif
    return r;
  }
};

// ---------------------------------------------------------------------------
// Configuration: env vars + pass parameters
// ---------------------------------------------------------------------------
/// Parse a comma-separated string like "flatten,indirect-calls,all" into flags.
static FnFlags parseFlagString(llvm::StringRef str) {
  FnFlags df;
  llvm::SmallVector<llvm::StringRef, 16> parts;
  str.split(parts, ',', /*MaxSplit=*/-1, /*KeepEmpty=*/false);
  for (auto n : parts) {
    n = n.trim();
    if (n == "flatten")               df.flatten = true;
    else if (n == "substitute")       df.substitute = true;
    else if (n == "string-encrypt")   df.stringEncrypt = true;
    else if (n == "const-unfold")     df.constUnfold = true;
    else if (n == "vectorize")        df.vectorize = true;
    else if (n == "opaque-predicates") df.opaquePred = true;
    else if (n == "bogus-cf")         df.bogusCf = true;
#ifdef OLLVM_HAS_PRIVATE
    else if (n == "dead-memory")          df.deadMemory = true;
    else if (n == "opaque-addressing")    df.opaqueAddr = true;
    else if (n == "entangle-arithmetic")  df.entangleArith = true;
    else if (n == "opaque-constants")     df.opaqueConst = true;
    else if (n == "encode-literals")      df.encodeLit = true;
    else if (n == "indirect-calls")       df.indirectCalls = true;
    else if (n == "cfi-poisoning")        df.cfiPoison = true;
    else if (n == "anti-symbolic")        df.antiSym = true;
#endif
    else if (n == "all") {
      df.flatten = df.substitute = df.stringEncrypt = df.constUnfold = true;
      df.vectorize = df.opaquePred = df.bogusCf = true;
#ifdef OLLVM_HAS_PRIVATE
      df.deadMemory = df.opaqueAddr = df.entangleArith = true;
      df.opaqueConst = df.encodeLit = df.indirectCalls = true;
      df.cfiPoison = df.antiSym = true;
#endif
    } else if (!n.empty()) {
      llvm::errs() << "ollvm-plugin: unknown pass '" << n << "'\n";
    }
  }
  return df;
}

// ---------------------------------------------------------------------------
// The module pass
// ---------------------------------------------------------------------------

struct OllvmObfuscatePass : llvm::PassInfoMixin<OllvmObfuscatePass> {
  uint32_t seed;
  FnFlags paramDefaults; // defaults parsed from pass parameters (if any)

  explicit OllvmObfuscatePass(uint32_t s = 0, FnFlags pd = {})
      : seed(s), paramDefaults(pd) {}

  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager & /*MAM*/) {
    // Resolve seed: ctor arg > OLLVM_SEED env > hardcoded default.
    uint32_t effectiveSeed = seed;
    if (effectiveSeed == 0) {
      if (auto *envSeed = std::getenv("OLLVM_SEED")) {
        char *end = nullptr;
        auto v = std::strtoul(envSeed, &end, 0);
        if (end && *end == '\0')
          effectiveSeed = static_cast<uint32_t>(v);
      }
    }
    if (effectiveSeed == 0)
      effectiveSeed = 0xB16B00B5u;

    // Merge defaults: pass parameters | OLLVM_DEFAULTS env var.
    FnFlags defaults = paramDefaults;
    if (auto *envDef = std::getenv("OLLVM_DEFAULTS"))
      defaults = defaults | parseFlagString(envDef);

    bool wantStringEncrypt = false;
    std::vector<std::pair<llvm::Function *, FnFlags>> plan;

    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      auto annos = collectAnnotations(F);

      // OLLVM_NONE opts out entirely, even from defaults.
      if (hasAnno(annos, "ollvm_none"))
        continue;

      // Start with defaults for this function.
      FnFlags flags = defaults;

      // OR in any per-function annotations.
      if (!annos.empty()) {
        FnFlags af;
        bool all = hasAnno(annos, "ollvm_all");
        af.flatten       = all || hasAnno(annos, "ollvm_flatten");
        af.substitute    = all || hasAnno(annos, "ollvm_substitute");
        af.stringEncrypt = all || hasAnno(annos, "ollvm_string_encrypt");
        af.constUnfold   = all || hasAnno(annos, "ollvm_const_unfold");
        af.vectorize     = all || hasAnno(annos, "ollvm_vectorize");
        af.opaquePred    = all || hasAnno(annos, "ollvm_opaque_predicates");
        af.bogusCf       = all || hasAnno(annos, "ollvm_bogus_cf");
#ifdef OLLVM_HAS_PRIVATE
        af.deadMemory    = all || hasAnno(annos, "ollvm_dead_memory");
        af.opaqueAddr    = all || hasAnno(annos, "ollvm_opaque_addressing");
        af.entangleArith = all || hasAnno(annos, "ollvm_entangle_arithmetic");
        af.opaqueConst   = all || hasAnno(annos, "ollvm_opaque_constants");
        af.encodeLit     = all || hasAnno(annos, "ollvm_encode_literals");
        af.indirectCalls = all || hasAnno(annos, "ollvm_indirect_calls");
        af.cfiPoison     = all || hasAnno(annos, "ollvm_cfi_poisoning");
        af.antiSym       = all || hasAnno(annos, "ollvm_anti_symbolic");
#endif
        flags = flags | af;
      }

      if (!flags.any())
        continue;

      if (flags.stringEncrypt)
        wantStringEncrypt = true;
      plan.emplace_back(&F, flags);
    }

    if (plan.empty())
      return llvm::PreservedAnalyses::all();

    // -----------------------------------------------------------------------
    // Module-level passes first.
    // -----------------------------------------------------------------------
    if (wantStringEncrypt)
      ollvm::encryptStringsModule(M, mixSeed(effectiveSeed, 0x11A48D53u));

    // -----------------------------------------------------------------------
    // Per-function passes in fixed order matching ollvm-obf.
    // We run each transform across all requesting functions before the next
    // transform to maintain deterministic ordering.
    // -----------------------------------------------------------------------

    // 1. Substitution
    {
      std::mt19937 rng(mixSeed(effectiveSeed, 0x5B2E6D4Fu));
      for (auto &[fn, flags] : plan)
        if (flags.substitute)
          ollvm::substituteModule(M, mixSeed(effectiveSeed, 0x5B2E6D4Fu));
    }

    // Opaque predicates (before CFF so flattening sees the injected branches).
    for (auto &[fn, flags] : plan) {
      if (flags.opaquePred) {
        ollvm::insertOpaquePredicatesModule(M, mixSeed(effectiveSeed, 0xD4E5F6A7u));
        break; // module-level — run once
      }
    }

    // Bogus control flow (before CFF).
    for (auto &[fn, flags] : plan) {
      if (flags.bogusCf) {
        ollvm::insertBogusControlFlowModule(M, mixSeed(effectiveSeed, 0xE7F8A9B0u));
        break; // module-level — run once
      }
    }

    // Flattening.
    for (auto &[fn, flags] : plan) {
      if (flags.flatten) {
        ollvm::flattenModule(M, mixSeed(effectiveSeed, 0xA1F3707Bu));
        break; // module-level — run once
      }
    }

    // Constant unfolding.
    for (auto &[fn, flags] : plan) {
      if (flags.constUnfold) {
        ollvm::unfoldConstantsModule(M, mixSeed(effectiveSeed, 0xC93A1E27u));
        break; // module-level — run once
      }
    }

#ifdef OLLVM_HAS_PRIVATE
    // Private passes — same order as PrivatePasses.cpp dispatch.
    auto anyFlag = [&](auto pred) {
      for (auto &[fn, flags] : plan)
        if (pred(flags)) return true;
      return false;
    };
    if (anyFlag([](auto &f){ return f.deadMemory; }))
      ollvm::deadMemorySemanticsModule(M, mixSeed(effectiveSeed, 0x71C4E8A3u));
    if (anyFlag([](auto &f){ return f.opaqueAddr; }))
      ollvm::opaqueAddressingModule(M, mixSeed(effectiveSeed, 0xF2A7B3D1u));
    if (anyFlag([](auto &f){ return f.entangleArith; }))
      ollvm::entangleArithmeticModule(M, mixSeed(effectiveSeed, 0xD8C14E6Bu));
    if (anyFlag([](auto &f){ return f.opaqueConst; }))
      ollvm::opaqueConstantsModule(M, mixSeed(effectiveSeed, 0xA3B7F219u));
    if (anyFlag([](auto &f){ return f.encodeLit; }))
      ollvm::encodeLiteralsModule(M, mixSeed(effectiveSeed, 0x4B9F27A3u));
    if (anyFlag([](auto &f){ return f.indirectCalls; }))
      ollvm::indirectCallsModule(M, mixSeed(effectiveSeed, 0x8E3D5C19u));
    if (anyFlag([](auto &f){ return f.cfiPoison; }))
      ollvm::cfiPoisoningModule(M, mixSeed(effectiveSeed, 0x5D2F9E47u));
    if (anyFlag([](auto &f){ return f.antiSym; }))
      ollvm::antiSymbolicModule(M, mixSeed(effectiveSeed, 0xE6A1C3B5u));
#endif

    // Vectorization (must run last).
    for (auto &[fn, flags] : plan) {
      if (flags.vectorize) {
        ollvm::vectorizeModule(M, mixSeed(effectiveSeed, 0x3D7C9A61u));
        break; // module-level — run once
      }
    }

    return llvm::PreservedAnalyses::none();
  }
};

// ---------------------------------------------------------------------------
// Seed parsing: "ollvm-obfuscate" or "ollvm-obfuscate<seed=12345>"
// ---------------------------------------------------------------------------

/// Parse pass parameters: "" | "seed=42" | "defaults=all" | "seed=42;defaults=flatten,bogus-cf"
static bool parseParams(llvm::StringRef params, uint32_t &outSeed,
                        FnFlags &outDefaults) {
  outSeed = 0;
  outDefaults = {};
  if (params.empty())
    return true;
  llvm::SmallVector<llvm::StringRef, 4> kvs;
  params.split(kvs, ';', /*MaxSplit=*/-1, /*KeepEmpty=*/false);
  for (auto kv : kvs) {
    kv = kv.trim();
    if (kv.consume_front("seed=")) {
      unsigned long long v;
      if (kv.getAsInteger(0, v))
        return false;
      outSeed = static_cast<uint32_t>(v);
    } else if (kv.consume_front("defaults=")) {
      outDefaults = outDefaults | parseFlagString(kv);
    } else {
      return false;
    }
  }
  return true;
}

}  // namespace

// ---------------------------------------------------------------------------
// Plugin entry point
// ---------------------------------------------------------------------------
#ifdef _WIN32
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wdll-attribute-on-redeclaration"
extern "C" __declspec(dllexport) ::llvm::PassPluginLibraryInfo
#else
extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
#endif
llvmGetPassPluginInfo() {
  return {
      LLVM_PLUGIN_API_VERSION, "OllvmPlugin", LLVM_VERSION_STRING,
      [](llvm::PassBuilder &PB) {
        // Allow explicit invocation:
        //   -passes='ollvm-obfuscate'
        //   -passes='ollvm-obfuscate<seed=42>'
        //   -passes='ollvm-obfuscate<seed=42;defaults=flatten,bogus-cf>'
        PB.registerPipelineParsingCallback(
            [](llvm::StringRef Name, llvm::ModulePassManager &MPM,
               llvm::ArrayRef<llvm::PassBuilder::PipelineElement>) {
              if (Name.consume_front("ollvm-obfuscate")) {
                uint32_t s;
                FnFlags df;
                if (!parseParams(Name, s, df))
                  return false;
                MPM.addPass(OllvmObfuscatePass(s, df));
                return true;
              }
              return false;
            });

        // Also run automatically at the end of -O1/-O2/-O3 pipelines.
        PB.registerOptimizerLastEPCallback(
            [](llvm::ModulePassManager &MPM, llvm::OptimizationLevel,
               llvm::ThinOrFullLTOPhase) {
              MPM.addPass(OllvmObfuscatePass());
            });
      }};
}
#ifdef _WIN32
#pragma clang diagnostic pop
#endif
