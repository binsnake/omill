#include <llvm/Bitcode/BitcodeWriter.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/InitLLVM.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/ToolOutputFile.h>
#include <llvm/Support/raw_ostream.h>

#include <cstdint>

#include "ArithmeticEncoding.h"
#include "BogusControlFlow.h"
#include "BMIMutation.h"
#include "CodeCloning.h"
#include "ConstantUnfolding.h"
#include "Flattening.h"
#include "FunctionOutlining.h"
#include "IfConversion.h"
#include "InstructionScheduling.h"
#include "LoopToRecursion.h"
#include "OpaquePredicates.h"
#include "RegisterPressure.h"
#include "StackRandomization.h"
#include "StringEncryption.h"
#include "Substitution.h"
#include "Vectorize.h"
#include "PassFilter.h"

#ifdef OLLVM_HAS_PRIVATE
#include "PrivatePasses.h"
#endif


static llvm::cl::opt<std::string> InputFilename(llvm::cl::Positional,
                                           llvm::cl::desc("<input .ll/.bc file>"),
                                           llvm::cl::Required);

static llvm::cl::opt<std::string> OutputFilename("o", llvm::cl::desc("Output filename"),
                                            llvm::cl::value_desc("filename"),
                                            llvm::cl::init("-"));

static llvm::cl::opt<bool> DoFlatten("flatten",
                                llvm::cl::desc("Apply control flow flattening"),
                                llvm::cl::init(false));

static llvm::cl::opt<bool> DoSubstitute("substitute",
                                   llvm::cl::desc("Apply MBA instruction substitution"),
                                   llvm::cl::init(false));

static llvm::cl::opt<bool> DoStringEncrypt("string-encrypt",
                                      llvm::cl::desc("Apply XOR-based string encryption"),
                                      llvm::cl::init(false));

static llvm::cl::opt<bool> DoConstUnfold("const-unfold",
                                    llvm::cl::desc("Replace constants with equivalent expressions"),
                                    llvm::cl::init(false));

static llvm::cl::opt<bool> DoOpaquePredicates("opaque-predicates",
                                         llvm::cl::desc("Insert opaque predicates"),
                                         llvm::cl::init(false));

static llvm::cl::opt<bool> DoBogusControlFlow("bogus-control-flow",
                                         llvm::cl::desc("Insert bogus control flow"),
                                         llvm::cl::init(false));


static llvm::cl::opt<bool> DoBMIMutate("bmi-mutate",
                                  llvm::cl::desc("Rewrite expressions with BMI1/BMI2 bit-manipulation"),
                                  llvm::cl::init(false));

static llvm::cl::opt<bool> DoSchedule("schedule-instructions",
                                llvm::cl::desc("Randomize instruction scheduling within basic blocks"),
                                llvm::cl::init(false));

static llvm::cl::opt<bool> DoIfConvert("if-convert",
                                 llvm::cl::desc("Convert diamond branches to select instructions"),
                                 llvm::cl::init(false));

static llvm::cl::opt<bool> DoOutline("outline-functions",
                               llvm::cl::desc("Outline basic blocks into separate functions"),
                               llvm::cl::init(false));

static llvm::cl::opt<bool> DoStackRandomize("stack-randomize",
                                      llvm::cl::desc("Randomize stack frame layout with padding and shuffling"),
                                      llvm::cl::init(false));

static llvm::cl::opt<bool> DoArithEncode("arith-encode",
                                   llvm::cl::desc("Encode integer allocas with affine transforms"),
                                   llvm::cl::init(false));

static llvm::cl::opt<bool> DoLoopToRecursion("loop-to-recursion",
                                       llvm::cl::desc("Convert simple loops to tail-recursive functions"),
                                       llvm::cl::init(false));

static llvm::cl::opt<bool> DoCodeClone("code-clone",
                                  llvm::cl::desc("Clone internal functions with variation"),
                                  llvm::cl::init(false));

static llvm::cl::opt<bool> DoRegPressure("reg-pressure",
                                    llvm::cl::desc("Extend register live ranges with inline asm anchors"),
                                    llvm::cl::init(false));

static llvm::cl::opt<bool> DoVectorize("vectorize",
                                  llvm::cl::desc("Replace i32/i64 scalar ops with SSE vector ops"),
                                  llvm::cl::init(false));

static llvm::cl::opt<bool> DoVectorizeData(
    "vectorize-data",
    llvm::cl::desc("Enable vectorized i32/i64 stack data mutation (lane-0 load/store)"),
    llvm::cl::init(true));

static llvm::cl::opt<bool> DoVectorizeBitwise(
    "vectorize-bitwise",
    llvm::cl::desc("Lower vectorized add/sub through bitwise ops (xor/and/shl)"),
    llvm::cl::init(false));

static llvm::cl::opt<bool> DoVectorizeI64(
    "vectorize-i64",
    llvm::cl::desc("Also vectorize i64 ops using <2 x i64> (SSE4.2)"),
    llvm::cl::init(true));

static llvm::cl::opt<unsigned> VectorizePercent(
    "vectorize-percent",
    llvm::cl::desc("Percent of eligible scalar ops to vectorize (0-100)"),
    llvm::cl::init(40));

static llvm::cl::opt<unsigned> ObfSeed(
    "seed",
    llvm::cl::desc("Base RNG seed for deterministic obfuscation"),
    llvm::cl::init(0xB16B00B5u));

static llvm::cl::opt<bool> VerifyEach(
    "verify-each",
    llvm::cl::desc("Run LLVM verifier after each obfuscation pass"),
    llvm::cl::init(false));

static llvm::cl::opt<unsigned> MinInstructions(
    "min-instructions",
    llvm::cl::desc("Skip functions with fewer than N instructions (default: 0 = no filter)"),
    llvm::cl::init(0));

static llvm::cl::opt<unsigned> TransformPercent(
    "transform-percent",
    llvm::cl::desc("Per-site transform probability 0-100 (default: 100 = always)"),
    llvm::cl::init(100));

static llvm::cl::opt<bool> SkipInlineAsm(
    "skip-inline-asm",
    llvm::cl::desc("Skip functions containing inline assembly"),
    llvm::cl::init(false));

namespace {

// Splitmix-style 32-bit mixer to derive independent deterministic seeds
// for each transform from a single base seed.
uint32_t mixSeed(uint32_t base, uint32_t salt) {
  uint32_t x = base ^ salt;
  x ^= x >> 16;
  x *= 0x7feb352du;
  x ^= x >> 15;
  x *= 0x846ca68bu;
  x ^= x >> 16;
  return x;
}

}  // namespace

int main(int argc, char **argv) {
  llvm::InitLLVM X(argc, argv);
  llvm::cl::ParseCommandLineOptions(argc, argv, "OLLVM-style obfuscation tool\n");

  llvm::LLVMContext Context;
  llvm::SMDiagnostic Err;

  auto M = llvm::parseIRFile(InputFilename, Err, Context);
  if (!M) {
    Err.print(argv[0], llvm::errs());
    return 1;
  }

  const uint32_t base_seed = static_cast<uint32_t>(ObfSeed);

  ollvm::FilterConfig filter;
  filter.min_instructions = MinInstructions;
  filter.skip_inline_asm = SkipInlineAsm;
  filter.transform_percent = TransformPercent;

  // Helper: verify module after a named pass, abort early with useful diag.
  auto verifyAfter = [&](const char *pass_name) {
    if (!VerifyEach) return;
    if (llvm::verifyModule(*M, &llvm::errs())) {
      llvm::errs() << "ollvm-obf: module verification failed after "
             << pass_name << "\n";
      std::exit(1);
    }
  };

  // Apply passes in a fixed order for determinism and compatibility.
  // 1. String encryption first (operates on global constants).
  // 2. Code cloning (before per-function transforms).
  // 3. MBA substitution (arithmetic-level).
  // 4. If-conversion (reduces branches before CFG transforms).
  // 5. Loop-to-recursion (before CFG obfuscation).
  // 6. Control flow transforms (CFF, opaque predicates, bogus CF).
  // 7. BMI mutation, constant-level transforms.
  // 8. Private passes (if compiled in).
  // 9. Function outlining, scheduling, arithmetic encoding, stack randomization.
  // 10. Vectorize (converts scalar to vector).
  // 11. Register pressure (must be last — adds inline asm).
  if (DoStringEncrypt) {
    ollvm::encryptStringsModule(*M, mixSeed(base_seed, 0x11A48D53u));
    verifyAfter("string-encrypt");
  }

  if (DoCodeClone) {
    ollvm::cloneFunctionsModule(*M, mixSeed(base_seed, 0xD4A2E7B1u), filter);
    verifyAfter("code-clone");
  }

  if (DoSubstitute) {
    ollvm::substituteModule(*M, mixSeed(base_seed, 0x5B2E6D4Fu), filter);
    verifyAfter("substitute");
  }

  if (DoIfConvert) {
    ollvm::ifConvertModule(*M, mixSeed(base_seed, 0x2F7D9C45u), filter);
    verifyAfter("if-convert");
  }

  if (DoLoopToRecursion) {
    ollvm::loopToRecursionModule(*M, mixSeed(base_seed, 0x6B3E81D7u), filter);
    verifyAfter("loop-to-recursion");
  }

  if (DoFlatten) {
    ollvm::flattenModule(*M, mixSeed(base_seed, 0xA1F3707Bu), filter);
    verifyAfter("flatten");
  }

  if (DoOpaquePredicates) {
    ollvm::insertOpaquePredicatesModule(*M, mixSeed(base_seed, 0xE4D29B13u), filter);
    verifyAfter("opaque-predicates");
  }

  if (DoBogusControlFlow) {
    ollvm::insertBogusControlFlowModule(*M, mixSeed(base_seed, 0x7F1A83C5u), filter);
    verifyAfter("bogus-control-flow");
  }


  if (DoBMIMutate) {
    ollvm::bmiMutateModule(*M, mixSeed(base_seed, 0x4E8B2F71u), filter);
    verifyAfter("bmi-mutate");
  }

  if (DoConstUnfold) {
    ollvm::unfoldConstantsModule(*M, mixSeed(base_seed, 0xC93A1E27u), filter);
    verifyAfter("const-unfold");
  }

#ifdef OLLVM_HAS_PRIVATE
  ollvm::priv::runPasses(*M, base_seed, filter);
  verifyAfter("private-passes");
#endif

  if (DoSchedule) {
    ollvm::scheduleInstructionsModule(*M, mixSeed(base_seed, 0x8C2E5A19u), filter);
    verifyAfter("schedule-instructions");
  }

  if (DoOutline) {
    ollvm::outlineFunctionsModule(*M, mixSeed(base_seed, 0xA5C4F239u), filter);
    verifyAfter("outline-functions");
  }

  if (DoArithEncode) {
    ollvm::encodeAllocasModule(*M, mixSeed(base_seed, 0x1E9B47D3u), filter);
    verifyAfter("arith-encode");
  }

  if (DoStackRandomize) {
    ollvm::randomizeStackModule(*M, mixSeed(base_seed, 0x7C5DA128u), filter);
    verifyAfter("stack-randomize");
  }

  // Must run last.
  if (DoVectorize) {
    ollvm::VectorizeOptions opts;
    opts.vectorize_data = DoVectorizeData;
    opts.vectorize_bitwise = DoVectorizeBitwise;
    opts.vectorize_i64 = DoVectorizeI64;
    opts.transform_percent = VectorizePercent;
    ollvm::vectorizeModule(*M, mixSeed(base_seed, 0x3D7C9A61u), opts, filter);
    verifyAfter("vectorize");
  }

  // Register pressure must be absolute last — it adds inline asm which
  // would cause shouldSkipFunction (skip_inline_asm) to skip the function
  // if any subsequent pass checked it.
  if (DoRegPressure) {
    ollvm::extendRegisterPressureModule(*M, mixSeed(base_seed, 0xF3B28E4Du), filter);
    verifyAfter("reg-pressure");
  }

  // Final verify (always runs, even without --verify-each).
  if (llvm::verifyModule(*M, &llvm::errs())) {
    llvm::errs() << "ollvm-obf: module verification failed after obfuscation\n";
    return 1;
  }

  // Write output (always bitcode for pipeline use).
  std::error_code EC;
  llvm::ToolOutputFile Out(OutputFilename, EC, llvm::sys::fs::OF_None);
  if (EC) {
    llvm::errs() << "ollvm-obf: error opening output file: " << EC.message() << "\n";
    return 1;
  }

  if (llvm::StringRef(OutputFilename).ends_with(".ll"))
    M->print(Out.os(), nullptr);
  else
    llvm::WriteBitcodeToFile(*M, Out.os());
  Out.keep();
  return 0;
}
