#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/PassTimingInfo.h>
#include <llvm/IR/Verifier.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Passes/StandardInstrumentations.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/InitLLVM.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/ToolOutputFile.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Bitcode/BitcodeWriter.h>

#include "omill/Omill.h"
#include "omill/Support/MemoryLimit.h"
#include "omill/Analysis/CallingConventionAnalysis.h"
#include "omill/Passes/LowerRemillIntrinsics.h"
#include "omill/Passes/PassRegistry.h"

using namespace llvm;

static cl::opt<std::string> InputFilename(cl::Positional,
                                           cl::desc("<input .ll/.bc file>"),
                                           cl::Required);

static cl::opt<std::string> OutputFilename("o", cl::desc("Output filename"),
                                            cl::value_desc("filename"),
                                            cl::init("-"));

static cl::opt<bool> OutputBitcode("emit-bc",
                                    cl::desc("Emit bitcode instead of IR"),
                                    cl::init(false));

static cl::opt<bool> NoLowerIntrinsics(
    "no-lower-intrinsics",
    cl::desc("Skip intrinsic lowering (Stage 2)"),
    cl::init(false));

static cl::opt<bool> NoOptimizeState(
    "no-optimize-state",
    cl::desc("Skip state optimization (Stage 3)"),
    cl::init(false));

static cl::opt<bool> NoLowerControlFlow(
    "no-lower-control-flow",
    cl::desc("Skip control flow recovery (Stage 4)"),
    cl::init(false));

static cl::opt<bool> NoCleanup(
    "no-cleanup",
    cl::desc("Skip standard LLVM cleanup passes between stages"),
    cl::init(false));

static cl::opt<bool> VerifyOutput(
    "verify",
    cl::desc("Verify module after optimization"),
    cl::init(true));

// Individual pass options for fine-grained control
static cl::opt<bool> OnlyLowerFlags(
    "lower-flags",
    cl::desc("Only run LowerFlagIntrinsics pass"),
    cl::init(false));

static cl::opt<bool> OnlyLowerMemory(
    "lower-memory",
    cl::desc("Only run LowerMemoryIntrinsics pass"),
    cl::init(false));

static cl::opt<bool> OnlyRemoveBarriers(
    "remove-barriers",
    cl::desc("Only run RemoveBarriers pass"),
    cl::init(false));

static cl::opt<bool> Deobfuscate(
    "deobfuscate",
    cl::desc("Enable deobfuscation passes"),
    cl::init(false));

static cl::opt<bool> RecoverABI(
    "recover-abi",
    cl::desc("Enable ABI recovery passes"),
    cl::init(false));

static cl::opt<bool> OnlyRecoverABI(
    "only-recover-abi",
    cl::desc("Run ONLY ABI recovery (skip phases 0-3)"),
    cl::init(false));

static cl::opt<bool> ResolveTargets(
    "resolve-targets",
    cl::desc("Enable iterative indirect target resolution"),
    cl::init(false));

static cl::opt<unsigned> MaxIterations(
    "max-iterations",
    cl::desc("Max iterations for target resolution (default 10)"),
    cl::init(10));

static cl::opt<bool> RefineSignatures(
    "refine-signatures",
    cl::desc("Refine function signatures after ABI recovery"),
    cl::init(false));

static cl::opt<bool> IPCP(
    "ipcp",
    cl::desc("Enable interprocedural constant propagation"),
    cl::init(false));

static cl::opt<bool> GenericStaticDevirtualize(
    "generic-static-devirtualize",
    cl::desc("Enable generic static devirtualization passes"),
    cl::init(false));

static cl::opt<bool> VerifyGenericStaticDevirtualization(
    "verify-generic-static-devirtualization",
    cl::desc("Validate generic static devirtualization rewrites"),
    cl::init(false));

static cl::opt<bool> BlockLift(
    "block-lift",
    cl::desc("Use block-lifting pipeline mode"),
    cl::init(false));

static cl::opt<bool> NoABIMode(
    "no-abi-mode",
    cl::desc("Run the pipeline in no-ABI mode"),
    cl::init(false));

static cl::opt<bool> PreserveLiftedSemantics(
    "preserve-lifted-semantics",
    cl::desc("Keep lifted semantic support alive across the pipeline"),
    cl::init(false));

static cl::opt<std::string> DumpVirtualModel(
    "dump-virtual-model",
    cl::desc("Dump generic virtual-machine model/materialization diagnostics"),
    cl::init(""));

static cl::opt<bool> OmillTimePasses(
    "omill-time-passes",
    cl::desc("Time each pass, printing elapsed time on exit"),
    cl::init(false));

static void setEnvValue(const char *name, const std::string &value) {
  if (value.empty())
    return;
#if defined(_WIN32)
  _putenv_s(name, value.c_str());
#else
  setenv(name, value.c_str(), 1);
#endif
}

int main(int argc, char **argv) {
  omill::setProcessMemoryLimit(32ULL * 1024 * 1024 * 1024);  // 32 GB
  InitLLVM X(argc, argv);
  cl::ParseCommandLineOptions(argc, argv, "omill optimizer\n");

  LLVMContext Context;
  SMDiagnostic Err;

  auto M = parseIRFile(InputFilename, Err, Context);
  if (!M) {
    Err.print(argv[0], errs());
    return 1;
  }

  // Build the pipeline based on options.
  omill::PipelineOptions opts;
  if (OnlyRecoverABI) {
    // Skip all phases except ABI recovery.
    opts.lower_intrinsics = false;
    opts.optimize_state = false;
    opts.lower_control_flow = false;
    opts.run_cleanup_passes = false;
    opts.deobfuscate = false;
    opts.recover_abi = true;
    opts.resolve_indirect_targets = false;
    opts.refine_signatures = RefineSignatures;
    opts.interprocedural_const_prop = false;
  } else {
    opts.lower_intrinsics = !NoLowerIntrinsics;
    opts.optimize_state = !NoOptimizeState;
    opts.lower_control_flow = !NoLowerControlFlow;
    opts.run_cleanup_passes = !NoCleanup;
    opts.deobfuscate = Deobfuscate;
    opts.recover_abi = RecoverABI;
    opts.resolve_indirect_targets = ResolveTargets;
    opts.max_resolution_iterations = MaxIterations;
    opts.refine_signatures = RefineSignatures;
    opts.interprocedural_const_prop = IPCP;
  }

  opts.generic_static_devirtualize = GenericStaticDevirtualize;
  opts.verify_generic_static_devirtualization =
      VerifyGenericStaticDevirtualization;
  opts.use_block_lifting = BlockLift;
  opts.no_abi_mode = NoABIMode;
  opts.preserve_lifted_semantics = PreserveLiftedSemantics;

  setEnvValue("OMILL_DUMP_VIRTUAL_MODEL", DumpVirtualModel);

  // When running --recover-abi on a checkpoint file, scope phases 0-3
  // to only process functions that still have the remill signature
  // (ptr, i64, ptr) -> ptr.  Already-processed functions crash if
  // re-run through the lowering passes.
  if (RecoverABI && !OnlyRecoverABI) {
    opts.scope_predicate = [](Function &F) -> bool {
      if (F.isDeclaration()) return false;
      auto *FT = F.getFunctionType();
      if (FT->getNumParams() != 3) return false;
      if (!FT->getReturnType()->isPointerTy()) return false;
      if (!FT->getParamType(0)->isPointerTy()) return false;
      if (!FT->getParamType(1)->isIntegerTy(64)) return false;
      if (!FT->getParamType(2)->isPointerTy()) return false;
      return true;
    };
  }

  // Set up pass timing instrumentation.
  PassInstrumentationCallbacks PIC;
  StandardInstrumentations SI(Context, /*DebugLogging=*/false);
  SI.registerCallbacks(PIC);
  TimePassesHandler TimingHandler(OmillTimePasses);
  TimingHandler.registerCallbacks(PIC);

  // Set up pass infrastructure
  PassBuilder PB(nullptr, PipelineTuningOptions(), std::nullopt, &PIC);

  LoopAnalysisManager LAM;
  FunctionAnalysisManager FAM;
  CGSCCAnalysisManager CGAM;
  ModuleAnalysisManager MAM;

  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

  // Register omill-specific analyses
  omill::registerAnalyses(FAM);
  omill::registerModuleAnalyses(MAM);

  ModulePassManager MPM;

  // Check if user requested a single pass
  bool single_pass =
      OnlyLowerFlags || OnlyLowerMemory || OnlyRemoveBarriers;

  if (single_pass) {
    FunctionPassManager FPM;
    if (OnlyLowerFlags) {
      FPM.addPass(omill::LowerRemillIntrinsicsPass(omill::LowerCategories::Flags));
    }
    if (OnlyRemoveBarriers) {
      FPM.addPass(omill::LowerRemillIntrinsicsPass(omill::LowerCategories::Barriers));
    }
    if (OnlyLowerMemory) {
      FPM.addPass(omill::LowerRemillIntrinsicsPass(omill::LowerCategories::Memory));
    }
    MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
  } else {
    omill::buildPipeline(MPM, opts);
  }

  // Run the pipeline
  MPM.run(*M, MAM);

  if (OmillTimePasses)
    TimingHandler.print();

  // Verify
  if (VerifyOutput) {
    if (verifyModule(*M, &errs())) {
      errs() << "omill-opt: module verification failed after optimization\n";
      return 1;
    }
  }

  // Write output
  std::error_code EC;
  ToolOutputFile Out(OutputFilename, EC, sys::fs::OF_None);
  if (EC) {
    errs() << "omill-opt: error opening output file: " << EC.message() << "\n";
    return 1;
  }

  if (OutputBitcode) {
    WriteBitcodeToFile(*M, Out.os());
  } else {
    M->print(Out.os(), nullptr);
  }

  Out.keep();
  return 0;
}
