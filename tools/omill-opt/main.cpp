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

static cl::opt<bool> TimePasses(
    "time-passes",
    cl::desc("Time each pass, printing elapsed time on exit"),
    cl::init(false));

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

  // Set up pass timing instrumentation.
  PassInstrumentationCallbacks PIC;
  TimePassesHandler TimingHandler(TimePasses);
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

  if (TimePasses)
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
