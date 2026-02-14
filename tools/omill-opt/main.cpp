#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/InitLLVM.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/ToolOutputFile.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Bitcode/BitcodeWriter.h>

#include "omill/Omill.h"
#include "omill/Passes/LowerFlagIntrinsics.h"
#include "omill/Passes/LowerMemoryIntrinsics.h"
#include "omill/Passes/PassRegistry.h"
#include "omill/Passes/RemoveBarriers.h"

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

int main(int argc, char **argv) {
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

  // Set up pass infrastructure
  PassBuilder PB;

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

  ModulePassManager MPM;

  // Check if user requested a single pass
  bool single_pass =
      OnlyLowerFlags || OnlyLowerMemory || OnlyRemoveBarriers;

  if (single_pass) {
    FunctionPassManager FPM;
    if (OnlyLowerFlags) {
      FPM.addPass(omill::LowerFlagIntrinsicsPass());
    }
    if (OnlyRemoveBarriers) {
      FPM.addPass(omill::RemoveBarriersPass());
    }
    if (OnlyLowerMemory) {
      FPM.addPass(omill::LowerMemoryIntrinsicsPass());
    }
    MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));
  } else {
    omill::buildPipeline(MPM, opts);
  }

  // Run the pipeline
  MPM.run(*M, MAM);

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
