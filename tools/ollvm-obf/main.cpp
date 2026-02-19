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

#include "ConstantUnfolding.h"
#include "Flattening.h"
#include "StringEncryption.h"
#include "Substitution.h"
#include "Vectorize.h"

using namespace llvm;

static cl::opt<std::string> InputFilename(cl::Positional,
                                           cl::desc("<input .ll/.bc file>"),
                                           cl::Required);

static cl::opt<std::string> OutputFilename("o", cl::desc("Output filename"),
                                            cl::value_desc("filename"),
                                            cl::init("-"));

static cl::opt<bool> DoFlatten("flatten",
                                cl::desc("Apply control flow flattening"),
                                cl::init(false));

static cl::opt<bool> DoSubstitute("substitute",
                                   cl::desc("Apply MBA instruction substitution"),
                                   cl::init(false));

static cl::opt<bool> DoStringEncrypt("string-encrypt",
                                      cl::desc("Apply XOR-based string encryption"),
                                      cl::init(false));

static cl::opt<bool> DoConstUnfold("const-unfold",
                                    cl::desc("Replace constants with equivalent expressions"),
                                    cl::init(false));

static cl::opt<bool> DoVectorize("vectorize",
                                  cl::desc("Replace i32 scalar ops with SSE vector ops"),
                                  cl::init(false));

static cl::opt<bool> DoVectorizeData(
    "vectorize-data",
    cl::desc("Enable vectorized i32 stack data mutation (lane-0 load/store)"),
    cl::init(true));

static cl::opt<bool> DoVectorizeBitwise(
    "vectorize-bitwise",
    cl::desc("Lower vectorized add/sub through bitwise ops (xor/and/shl)"),
    cl::init(false));

static cl::opt<unsigned> VectorizePercent(
    "vectorize-percent",
    cl::desc("Percent of eligible i32 scalar ops to vectorize (0-100)"),
    cl::init(40));

static cl::opt<unsigned> ObfSeed(
    "seed",
    cl::desc("Base RNG seed for deterministic obfuscation"),
    cl::init(0xB16B00B5u));

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
  InitLLVM X(argc, argv);
  cl::ParseCommandLineOptions(argc, argv, "OLLVM-style obfuscation tool\n");

  LLVMContext Context;
  SMDiagnostic Err;

  auto M = parseIRFile(InputFilename, Err, Context);
  if (!M) {
    Err.print(argv[0], errs());
    return 1;
  }

  const uint32_t base_seed = static_cast<uint32_t>(ObfSeed);

  // Apply passes in a fixed order for determinism and compatibility.
  // Scalar->vector mutation must stay last so prior obfuscations (CFF/MBA/etc.)
  // can reshape scalar IR first.
  if (DoStringEncrypt) {
    ollvm::encryptStringsModule(*M, mixSeed(base_seed, 0x11A48D53u));
  }

  if (DoSubstitute) {
    ollvm::substituteModule(*M, mixSeed(base_seed, 0x5B2E6D4Fu));
  }

  if (DoFlatten) {
    ollvm::flattenModule(*M, mixSeed(base_seed, 0xA1F3707Bu));
  }

  if (DoConstUnfold) {
    ollvm::unfoldConstantsModule(*M, mixSeed(base_seed, 0xC93A1E27u));
  }

  // Must run last.
  if (DoVectorize) {
    ollvm::VectorizeOptions opts;
    opts.vectorize_data = DoVectorizeData;
    opts.vectorize_bitwise = DoVectorizeBitwise;
    opts.transform_percent = VectorizePercent;
    ollvm::vectorizeModule(*M, mixSeed(base_seed, 0x3D7C9A61u), opts);
  }

  // Verify.
  if (verifyModule(*M, &errs())) {
    errs() << "ollvm-obf: module verification failed after obfuscation\n";
    return 1;
  }

  // Write output (always bitcode for pipeline use).
  std::error_code EC;
  ToolOutputFile Out(OutputFilename, EC, sys::fs::OF_None);
  if (EC) {
    errs() << "ollvm-obf: error opening output file: " << EC.message() << "\n";
    return 1;
  }

  WriteBitcodeToFile(*M, Out.os());
  Out.keep();
  return 0;
}
