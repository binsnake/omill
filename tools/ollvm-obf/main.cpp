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

#include "Flattening.h"
#include "StringEncryption.h"
#include "Substitution.h"

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

  // Apply passes in order: string encryption first (before CFF moves blocks
  // around), then substitution, then flattening.
  if (DoStringEncrypt) {
    ollvm::encryptStringsModule(*M);
  }

  if (DoSubstitute) {
    ollvm::substituteModule(*M);
  }

  if (DoFlatten) {
    ollvm::flattenModule(*M);
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
