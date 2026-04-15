#pragma once
#include <llvm/Support/CommandLine.h>
#include <cstdint>
#include <string>

// External declarations for all omill-lift command-line options.
// Defined in Options.cpp.

extern llvm::cl::opt<std::string> InputFilename;
extern llvm::cl::opt<std::string> FuncVA;
extern llvm::cl::opt<bool> RawBinary;
extern llvm::cl::opt<uint64_t> BaseAddress;
extern llvm::cl::opt<std::string> OutputFilename;
extern llvm::cl::opt<bool> NoABI;
extern llvm::cl::opt<bool> Deobfuscate;
extern llvm::cl::opt<bool> Devirtualize;
extern llvm::cl::opt<bool> ResolveTargets;
extern llvm::cl::opt<unsigned> MaxIterations;
extern llvm::cl::opt<bool> IPCP;
extern llvm::cl::opt<bool> ResolveExceptions;
extern llvm::cl::opt<bool> BlockLift;
extern llvm::cl::opt<bool> DumpIR;
extern llvm::cl::opt<std::string> VMEntry;
extern llvm::cl::opt<std::string> VMExit;
extern llvm::cl::opt<std::string> VMWrapper;
extern llvm::cl::opt<std::string> VMTraceJSON;
extern llvm::cl::opt<std::string> LiftDBIn;
extern llvm::cl::opt<std::string> LiftDBOut;
extern llvm::cl::opt<bool> LiftDBRebuild;
extern llvm::cl::opt<std::string> SolveControlVA;
extern llvm::cl::list<std::string> SolveStateFields;
extern llvm::cl::opt<bool> OmillTimePasses;
extern llvm::cl::opt<bool> VerifyEach;
extern llvm::cl::opt<std::string> TraceFunc;
extern llvm::cl::opt<bool> DumpFuncPhases;
extern llvm::cl::opt<std::string> ScanSection;
extern llvm::cl::opt<std::string> ScanOutput;
extern llvm::cl::opt<bool> ScanAll;
extern llvm::cl::opt<std::string> DeobfTargets;
extern llvm::cl::opt<std::string> DeobfSection;
extern llvm::cl::opt<bool> AllFunctions;
extern llvm::cl::opt<unsigned> MinFuncSize;
extern llvm::cl::opt<std::string> EventJSONL;
extern llvm::cl::opt<std::string> EventDetail;
extern llvm::cl::opt<bool> VerboseRemillLogs;
extern llvm::cl::opt<bool> GenericStaticDevirtualize;
extern llvm::cl::opt<bool> VerifyGenericStaticDevirtualization;
extern llvm::cl::opt<std::string> DumpVirtualModel;
