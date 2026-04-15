#include "Options.h"
#include <llvm/Support/CommandLine.h>
#include <string>

using namespace llvm;

cl::opt<std::string> InputFilename(cl::Positional,
                                           cl::desc("<input binary (PE/Mach-O)>"),
                                           cl::Required);

cl::opt<std::string> FuncVA("va",
                                    cl::desc("Function virtual address (hex)"));

cl::opt<bool> RawBinary(
    "raw",
    cl::desc("Treat input as a raw (headerless) code binary"),
    cl::init(false));

cl::opt<uint64_t> BaseAddress(
    "base",
    cl::desc("Base address for raw binary loading (default: 0)"),
    cl::init(0));

cl::opt<std::string> OutputFilename("o", cl::desc("Output .ll file"),
                                            cl::value_desc("filename"),
                                            cl::init("-"));

cl::opt<bool> NoABI("no-abi",
                            cl::desc("Skip ABI recovery"),
                            cl::init(false));

cl::opt<bool> Deobfuscate("deobfuscate",
                                  cl::desc("Enable deobfuscation passes"),
                                  cl::init(false));

cl::opt<bool> Devirtualize(
    "devirtualize",
    cl::desc("Force the library-owned devirtualization orchestrator"),
    cl::init(false));

cl::opt<bool> ResolveTargets(
    "resolve-targets",
    cl::desc("Enable iterative indirect target resolution"),
    cl::init(false));

cl::opt<unsigned> MaxIterations(
    "max-iterations",
    cl::desc("Max iterations for target resolution (default 10)"),
    cl::init(10));

cl::opt<bool> IPCP(
    "ipcp",
    cl::desc("Enable interprocedural constant propagation"),
    cl::init(false));

cl::opt<bool> ResolveExceptions(
    "resolve-exceptions",
    cl::desc("Resolve forced exceptions (ud2/int3) via .pdata SEH handlers"),
    cl::init(false));

cl::opt<bool> BlockLift(
    "block-lift",
    cl::desc("Use blocks-as-functions architecture for iterative discovery"),
    cl::init(false));

cl::opt<bool> DumpIR(
    "dump-ir",
    cl::desc("Dump before/after IR to before.ll, after.ll, after_abi.ll"),
    cl::init(false));

cl::opt<std::string> VMEntry(
    "vm-entry",
    cl::desc("VM entry (vmenter) function VA for VM devirtualization (hex)"));

cl::opt<std::string> VMExit(
    "vm-exit",
    cl::desc("VM exit (vmexit) function VA for VM devirtualization (hex)"));

cl::opt<std::string> VMWrapper(
    "vm-wrapper",
    cl::desc("VM entry wrapper VA (hex).  If omitted, defaults to --va.  "
             "Specify this when --va points to an outer function (e.g. "
             "DriverEntry) that calls the wrapper through a thunk."));

cl::opt<std::string> VMTraceJSON(
    "vm-trace-json",
    cl::desc("Path to an external VMTraceRecord JSON file (e.g. from "
             "eac_vm_tracer.py).  Populates the VMTraceMap analysis from "
             "pre-computed trace data instead of running the built-in emulator."));

cl::opt<std::string> LiftDBIn(
    "lift-db-in",
    cl::desc("Load an existing lift database directory before lifting."));

cl::opt<std::string> LiftDBOut(
    "lift-db-out",
    cl::desc("Write the lift database directory after root discovery."));

cl::opt<bool> LiftDBRebuild(
    "lift-db-rebuild",
    cl::desc("Discard any loaded function state before rebuilding lift-db roots."),
    cl::init(false));

cl::opt<std::string> SolveControlVA(
    "solve-control-va",
    cl::desc("Solve branch/target/state values at the specified lifted control VA (hex)"));

cl::list<std::string> SolveStateFields(
    "solve-state-field",
    cl::desc("Named remill State field to solve before --solve-control-va (repeatable or comma-separated)"),
    cl::CommaSeparated);

cl::opt<bool> OmillTimePasses(
    "omill-time-passes",
    cl::desc("Time each omill pass, printing elapsed time on exit"),
    cl::init(false));

cl::opt<bool> VerifyEach(
    "verify-each",
    cl::desc("Run module verifier after every pass (slow, for debugging)"),
    cl::init(false));

cl::opt<std::string> TraceFunc(
    "trace-func",
    cl::desc("Print block/instruction counts for a named function after each "
             "omill pass (e.g. sub_1800444a0)"));

cl::opt<bool> DumpFuncPhases(
    "dump-func-phases",
    cl::desc("With --trace-func, dump the function's IR to files at each "
             "phase marker and on large instruction drops (>30%)"),
    cl::init(false));

cl::opt<std::string> ScanSection(
    "scan-section",
    cl::desc("Scan a PE section and output function classification as JSON"));

cl::opt<std::string> ScanOutput(
    "scan-output",
    cl::desc("Output file for --scan-section (default: stdout)"),
    cl::init("-"));

cl::opt<bool> ScanAll(
    "scan-all",
    cl::desc("Include all functions in scan output (default: >=64B only)"),
    cl::init(false));

cl::opt<std::string> DeobfTargets(
    "deobf-targets",
    cl::desc("JSON file with function VAs to batch-deobfuscate"));

cl::opt<std::string> DeobfSection(
    "deobf-section",
    cl::desc("Scan section and deobfuscate all qualifying functions"));

cl::opt<bool> AllFunctions(
    "all-functions",
    cl::desc("Batch-lift all discovered functions in executable sections"),
    cl::init(false));

cl::opt<unsigned> MinFuncSize(
    "min-func-size",
    cl::desc("Minimum function size in bytes for scan/deobf (default: 64)"),
    cl::init(64));

cl::opt<std::string> EventJSONL(
    "event-jsonl",
    cl::desc("Emit structured run events as JSONL to file path or '-'"),
    cl::init(""));

cl::opt<std::string> EventDetail(
    "event-detail",
    cl::desc("Event granularity: basic|detailed"),
    cl::init("basic"));

cl::opt<bool> VerboseRemillLogs(
    "verbose-remill-logs",
    cl::desc("Keep verbose Remill/GLOG startup diagnostics enabled"),
    cl::init(false));

cl::opt<bool> GenericStaticDevirtualize(
    "generic-static-devirtualize",
    cl::desc("Enable generic static devirtualization materialization"),
    cl::init(false));

cl::opt<bool> VerifyGenericStaticDevirtualization(
    "verify-generic-static-devirtualization",
    cl::desc("Validate generic static devirtualization rewrites when supported"),
    cl::init(false));

cl::opt<std::string> DumpVirtualModel(
    "dump-virtual-model",
    cl::desc("Dump generic virtual-machine model/materialization diagnostics"),
    cl::init(""));

