#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Object/COFF.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/InitLLVM.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/ToolOutputFile.h>
#include <llvm/Support/raw_ostream.h>

#include <remill/Arch/Arch.h>
#include <remill/Arch/Name.h>
#include <remill/BC/IntrinsicTable.h>
#include <remill/BC/TraceLifter.h>
#include <remill/BC/Util.h>
#include <remill/OS/OS.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/CallingConventionAnalysis.h"
#include "omill/Analysis/CallGraphAnalysis.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Omill.h"

#include <deque>
#include <vector>

using namespace llvm;

static cl::opt<std::string> InputFilename(cl::Positional,
                                           cl::desc("<input PE file>"),
                                           cl::Required);

static cl::opt<std::string> FuncVA("va",
                                    cl::desc("Function virtual address (hex)"),
                                    cl::Required);

static cl::opt<std::string> OutputFilename("o", cl::desc("Output .ll file"),
                                            cl::value_desc("filename"),
                                            cl::init("-"));

static cl::opt<bool> NoABI("no-abi",
                            cl::desc("Skip ABI recovery"),
                            cl::init(false));

static cl::opt<bool> Deobfuscate("deobfuscate",
                                  cl::desc("Enable deobfuscation passes"),
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

namespace {

/// In-memory trace manager for remill lifting.
class BufferTraceManager : public remill::TraceManager {
 public:
  void setCode(const uint8_t *data, size_t size, uint64_t base) {
    code_[base] = {data, data + size};
    base_addr_ = base;
  }

  void setBaseAddr(uint64_t addr) { base_addr_ = addr; }
  uint64_t baseAddr() const { return base_addr_; }

  void SetLiftedTraceDefinition(uint64_t addr,
                                llvm::Function *func) override {
    lifted_[addr] = func;
  }

  llvm::Function *GetLiftedTraceDeclaration(uint64_t addr) override {
    auto it = lifted_.find(addr);
    return (it != lifted_.end()) ? it->second : nullptr;
  }

  llvm::Function *GetLiftedTraceDefinition(uint64_t addr) override {
    return GetLiftedTraceDeclaration(addr);
  }

  bool TryReadExecutableByte(uint64_t addr, uint8_t *out) override {
    for (auto &[base, data] : code_) {
      if (addr >= base && addr < base + data.size()) {
        *out = data[addr - base];
        return true;
      }
    }
    return false;
  }

 private:
  std::map<uint64_t, std::vector<uint8_t>> code_;
  std::map<uint64_t, llvm::Function *> lifted_;
  uint64_t base_addr_ = 0;
};

struct PEInfo {
  std::deque<std::vector<uint8_t>> section_storage;
  omill::BinaryMemoryMap memory_map;
  uint64_t text_base = 0;
  uint64_t text_size = 0;
  uint64_t image_base = 0;
};

bool loadPE(StringRef path, PEInfo &out) {
  auto buf_or_err = MemoryBuffer::getFile(path);
  if (!buf_or_err) {
    errs() << "Cannot open " << path << ": "
           << buf_or_err.getError().message() << "\n";
    return false;
  }

  auto obj_or_err = object::COFFObjectFile::create(
      (*buf_or_err)->getMemBufferRef());
  if (!obj_or_err) {
    errs() << "Not a valid COFF/PE: "
           << toString(obj_or_err.takeError()) << "\n";
    return false;
  }
  auto &coff = **obj_or_err;
  out.image_base = coff.getImageBase();

  // Parse IAT: map each import's IAT slot VA to its module+function name.
  for (const auto &dir : coff.import_directories()) {
    StringRef dll_name;
    if (dir.getName(dll_name))
      continue;

    // Get IAT RVA from the raw import directory entry.
    const object::coff_import_directory_table_entry *raw_entry = nullptr;
    if (dir.getImportTableEntry(raw_entry) || !raw_entry)
      continue;
    uint32_t iat_rva = raw_entry->ImportAddressTableRVA;

    unsigned idx = 0;
    for (auto sym : dir.imported_symbols()) {
      StringRef sym_name;
      if (!sym.getSymbolName(sym_name)) {
        uint64_t iat_va = out.image_base + iat_rva + idx * 8;
        out.memory_map.addImport(iat_va, dll_name.str(), sym_name.str());
      }
      ++idx;
    }
  }

  for (const auto &sec : coff.sections()) {
    auto name_or_err = sec.getName();
    if (!name_or_err) { consumeError(name_or_err.takeError()); continue; }
    StringRef name = *name_or_err;

    auto contents_or_err = sec.getContents();
    if (!contents_or_err) { consumeError(contents_or_err.takeError()); continue; }
    StringRef contents = *contents_or_err;

    uint64_t va = sec.getAddress();
    out.section_storage.emplace_back(
        reinterpret_cast<const uint8_t *>(contents.data()),
        reinterpret_cast<const uint8_t *>(contents.data()) + contents.size());
    auto &stored = out.section_storage.back();
    out.memory_map.addRegion(va, stored.data(), stored.size());

    if (name == ".text") {
      out.text_base = va;
      out.text_size = stored.size();
    }
  }
  return true;
}

}  // namespace

int main(int argc, char **argv) {
  InitLLVM X(argc, argv);
  cl::ParseCommandLineOptions(argc, argv,
      "omill-lift: Lift a function from a PE binary and optimize\n");

  // Parse VA
  uint64_t func_va = 0;
  if (StringRef(FuncVA).starts_with("0x") ||
      StringRef(FuncVA).starts_with("0X")) {
    StringRef(FuncVA).drop_front(2).getAsInteger(16, func_va);
  } else {
    StringRef(FuncVA).getAsInteger(16, func_va);
  }
  if (func_va == 0) {
    errs() << "Invalid VA: " << FuncVA << "\n";
    return 1;
  }
  errs() << "Lifting function at VA 0x" << Twine::utohexstr(func_va) << "\n";

  // Load PE
  PEInfo pe;
  if (!loadPE(InputFilename, pe)) return 1;
  errs() << "Loaded PE: image_base=0x" << Twine::utohexstr(pe.image_base)
         << " .text=0x" << Twine::utohexstr(pe.text_base)
         << " (" << pe.text_size << " bytes)\n";

  // Set up remill
  LLVMContext ctx;
  auto arch = remill::Arch::Get(ctx, remill::kOSWindows, remill::kArchAMD64_AVX);
  if (!arch) {
    errs() << "Failed to create AMD64 arch\n";
    return 1;
  }

  auto module = remill::LoadArchSemantics(arch.get());
  if (!module) {
    errs() << "Failed to load arch semantics\n";
    return 1;
  }

  // Read .text section
  std::vector<uint8_t> text_copy(pe.text_size);
  if (!pe.memory_map.read(pe.text_base, text_copy.data(),
                           static_cast<unsigned>(pe.text_size))) {
    errs() << "Failed to read .text section\n";
    return 1;
  }

  BufferTraceManager manager;
  manager.setCode(text_copy.data(), text_copy.size(), pe.text_base);
  manager.setBaseAddr(func_va);

  // Lift
  remill::TraceLifter lifter(arch.get(), manager);
  if (!lifter.Lift(func_va)) {
    errs() << "TraceLifter::Lift() failed\n";
    return 1;
  }
  errs() << "Lifting complete\n";

  // Dump before IR
  {
    std::error_code ec;
    raw_fd_ostream os("before.ll", ec, sys::fs::OF_Text);
    if (!ec) {
      module->print(os, nullptr);
      errs() << "Wrote before.ll\n";
    }
  }

  // Set up pass infrastructure
  PassBuilder PB;
  LoopAnalysisManager LAM;
  FunctionAnalysisManager FAM;
  CGSCCAnalysisManager CGAM;
  ModuleAnalysisManager MAM;

  // Register BinaryMemoryAnalysis with our PE memory map.
  MAM.registerPass([&] {
    return omill::BinaryMemoryAnalysis(pe.memory_map);
  });

  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

  omill::registerAnalyses(FAM);
  omill::registerModuleAnalyses(MAM);

  // Run the main pipeline (without ABI first)
  omill::PipelineOptions opts;
  opts.recover_abi = false;
  opts.deobfuscate = Deobfuscate;
  opts.resolve_indirect_targets = ResolveTargets;
  opts.max_resolution_iterations = MaxIterations;
  opts.refine_signatures = RefineSignatures;
  opts.interprocedural_const_prop = IPCP;
  {
    ModulePassManager MPM;
    omill::buildPipeline(MPM, opts);
    MPM.run(*module, MAM);
  }
  errs() << "Main pipeline complete\n";

  // Dump after IR
  {
    std::error_code ec;
    raw_fd_ostream os("after.ll", ec, sys::fs::OF_Text);
    if (!ec) {
      module->print(os, nullptr);
      errs() << "Wrote after.ll\n";
    }
  }

  // ABI recovery
  if (!NoABI) {
    ModulePassManager MPM;
    omill::buildABIRecoveryPipeline(MPM);
    MPM.run(*module, MAM);
    errs() << "ABI recovery complete\n";
  }

  // Verify
  if (verifyModule(*module, &errs())) {
    errs() << "WARNING: module verification failed\n";
  }

  // Write final output
  std::error_code EC;
  ToolOutputFile Out(OutputFilename, EC, sys::fs::OF_Text);
  if (EC) {
    errs() << "Error opening output: " << EC.message() << "\n";
    return 1;
  }
  module->print(Out.os(), nullptr);
  Out.keep();

  // Also write after_abi.ll
  {
    std::error_code ec;
    raw_fd_ostream os("after_abi.ll", ec, sys::fs::OF_Text);
    if (!ec) {
      module->print(os, nullptr);
      errs() << "Wrote after_abi.ll\n";
    }
  }

  errs() << "Done.\n";
  return 0;
}
