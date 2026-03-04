#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/PassTimingInfo.h>
#include <llvm/IR/Verifier.h>
#include <llvm/BinaryFormat/COFF.h>
#include <llvm/Linker/Linker.h>
#include <llvm/Object/COFF.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Passes/StandardInstrumentations.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/InitLLVM.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/ToolOutputFile.h>
#include <llvm/Support/JSON.h>
#include <llvm/Support/raw_ostream.h>

#include <remill/Arch/Arch.h>
#include <remill/Arch/Instruction.h>
#include <remill/Arch/Name.h>
#include <remill/BC/IntrinsicTable.h>
#include "omill/BC/TraceLifter.h"
#include "omill/BC/BlockLifter.h"
#include "omill/BC/BlockLifterAnalysis.h"
#include "omill/BC/TraceLiftAnalysis.h"
#include <remill/BC/Util.h>
#include <remill/OS/OS.h>

#include <llvm/Support/Win64EH.h>

#include "omill/Support/MemoryLimit.h"
#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/CallingConventionAnalysis.h"
#include "omill/Analysis/CallGraphAnalysis.h"
#include "omill/Analysis/ExceptionInfo.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Analysis/VMHandlerGraph.h"
#include "omill/Omill.h"

#include <algorithm>
#include <deque>
#include <memory>
#include <vector>

using namespace llvm;

/// Repair malformed PHI nodes in a module so it can be written as valid LL.
/// Handles two cases:
/// 1. Incoming values from blocks that are not predecessors (stale entries).
/// 2. Missing duplicate entries for multi-edge predecessors (e.g. switch
///    with two cases branching to the same block needs two PHI entries).
static void repairMalformedPHIs(Module &M) {
  for (auto &F : M) {
    if (F.isDeclaration()) continue;
    for (auto &BB : F) {
      // Count how many edges each predecessor has to this block.
      DenseMap<BasicBlock *, unsigned> pred_edge_count;
      for (auto *P : predecessors(&BB))
        ++pred_edge_count[P];

      for (auto &I : make_early_inc_range(BB)) {
        auto *phi = dyn_cast<PHINode>(&I);
        if (!phi) break;

        // Remove entries from non-predecessors.
        for (unsigned i = phi->getNumIncomingValues(); i-- > 0;) {
          if (!pred_edge_count.count(phi->getIncomingBlock(i))) {
            phi->removeIncomingValue(i, /*DeletePHIIfEmpty=*/false);
          }
        }

        // Count current entries per predecessor.
        DenseMap<BasicBlock *, unsigned> phi_count;
        for (unsigned i = 0; i < phi->getNumIncomingValues(); ++i)
          ++phi_count[phi->getIncomingBlock(i)];

        // Add missing duplicate entries for multi-edge predecessors.
        for (auto &[pred, needed] : pred_edge_count) {
          unsigned have = phi_count.lookup(pred);
          if (have == 0) continue;  // No entry at all — can't invent a value.
          for (unsigned j = have; j < needed; ++j) {
            // Find the existing value for this predecessor.
            Value *val = phi->getIncomingValueForBlock(pred);
            phi->addIncoming(val, pred);
          }
        }

        if (phi->getNumIncomingValues() == 0) {
          phi->replaceAllUsesWith(PoisonValue::get(phi->getType()));
          phi->eraseFromParent();
        }
      }
    }
  }
}

static cl::opt<std::string> InputFilename(cl::Positional,
                                           cl::desc("<input PE file>"),
                                           cl::Required);

static cl::opt<std::string> FuncVA("va",
                                    cl::desc("Function virtual address (hex)"));

static cl::opt<bool> RawBinary(
    "raw",
    cl::desc("Treat input as a raw (headerless) code binary"),
    cl::init(false));

static cl::opt<uint64_t> BaseAddress(
    "base",
    cl::desc("Base address for raw binary loading (default: 0)"),
    cl::init(0));

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

static cl::opt<bool> ResolveExceptions(
    "resolve-exceptions",
    cl::desc("Resolve forced exceptions (ud2/int3) via .pdata SEH handlers"),
    cl::init(false));

static cl::opt<bool> BlockLift(
    "block-lift",
    cl::desc("Use blocks-as-functions architecture for iterative discovery"),
    cl::init(false));

static cl::opt<bool> DumpIR(
    "dump-ir",
    cl::desc("Dump before/after IR to before.ll, after.ll, after_abi.ll"),
    cl::init(false));

static cl::opt<std::string> VMEntry(
    "vm-entry",
    cl::desc("VM entry (vmenter) function VA for VM devirtualization (hex)"));

static cl::opt<std::string> VMExit(
    "vm-exit",
    cl::desc("VM exit (vmexit) function VA for VM devirtualization (hex)"));

static cl::opt<bool> OmillTimePasses(
    "omill-time-passes",
    cl::desc("Time each omill pass, printing elapsed time on exit"),
    cl::init(false));

static cl::opt<bool> VerifyEach(
    "verify-each",
    cl::desc("Run module verifier after every pass (slow, for debugging)"),
    cl::init(false));

static cl::opt<std::string> TraceFunc(
    "trace-func",
    cl::desc("Print block/instruction counts for a named function after each "
             "omill pass (e.g. sub_1800444a0)"));

static cl::opt<bool> DumpFuncPhases(
    "dump-func-phases",
    cl::desc("With --trace-func, dump the function's IR to files at each "
             "phase marker and on large instruction drops (>30%)"),
    cl::init(false));

static cl::opt<std::string> ScanSection(
    "scan-section",
    cl::desc("Scan a PE section and output function classification as JSON"));

static cl::opt<std::string> ScanOutput(
    "scan-output",
    cl::desc("Output file for --scan-section (default: stdout)"),
    cl::init("-"));

static cl::opt<bool> ScanAll(
    "scan-all",
    cl::desc("Include all functions in scan output (default: >=64B only)"),
    cl::init(false));

static cl::opt<std::string> DeobfTargets(
    "deobf-targets",
    cl::desc("JSON file with function VAs to batch-deobfuscate"));

static cl::opt<std::string> DeobfSection(
    "deobf-section",
    cl::desc("Scan section and deobfuscate all qualifying functions"));

static cl::opt<unsigned> MinFuncSize(
    "min-func-size",
    cl::desc("Minimum function size in bytes for scan/deobf (default: 64)"),
    cl::init(64));

namespace {

/// In-memory trace manager for remill lifting.
class BufferTraceManager : public omill::TraceManager {
 public:
  void setCode(const uint8_t *data, size_t size, uint64_t base) {
    code_[base] = {data, data + size};
    base_addr_ = base;
  }

  void setBaseAddr(uint64_t addr) { base_addr_ = addr; }
  uint64_t baseAddr() const { return base_addr_; }

  /// Must be called after the module and arch are created so that
  /// shallow-lift mode can create proper function declarations.
  void setModuleAndArch(llvm::Module *m, const remill::Arch *a) {
    module_ = m;
    arch_ = a;
  }

  void SetLiftedTraceDefinition(uint64_t addr,
                                llvm::Function *func) override {
    lifted_[addr] = func;
    ++lift_count_;
  }

  llvm::Function *GetLiftedTraceDeclaration(uint64_t addr) override {
    auto it = lifted_.find(addr);
    return (it != lifted_.end()) ? it->second : nullptr;
  }

  llvm::Function *GetLiftedTraceDefinition(uint64_t addr) override {
    // In shallow mode, report all addresses outside the root set as
    // "already lifted" to prevent recursive lifting of the entire
    // call graph.  This is used for late target discovery where we
    // only need the target function, not its callees.
    if (max_lift_count_ > 0 && lift_count_ >= max_lift_count_) {
      auto it = lifted_.find(addr);
      if (it != lifted_.end())
        return it->second;
      // Create a real declaration so the TraceLifter can safely
      // dereference the returned pointer (it checks getParent()).
      auto *decl = arch_->DeclareLiftedFunction(TraceName(addr), module_);
      lifted_[addr] = decl;
      return decl;
    }
    return GetLiftedTraceDeclaration(addr);
  }

  /// Set maximum number of traces to lift per Lift() call.  0 = unlimited.
  void setMaxLiftCount(unsigned n) { max_lift_count_ = n; }
  void resetLiftCount() { lift_count_ = 0; }

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
  unsigned max_lift_count_ = 0;
  unsigned lift_count_ = 0;
  llvm::Module *module_ = nullptr;
  const remill::Arch *arch_ = nullptr;
};

/// In-memory block manager for block-lifting mode.
class BufferBlockManager : public omill::BlockManager {
 public:
  void setCode(const uint8_t *data, size_t size, uint64_t base) {
    code_[base] = {data, data + size};
  }

  void SetLiftedBlockDefinition(uint64_t addr,
                                 llvm::Function *fn) override {
    blocks_[addr] = fn;
  }

  llvm::Function *GetLiftedBlockDeclaration(uint64_t addr) override {
    auto it = blocks_.find(addr);
    return (it != blocks_.end()) ? it->second : nullptr;
  }

  llvm::Function *GetLiftedBlockDefinition(uint64_t addr) override {
    return GetLiftedBlockDeclaration(addr);
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
  std::map<uint64_t, llvm::Function *> blocks_;
};

struct SectionInfo {
  uint64_t va;
  size_t size;
  size_t storage_index;  // index into section_storage
};

struct PEInfo {
  std::deque<std::vector<uint8_t>> section_storage;
  omill::BinaryMemoryMap memory_map;
  omill::ExceptionInfo exception_info;
  std::vector<SectionInfo> code_sections;
  std::deque<std::vector<uint8_t>> synthetic_dc_storage;
  uint64_t image_base = 0;
};

/// Parse .pdata (exception table) from a PE binary.
/// Populates exception_info with RUNTIME_FUNCTION entries that have
/// language-specific exception handlers.
void parsePData(const object::COFFObjectFile &coff, uint64_t image_base,
                omill::ExceptionInfo &exception_info) {
  const object::data_directory *dd = coff.getDataDirectory(COFF::EXCEPTION_TABLE);
  if (!dd || dd->RelativeVirtualAddress == 0 || dd->Size == 0)
    return;

  uintptr_t table_ptr = 0;
  if (auto err = coff.getRvaPtr(dd->RelativeVirtualAddress, table_ptr)) {
    consumeError(std::move(err));
    return;
  }

  unsigned num_entries = dd->Size / sizeof(Win64EH::RuntimeFunction);
  auto *entries = reinterpret_cast<const Win64EH::RuntimeFunction *>(table_ptr);

  for (unsigned i = 0; i < num_entries; ++i) {
    uint32_t begin_rva = entries[i].StartAddress;
    uint32_t end_rva = entries[i].EndAddress;
    uint32_t unwind_rva = entries[i].UnwindInfoOffset;

    if (begin_rva == 0 && end_rva == 0)
      continue;

    // Follow unwind info chain to find the exception handler.
    uint64_t handler_va = 0;
    uint64_t handler_data_va = 0;
    uint32_t current_unwind_rva = unwind_rva;

    for (unsigned depth = 0; depth < 16; ++depth) {
      uintptr_t unwind_ptr = 0;
      if (auto err = coff.getRvaPtr(current_unwind_rva, unwind_ptr)) {
        consumeError(std::move(err));
        break;
      }

      auto *uwi =
          reinterpret_cast<const Win64EH::UnwindInfo *>(unwind_ptr);
      uint8_t flags = uwi->getFlags();

      if (flags & Win64EH::UNW_ExceptionHandler) {
        uint32_t handler_rva = uwi->getLanguageSpecificHandlerOffset();
        handler_va = image_base + handler_rva;

        // HandlerData follows the handler RVA in the language-specific data.
        auto *lsd = reinterpret_cast<const support::ulittle32_t *>(
            uwi->getLanguageSpecificData());
        // lsd[0] = handler RVA, lsd[1] = handler data RVA
        uint32_t data_rva = lsd[1];
        if (data_rva != 0)
          handler_data_va = image_base + data_rva;
        break;
      }

      if (flags & Win64EH::UNW_ChainInfo) {
        // Follow chain to next RUNTIME_FUNCTION.
        auto *chained = uwi->getChainedFunctionEntry();
        current_unwind_rva = chained->UnwindInfoOffset;
        continue;
      }

      // No handler, no chain — done.
      break;
    }

    exception_info.addEntry({image_base + begin_rva, image_base + end_rva,
                             handler_va, handler_data_va, 0, 0});
  }
}

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

  // Determine image size from PE optional header.
  uint64_t image_size = 0;
  if (auto *pe32p = coff.getPE32PlusHeader())
    image_size = pe32p->SizeOfImage;
  else if (auto *pe32 = coff.getPE32Header())
    image_size = pe32->SizeOfImage;
  out.memory_map.setImageBase(out.image_base);
  out.memory_map.setImageSize(image_size);

  // Check for suspicious preferred base (anti-analysis defense).
  if (out.memory_map.isSuspiciousImageBase()) {
    errs() << "WARNING: suspicious preferred image base 0x"
           << Twine::utohexstr(out.image_base)
           << " — ASLR will likely produce a non-zero delta.\n"
           << "         Relocated constants in the binary may be unreliable.\n";
  }

  // Parse .reloc (base relocations) for relocation-aware constant folding.
  for (const auto &reloc : coff.base_relocs()) {
    uint8_t type = 0;
    uint32_t rva = 0;
    if (auto err = reloc.getType(type)) {
      consumeError(std::move(err));
      continue;
    }
    if (auto err = reloc.getRVA(rva)) {
      consumeError(std::move(err));
      continue;
    }

    uint8_t reloc_size = 0;
    if (type == COFF::IMAGE_REL_BASED_DIR64)
      reloc_size = 8;
    else if (type == COFF::IMAGE_REL_BASED_HIGHLOW)
      reloc_size = 4;
    else
      continue;  // Skip padding (ABSOLUTE) and exotic types.

    out.memory_map.addRelocation(out.image_base + rva, reloc_size);
  }
  out.memory_map.finalizeRelocations();

  for (const auto &sec : coff.sections()) {
    auto contents_or_err = sec.getContents();
    if (!contents_or_err) { consumeError(contents_or_err.takeError()); continue; }
    StringRef contents = *contents_or_err;

    uint64_t va = sec.getAddress();
    size_t idx = out.section_storage.size();
    out.section_storage.emplace_back(
        reinterpret_cast<const uint8_t *>(contents.data()),
        reinterpret_cast<const uint8_t *>(contents.data()) + contents.size());
    auto &stored = out.section_storage.back();
    out.memory_map.addRegion(va, stored.data(), stored.size());

    // Track all executable sections for the trace manager.
    const auto *coff_sec = coff.getCOFFSection(sec);
    if (coff_sec && (coff_sec->Characteristics &
                     (COFF::IMAGE_SCN_CNT_CODE | COFF::IMAGE_SCN_MEM_EXECUTE))) {
      out.code_sections.push_back({va, stored.size(), idx});
    }
  }

  // Parse .pdata unconditionally (cheap); the flag controls usage.
  parsePData(coff, out.image_base, out.exception_info);
  out.exception_info.setImageBase(out.image_base);

  // Create synthetic DISPATCHER_CONTEXT regions in BinaryMemoryMap.
  // Each exception entry with HandlerData gets a synthetic DC at a unique
  // address so ConstantMemoryFolding can resolve [R9+0x38] → HandlerData.
  out.exception_info.buildSyntheticDCs(out.synthetic_dc_storage, out.memory_map,
                                        out.image_base);

  return true;
}

struct ScanResult {
  uint64_t va;
  uint32_t size;
  SmallVector<StringRef, 2> tags;
};

/// Scan a PE section, classifying each .pdata function by size and jmp density.
std::vector<ScanResult> scanSection(StringRef section_name, const PEInfo &pe) {
  // Find the named section's VA range by re-parsing the COFF headers.
  // loadPE doesn't preserve section names, so we re-open briefly.
  uint64_t sec_va = 0;
  uint64_t sec_size = 0;
  const uint8_t *sec_data = nullptr;
  {
    auto buf_or_err = MemoryBuffer::getFile(InputFilename);
    if (!buf_or_err) return {};
    auto obj_or_err = object::COFFObjectFile::create(
        (*buf_or_err)->getMemBufferRef());
    if (!obj_or_err) { consumeError(obj_or_err.takeError()); return {}; }
    auto &coff = **obj_or_err;
    for (const auto &sec : coff.sections()) {
      Expected<StringRef> name_or = sec.getName();
      if (!name_or) { consumeError(name_or.takeError()); continue; }
      if (*name_or == section_name) {
        sec_va = sec.getAddress();
        sec_size = sec.getSize();
        break;
      }
    }
  }
  if (sec_va == 0) {
    errs() << "Section '" << section_name << "' not found\n";
    return {};
  }

  // Find backing storage for byte-level analysis.
  for (const auto &si : pe.code_sections) {
    if (si.va == sec_va) {
      sec_data = pe.section_storage[si.storage_index].data();
      break;
    }
  }

  uint64_t sec_end = sec_va + sec_size;
  std::vector<ScanResult> results;

  for (const auto &entry : pe.exception_info.entries()) {
    if (entry.begin_va < sec_va || entry.begin_va >= sec_end)
      continue;

    uint32_t func_size = static_cast<uint32_t>(entry.end_va - entry.begin_va);
    ScanResult sr;
    sr.va = entry.begin_va;
    sr.size = func_size;

    // Compute jmp density from raw bytes if we have section data.
    float jmp_density = 0.0f;
    if (sec_data && func_size > 0) {
      uint64_t offset = entry.begin_va - sec_va;
      uint64_t end_offset = std::min(offset + func_size, sec_size);
      unsigned jmp_count = 0;
      for (uint64_t i = offset; i < end_offset; ++i) {
        uint8_t b = sec_data[i];
        if (b == 0xE9 || b == 0xEB)
          ++jmp_count;
      }
      jmp_density = static_cast<float>(jmp_count) / func_size;
    }

    // Classify.
    if (func_size < 64)
      sr.tags.push_back("trivial");
    else if (func_size <= 256)
      sr.tags.push_back("stub");
    else if (func_size > 256 && jmp_density > 0.08f)
      sr.tags.push_back("cff");
    else
      sr.tags.push_back("normal");

    if (func_size > 4096)
      sr.tags.push_back("large");

    results.push_back(std::move(sr));
  }

  return results;
}

/// Write scan results as JSON.
void writeScanJSON(ArrayRef<ScanResult> results, StringRef binary_name,
                   uint64_t image_base, StringRef section_name,
                   raw_ostream &os) {
  json::OStream J(os, /*IndentSize=*/2);
  J.objectBegin();
  J.attributeBegin("binary");
  J.value(binary_name);
  J.attributeEnd();
  J.attributeBegin("image_base");
  J.value(("0x" + Twine::utohexstr(image_base)).str());
  J.attributeEnd();
  J.attributeBegin("section");
  J.value(section_name);
  J.attributeEnd();
  J.attributeBegin("functions");
  J.arrayBegin();
  for (const auto &r : results) {
    J.objectBegin();
    J.attributeBegin("va");
    J.value(("0x" + Twine::utohexstr(r.va)).str());
    J.attributeEnd();
    J.attributeBegin("size");
    J.value(static_cast<int64_t>(r.size));
    J.attributeEnd();
    J.attributeBegin("tags");
    J.arrayBegin();
    for (auto &tag : r.tags)
      J.value(tag);
    J.arrayEnd();
    J.attributeEnd();
    J.objectEnd();
  }
  J.arrayEnd();
  J.attributeEnd();
  J.objectEnd();
  os << "\n";
}

/// Parse a deobf-targets JSON file, returning function VAs.
std::vector<uint64_t> parseDeobfTargets(StringRef path) {
  auto buf = MemoryBuffer::getFile(path);
  if (!buf) {
    errs() << "Cannot open " << path << ": "
           << buf.getError().message() << "\n";
    return {};
  }
  auto parsed = json::parse((*buf)->getBuffer());
  if (!parsed) {
    errs() << "JSON parse error: " << toString(parsed.takeError()) << "\n";
    return {};
  }
  auto *root = parsed->getAsObject();
  if (!root) {
    errs() << "Expected JSON object at root\n";
    return {};
  }
  auto *funcs = root->getArray("functions");
  if (!funcs) {
    errs() << "No 'functions' array in JSON\n";
    return {};
  }
  std::vector<uint64_t> vas;
  for (const auto &item : *funcs) {
    auto *obj = item.getAsObject();
    if (!obj) continue;
    auto va_str = obj->getString("va");
    if (!va_str) continue;
    uint64_t va = 0;
    StringRef sr = *va_str;
    if (sr.starts_with("0x") || sr.starts_with("0X"))
      sr = sr.drop_front(2);
    sr.getAsInteger(16, va);
    if (va != 0)
      vas.push_back(va);
  }
  return vas;
}

}  // namespace

int main(int argc, char **argv) {
  omill::setProcessMemoryLimit(32ULL * 1024 * 1024 * 1024);  // 32 GB
  InitLLVM X(argc, argv);
  cl::ParseCommandLineOptions(argc, argv,
      "omill-lift: Lift a function from a PE binary and optimize\n");

  // Check for batch/scan modes that don't require --va.
  bool batch_mode = (ScanSection.getNumOccurrences() > 0 ||
                     DeobfTargets.getNumOccurrences() > 0 ||
                     DeobfSection.getNumOccurrences() > 0);

  // Parse VA — for raw binaries, default to base address if --va not given.
  uint64_t func_va = 0;
  if (FuncVA.getNumOccurrences() > 0) {
    if (StringRef(FuncVA).starts_with("0x") ||
        StringRef(FuncVA).starts_with("0X")) {
      StringRef(FuncVA).drop_front(2).getAsInteger(16, func_va);
    } else {
      StringRef(FuncVA).getAsInteger(16, func_va);
    }
  } else if (RawBinary) {
    func_va = BaseAddress;
  } else if (!batch_mode) {
    errs() << "--va is required for PE mode\n";
    return 1;
  }
  if (func_va == 0 && !RawBinary && !batch_mode) {
    errs() << "Invalid VA: " << FuncVA << "\n";
    return 1;
  }
  if (func_va != 0)
    errs() << "Lifting function at VA 0x" << Twine::utohexstr(func_va) << "\n";

  // Parse VM entry/exit VAs if provided.
  uint64_t vm_entry_va = 0, vm_exit_va = 0;
  auto parseHexOpt = [](const std::string &s) -> uint64_t {
    uint64_t v = 0;
    StringRef sr(s);
    if (sr.starts_with("0x") || sr.starts_with("0X"))
      sr.drop_front(2).getAsInteger(16, v);
    else
      sr.getAsInteger(16, v);
    return v;
  };
  if (VMEntry.getNumOccurrences() > 0)
    vm_entry_va = parseHexOpt(VMEntry);
  if (VMExit.getNumOccurrences() > 0)
    vm_exit_va = parseHexOpt(VMExit);

  bool vm_mode = (vm_entry_va != 0);
  if (vm_mode) {
    errs() << "VM mode: vmenter=0x" << Twine::utohexstr(vm_entry_va)
           << " vmexit=0x" << Twine::utohexstr(vm_exit_va) << "\n";
  }

  // --- Raw binary mode ---
  PEInfo pe;
  std::vector<uint8_t> raw_code;

  if (RawBinary) {
    auto buf_or_err = MemoryBuffer::getFile(InputFilename);
    if (!buf_or_err) {
      errs() << "Cannot open " << InputFilename << ": "
             << buf_or_err.getError().message() << "\n";
      return 1;
    }
    auto &buf = *buf_or_err;
    raw_code.assign(
        reinterpret_cast<const uint8_t *>(buf->getBufferStart()),
        reinterpret_cast<const uint8_t *>(buf->getBufferEnd()));
    errs() << "Loaded raw binary: " << raw_code.size()
           << " bytes at base 0x" << Twine::utohexstr(BaseAddress) << "\n";
  } else {
    // Load PE
    if (!loadPE(InputFilename, pe)) return 1;
    errs() << "Loaded PE: image_base=0x" << Twine::utohexstr(pe.image_base)
           << " code_sections=" << pe.code_sections.size() << "\n";
    for (const auto &cs : pe.code_sections) {
      errs() << "  code: 0x" << Twine::utohexstr(cs.va)
             << " (" << cs.size << " bytes)\n";
    }
    if (pe.code_sections.empty()) {
      errs() << "No executable sections found in PE\n";
      return 1;
    }

    // --scan-section: classify functions and output JSON, then exit.
    if (ScanSection.getNumOccurrences() > 0) {
      auto results = scanSection(ScanSection, pe);
      // Filter by minimum size unless --scan-all.
      if (!ScanAll) {
        results.erase(
            std::remove_if(results.begin(), results.end(),
                           [](const ScanResult &r) {
                             return r.size < MinFuncSize;
                           }),
            results.end());
      }
      errs() << "Scanned " << results.size() << " functions in '"
             << ScanSection << "'\n";

      if (ScanOutput == "-") {
        writeScanJSON(results, InputFilename, pe.image_base, ScanSection,
                      outs());
      } else {
        std::error_code ec;
        raw_fd_ostream out(ScanOutput, ec, sys::fs::OF_Text);
        if (ec) {
          errs() << "Error opening " << ScanOutput << ": "
                 << ec.message() << "\n";
          return 1;
        }
        writeScanJSON(results, InputFilename, pe.image_base, ScanSection, out);
      }
      return 0;
    }
  }

  // Collect batch VAs from --deobf-targets or --deobf-section.
  std::vector<uint64_t> batch_vas;
  if (DeobfTargets.getNumOccurrences() > 0) {
    batch_vas = parseDeobfTargets(DeobfTargets);
    if (batch_vas.empty()) {
      errs() << "No valid VAs in " << DeobfTargets << "\n";
      return 1;
    }
    errs() << "Batch mode: " << batch_vas.size()
           << " targets from " << DeobfTargets << "\n";
  } else if (DeobfSection.getNumOccurrences() > 0) {
    auto results = scanSection(DeobfSection, pe);
    for (const auto &r : results) {
      if (r.size >= MinFuncSize)
        batch_vas.push_back(r.va);
    }
    if (batch_vas.empty()) {
      errs() << "No functions >= " << MinFuncSize
             << "B in section '" << DeobfSection << "'\n";
      return 1;
    }
    errs() << "Section mode: " << batch_vas.size()
           << " functions from '" << DeobfSection << "' (>= "
           << MinFuncSize << "B)\n";
    // Force deobfuscation on for --deobf-section.
    Deobfuscate = true;
  }

  // Set up remill — use Linux for raw binaries (no PE metadata).
  LLVMContext ctx;
  auto os_name = RawBinary ? remill::kOSLinux : remill::kOSWindows;
  auto arch = remill::Arch::Get(ctx, os_name, remill::kArchAMD64_AVX);
  if (!arch) {
    errs() << "Failed to create AMD64 arch\n";
    return 1;
  }

  auto module = remill::LoadArchSemantics(arch.get());
  if (!module) {
    errs() << "Failed to load arch semantics\n";
    return 1;
  }

  // Load code into the trace manager.
  BufferTraceManager manager;
  manager.setModuleAndArch(module.get(), arch.get());
  if (RawBinary) {
    manager.setCode(raw_code.data(), raw_code.size(), BaseAddress);
  } else {
    for (const auto &cs : pe.code_sections) {
      auto &stored = pe.section_storage[cs.storage_index];
      manager.setCode(stored.data(), stored.size(), cs.va);
    }
  }
  if (func_va != 0)
    manager.setBaseAddr(func_va);
  else if (!batch_vas.empty())
    manager.setBaseAddr(batch_vas.front());

  if (!RawBinary && ResolveExceptions && !pe.exception_info.empty()) {
    errs() << "Parsed .pdata: " << pe.exception_info.getHandlerVAs().size()
           << " unique handler(s)\n";
  }

  // Lift
  omill::TraceLifter lifter(arch.get(), manager);

  if (!batch_vas.empty()) {
    // Batch lifting mode.
    unsigned lifted = 0, failed = 0;
    for (uint64_t va : batch_vas) {
      if (lifter.Lift(va))
        ++lifted;
      else
        ++failed;
    }
    errs() << "Batch lift: " << lifted << " succeeded, "
           << failed << " failed\n";
    if (lifted == 0) {
      errs() << "No functions lifted\n";
      return 1;
    }
  } else {
    // Single-function lifting mode.
    // If available, lift the handler first so Remill reuses a canonical
    // sub_<va> function instead of creating a late duplicate (sub_<va>.1).
    uint64_t auto_handler_va = 0;
    if (!RawBinary && ResolveExceptions) {
      if (auto *entry = pe.exception_info.lookup(func_va)) {
        auto_handler_va = entry->handler_va;
      }
    }
    if (auto_handler_va != 0 && auto_handler_va != func_va) {
      errs() << "Auto-lifting exception handler at 0x"
             << Twine::utohexstr(auto_handler_va) << "\n";
      if (!lifter.Lift(auto_handler_va)) {
        errs() << "WARNING: failed to lift handler at 0x"
               << Twine::utohexstr(auto_handler_va) << "\n";
      }
    }

    if (!lifter.Lift(func_va)) {
      errs() << "TraceLifter::Lift() failed\n";
      return 1;
    }
  }
  errs() << "Lifting complete\n";

  // VM mode: build handler graph and bulk-lift all discovered handlers.
  std::shared_ptr<omill::VMHandlerGraph> vm_graph;
  if (vm_mode && !RawBinary) {
    vm_graph = std::make_shared<omill::VMHandlerGraph>(
        pe.memory_map, pe.image_base, vm_entry_va, vm_exit_va);

    errs() << "VM handler graph: " << vm_graph->handlerEntries().size()
           << " handlers, " << vm_graph->numDispatchSites()
           << " dispatch sites\n";

    // Lift all discovered handler entry VAs.
    unsigned lifted_count = 0;
    unsigned failed_count = 0;
    unsigned skipped_count = 0;
    for (uint64_t handler_va : vm_graph->handlerEntries()) {
      // Skip if already lifted (e.g. func_va or vmenter/vmexit).
      std::string name = "sub_" + Twine::utohexstr(handler_va).str();
      if (auto *existing = module->getFunction(name)) {
        if (!existing->isDeclaration()) {
          // Tag existing function as a VM handler.
          existing->addFnAttr("omill.vm_handler");
          continue;
        }
      }

      // Probe decode: skip handler VAs where the first instruction can't
      // be decoded.  These are typically decoy dispatch patterns in
      // obfuscated code with garbage RVAs pointing mid-instruction.
      {
        uint8_t probe_buf[15];
        if (!pe.memory_map.read(handler_va, probe_buf, sizeof(probe_buf))) {
          ++skipped_count;
          continue;
        }
        std::string_view probe_bytes(
            reinterpret_cast<const char *>(probe_buf), sizeof(probe_buf));
        remill::Instruction probe_inst;
        if (!arch->DecodeInstruction(handler_va, probe_bytes, probe_inst,
                                     arch->CreateInitialContext())) {
          ++skipped_count;
          continue;
        }
      }

      if (lifter.Lift(handler_va)) {
        ++lifted_count;
        // Tag the lifted function.
        if (auto *fn = module->getFunction(name))
          fn->addFnAttr("omill.vm_handler");
      } else {
        ++failed_count;
      }
    }

    errs() << "VM bulk lift: " << lifted_count << " handlers lifted";
    if (skipped_count > 0)
      errs() << ", " << skipped_count << " skipped (bad VA)";
    if (failed_count > 0)
      errs() << ", " << failed_count << " failed";
    errs() << "\n";

    // Also tag vmenter/vmexit.
    if (auto *fn = module->getFunction(
            "sub_" + Twine::utohexstr(vm_entry_va).str()))
      fn->addFnAttr("omill.vm_handler");
    if (vm_exit_va != 0) {
      if (auto *fn = module->getFunction(
              "sub_" + Twine::utohexstr(vm_exit_va).str()))
        fn->addFnAttr("omill.vm_handler");
    }

    // Fix DeclareLiftedFunction naming collisions (sub_X.N → sub_X).
    for (auto &F : llvm::make_early_inc_range(*module)) {
      if (!F.isDeclaration())
        continue;
      auto fname = F.getName();
      if (!fname.starts_with("sub_"))
        continue;
      for (int i = 1; i <= 20; ++i) {
        std::string def_name = (fname + "." + Twine(i)).str();
        if (auto *def = module->getFunction(def_name)) {
          if (!def->isDeclaration()) {
            F.replaceAllUsesWith(def);
            F.eraseFromParent();
            def->setName(fname);
            break;
          }
        }
      }
    }
  }

  if (DumpIR) {
    std::error_code ec;
    raw_fd_ostream os("before.ll", ec, sys::fs::OF_Text);
    if (!ec) {
      module->print(os, nullptr);
      errs() << "Wrote before.ll\n";
    }
  }

  // Set up pass timing and verification instrumentation.
  PassInstrumentationCallbacks PIC;
  TimePassesHandler TimingHandler(OmillTimePasses);
  TimingHandler.registerCallbacks(PIC);

  // Set up pass infrastructure
  LoopAnalysisManager LAM;
  FunctionAnalysisManager FAM;
  CGSCCAnalysisManager CGAM;
  ModuleAnalysisManager MAM;

  StandardInstrumentations SI(ctx, /*DebugLogging=*/false,
                              /*VerifyEach=*/false);
  SI.registerCallbacks(PIC, &MAM);

  // Custom safe verify-each: only runs after omill custom passes (not LLVM
  // standard passes) for performance.  Uses nullptr stream to avoid crash
  // in SlotTracker on corrupted modules.
  if (VerifyEach) {
    PIC.registerAfterPassCallback(
        [&](StringRef PassName, Any IR,
            const PreservedAnalyses &) {
          // Skip standard LLVM passes — verifying after every InstCombine/
          // GVN/SimplifyCFG etc. is prohibitively slow.
          static const char *const llvm_passes[] = {
              "InstCombinePass",
              "GVNPass",
              "SimplifyCFGPass",
              "SROAPass",
              "ADCEPass",
              "DSEPass",
              "EarlyCSEPass",
              "GlobalDCEPass",
              "AlwaysInlinerPass",
              "InlinerPass",
              "GlobalOptPass",
              "LoopSimplifyPass",
              "LCSSAPass",
              "LoopRotatePass",
              "LICMPass",
              "IndVarSimplifyPass",
              "LoopDeletionPass",
              "LoopUnrollPass",
              "JumpThreadingPass",
              "CorrelatedValuePropagationPass",
              "MemCpyOptPass",
              "SCCPPass",
              "BDCEPass",
              "ReassociatePass",
              "MergedLoadStoreMotionPass",
              "TailCallElimPass",
              "PromotePass",
              "AggressiveInstCombinePass",
              "LibCallsShrinkWrapPass",
              "ConstraintEliminationPass",
              "CoroSplitPass",
              "CoroElidePass",
              "InvalidateAnalysisPass",
              "RequireAnalysisPass",
              "VerifierPass",
              "PrintModulePass",
              "BitcodeWriterPass",
          };
          for (const char *p : llvm_passes) {
            if (PassName == p) return;
          }
          // Also skip pass manager wrappers and adaptors.
          if (PassName.starts_with("PassManager") ||
              PassName.starts_with("ModuleToFunction") ||
              PassName.starts_with("CGSCCToFunction") ||
              PassName.starts_with("ModuleInliner") ||
              PassName.starts_with("DevirtSCCRepeated") ||
              PassName.contains("Adaptor") ||
              PassName.contains("PassManager"))
            return;

          // Extract the module from whatever IR level we're at.
          const Module *M = nullptr;
          if (const auto **F = any_cast<const Function *>(&IR))
            M = (*F)->getParent();
          else if (const auto **MPtr = any_cast<const Module *>(&IR))
            M = *MPtr;
          else if (const auto **L = any_cast<const Loop *>(&IR))
            M = (*L)->getHeader()->getParent()->getParent();
          if (!M) return;

          if (verifyModule(*M, nullptr)) {
            errs() << "VERIFY-EACH: verification failed after pass: "
                   << PassName << "\n";
            // Don't try module->print() — SlotTracker may crash on
            // corrupted modules with dangling Comdat/Value references.
            // Per-function verification to narrow down:
            for (const auto &F : *M) {
              if (F.isDeclaration()) continue;
              if (verifyFunction(F, nullptr))
                errs() << "  broken function: " << F.getName() << "\n";
            }
            exit(1);
          }
        });
  }

  // --trace-func: print block/instruction counts after every pass for a
  // specific function.  Helps diagnose when the function body disappears.
  if (!TraceFunc.empty()) {
    // Track both the lifted name and the _native wrapper.
    std::string target_base = TraceFunc;
    std::string target_native = target_base + "_native";
    unsigned prev_blocks = 0, prev_insts = 0;
    unsigned prev_blocks_n = 0, prev_insts_n = 0;
    unsigned dump_seq = 0;

    // Helper: dump function IR to a file for post-mortem analysis.
    auto dumpFuncIR = [&](const Function *F, StringRef reason,
                          unsigned seq) {
      if (!DumpFuncPhases || !F || F->isDeclaration())
        return;
      std::string filename = (F->getName() + ".phase" +
                              llvm::Twine(seq) + ".ll").str();
      std::error_code EC;
      llvm::raw_fd_ostream OS(filename, EC);
      if (EC) return;
      OS << "; " << reason << "\n";
      F->print(OS);
      errs() << "[TRACE] dumped " << F->getName() << " → " << filename
             << " (" << reason << ")\n";
    };

    PIC.registerAfterPassCallback(
        [=, &prev_blocks, &prev_insts,
         &prev_blocks_n, &prev_insts_n,
         &dump_seq, &dumpFuncIR](
            StringRef PassName, Any IR, const PreservedAnalyses &) mutable {
          const Module *M = nullptr;
          if (const auto **F = any_cast<const Function *>(&IR))
            M = (*F)->getParent();
          else if (const auto **MPtr = any_cast<const Module *>(&IR))
            M = *MPtr;
          else if (const auto **L = any_cast<const Loop *>(&IR))
            M = (*L)->getHeader()->getParent()->getParent();
          if (!M) return;

          auto report = [&](const std::string &name,
                            unsigned &pb, unsigned &pi) {
            auto *F = M->getFunction(name);
            if (!F || F->isDeclaration()) {
              if (pb != 0 || pi != 0) {
                errs() << "[TRACE] " << PassName << " | " << name
                       << ": GONE (was " << pb << " blocks, "
                       << pi << " instrs)\n";
                pb = 0;
                pi = 0;
              }
              return;
            }
            unsigned blocks = 0, insts = 0;
            for (auto &BB : *F) {
              ++blocks;
              insts += BB.size();
            }
            if (blocks != pb || insts != pi) {
              int di = (pi > 0) ? (int)insts - (int)pi : 0;
              errs() << "[TRACE] " << PassName << " | " << name
                     << ": " << blocks << " blocks, " << insts
                     << " instrs";
              if (pb != 0) {
                int db = (int)blocks - (int)pb;
                errs() << " (delta: " << db << " blocks, "
                       << di << " instrs)";
              }
              errs() << "\n";

              // Dump IR on large drops (>30% instruction loss) or phase markers.
              bool is_phase = PassName.contains("PhaseMarker");
              bool large_drop = pi > 0 && di < 0 &&
                                (unsigned)(-di) > pi * 3 / 10;
              if (DumpFuncPhases && (is_phase || large_drop)) {
                std::string reason = (PassName + " | " +
                    llvm::Twine(blocks) + "bb/" +
                    llvm::Twine(insts) + "i").str();
                dumpFuncIR(F, reason, dump_seq++);
              }

              pb = blocks;
              pi = insts;
            }
          };

          report(target_base, prev_blocks, prev_insts);
          report(target_native, prev_blocks_n, prev_insts_n);
        });
  }

  PassBuilder PB(nullptr, PipelineTuningOptions(), std::nullopt, &PIC);

  // Register custom module analyses first and keep backing storage stable.
  omill::BinaryMemoryMap raw_memory_map;
  if (RawBinary) {
    raw_memory_map.addRegion(BaseAddress, raw_code.data(), raw_code.size());
    raw_memory_map.setImageBase(BaseAddress);
    raw_memory_map.setImageSize(raw_code.size());
  }
  auto memory_map_holder =
      std::make_shared<omill::BinaryMemoryMap>(
          RawBinary ? std::move(raw_memory_map) : pe.memory_map);
  MAM.registerPass([memory_map_holder] {
    return omill::BinaryMemoryAnalysis(*memory_map_holder);
  });

  std::shared_ptr<omill::ExceptionInfo> exception_info_holder;
  if (!RawBinary && ResolveExceptions) {
    exception_info_holder =
        std::make_shared<omill::ExceptionInfo>(std::move(pe.exception_info));
    MAM.registerPass([exception_info_holder] {
      return omill::ExceptionInfoAnalysis(*exception_info_holder);
    });
  }

  // Build AAManager with omill's custom SegmentsAA before standard
  // registration so it's included in LLVM's AA pipeline.
  FAM.registerPass([&] {
    auto AAM = PB.buildDefaultAAPipeline();
    omill::registerAAWithManager(AAM);
    return AAM;
  });

  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);  // AAManager already registered, skipped.
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

  omill::registerAnalyses(FAM);
  // Register remaining module analyses without overriding custom ones above.
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });
  MAM.registerPass([&] { return omill::CallGraphAnalysis(); });
  MAM.registerPass([&] { return omill::LiftedFunctionAnalysis(); });
  if (!ResolveExceptions) {
    MAM.registerPass([&] { return omill::ExceptionInfoAnalysis(); });
  }

  // Register VM handler graph analysis if in VM mode.
  if (vm_graph) {
    MAM.registerPass([vm_graph] {
      return omill::VMHandlerGraphAnalysis(*vm_graph);
    });
  } else {
    MAM.registerPass([&] { return omill::VMHandlerGraphAnalysis(); });
  }

  // Register trace-lift callback so IterativeTargetResolutionPass can
  // lift new functions from resolved dispatch targets.
  {
    omill::TraceLiftCallback trace_cb;
    if (ResolveTargets) {
      trace_cb = [&lifter](uint64_t pc) -> bool {
        return lifter.Lift(pc);
      };
    }
    MAM.registerPass([trace_cb] {
      return omill::TraceLiftAnalysis(trace_cb);
    });
  }

  // Block-lifting mode: set up BlockLifter and register the analysis
  // so IterativeBlockDiscoveryPass can lift new blocks on the fly.
  std::unique_ptr<BufferBlockManager> block_manager;
  std::unique_ptr<omill::BlockLifter> block_lifter;
  if (BlockLift) {
    block_manager = std::make_unique<BufferBlockManager>();
    // Share code with the block manager.
    if (RawBinary) {
      block_manager->setCode(raw_code.data(), raw_code.size(), BaseAddress);
    } else {
      for (auto &sec : pe.code_sections) {
        auto &data = pe.section_storage[sec.storage_index];
        block_manager->setCode(data.data(), data.size(), sec.va);
      }
    }
    block_lifter = std::make_unique<omill::BlockLifter>(
        arch.get(), *block_manager);

    // Do initial block-lifting for the entry function.
    block_lifter->LiftReachable(func_va);
    errs() << "Block-lifting initial reachable blocks complete\n";

    // Register the lift callback so the discovery pass can lift more.
    omill::BlockLiftCallback lift_cb =
        [&](uint64_t pc) -> bool {
          llvm::SmallVector<uint64_t, 4> targets;
          auto *fn = block_lifter->LiftBlock(pc, targets);
          return fn != nullptr;
        };
    MAM.registerPass([lift_cb] {
      return omill::BlockLiftAnalysis(lift_cb);
    });
  }

  // Run the main pipeline (without ABI first)
  omill::PipelineOptions opts;
  opts.recover_abi = false;
  opts.deobfuscate = Deobfuscate;
  opts.resolve_indirect_targets = ResolveTargets;
  opts.max_resolution_iterations = MaxIterations;
  opts.refine_signatures = RefineSignatures;
  opts.interprocedural_const_prop = IPCP;
  opts.use_block_lifting = BlockLift;
  opts.vm_devirtualize = vm_mode;
  {
    ModulePassManager MPM;
    omill::buildPipeline(MPM, opts);
    MPM.run(*module, MAM);
  }
  errs() << "Main pipeline complete\n";

  if (VerifyEach && verifyModule(*module, nullptr)) {
    errs() << "ERROR: module verification failed after main pipeline\n";
    for (const auto &F : *module)
      if (!F.isDeclaration() && verifyFunction(F, nullptr))
        errs() << "  broken function: " << F.getName() << "\n";
    return 1;
  }

  if (DumpIR) {
    std::error_code ec;
    raw_fd_ostream os("after.ll", ec, sys::fs::OF_Text);
    if (!ec) {
      module->print(os, nullptr);
      errs() << "Wrote after.ll\n";
    }
  }

  // VM target discovery loop: after the pipeline resolves dispatch targets,
  // some are newly discovered (image_base + RVA where RVA wasn't in the
  // original binary scan).  Lift these new targets and re-run the pipeline.
  if (vm_mode) {
    for (unsigned vm_round = 0; vm_round < 4; ++vm_round) {
      // Extract discovered dispatch targets from named metadata.
      llvm::DenseSet<uint64_t> dispatch_targets;
      if (auto *named_md =
              module->getNamedMetadata("omill.vm_discovered_targets")) {
        for (unsigned i = 0; i < named_md->getNumOperands(); ++i) {
          auto *tuple = named_md->getOperand(i);
          if (tuple->getNumOperands() == 0)
            continue;
          if (auto *cmd = llvm::dyn_cast<llvm::ConstantAsMetadata>(
                  tuple->getOperand(0))) {
            if (auto *ci =
                    llvm::dyn_cast<llvm::ConstantInt>(cmd->getValue())) {
              uint64_t va = ci->getZExtValue();
              std::string name =
                  "sub_" + llvm::Twine::utohexstr(va).str();
              auto *existing = module->getFunction(name);
              if (!existing || existing->isDeclaration())
                dispatch_targets.insert(va);
            }
          }
        }
        // Remove so next round starts fresh.
        module->eraseNamedMetadata(named_md);
      }

      // Scan for dispatch_call(state, ConstantInt(pc), mem) where pc
      // points to unlifted code.  These are calls whose target was folded
      // to a constant by GVN/InstCombine but wasn't in the module when
      // LowerFunctionCall ran, so they went through the dispatch stub.
      // RewriteLiftedCallsToNative (during ABI recovery) would turn them
      // into inttoptr indirect calls; lifting them NOW lets that pass
      // resolve them to direct calls instead.
      llvm::DenseSet<uint64_t> call_targets;
      auto *dispatch_fn = module->getFunction("__omill_dispatch_call");
      auto *dispatch_jmp = module->getFunction("__omill_dispatch_jump");
      auto scanDispatchUses = [&](llvm::Function *dispatcher) {
        if (!dispatcher)
          return;
        for (auto *U : dispatcher->users()) {
          auto *call = llvm::dyn_cast<llvm::CallInst>(U);
          if (!call || call->arg_size() < 2)
            continue;
          auto *ci = llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
          if (!ci)
            continue;
          uint64_t target = ci->getZExtValue();
          if (target == 0)
            continue;
          bool in_code = false;
          if (RawBinary) {
            in_code = (target >= BaseAddress &&
                       target < BaseAddress + raw_code.size());
          } else {
            for (auto &sec : pe.code_sections) {
              if (target >= sec.va && target < sec.va + sec.size) {
                in_code = true;
                break;
              }
            }
          }
          if (!in_code)
            continue;
          std::string name =
              "sub_" + llvm::Twine::utohexstr(target).str();
          auto *existing = module->getFunction(name);
          if (!existing || existing->isDeclaration())
            call_targets.insert(target);
        }
      };
      scanDispatchUses(dispatch_fn);
      scanDispatchUses(dispatch_jmp);
      // Remove targets already covered by dispatch discovery.
      for (uint64_t va : dispatch_targets)
        call_targets.erase(va);

      if (dispatch_targets.empty() && call_targets.empty())
        break;

      errs() << "VM discovery round " << (vm_round + 1) << ": "
             << dispatch_targets.size() << " dispatch + "
             << call_targets.size() << " call target(s)\n";

      // Lift dispatch targets as VM handlers.
      unsigned lift_ok = 0, lift_fail = 0;
      for (uint64_t va : dispatch_targets) {
        if (lifter.Lift(va)) {
          ++lift_ok;
          std::string name =
              "sub_" + llvm::Twine::utohexstr(va).str();
          if (auto *fn = module->getFunction(name)) {
            fn->addFnAttr("omill.vm_handler");
            fn->addFnAttr("omill.vm_newly_lifted");
          }
        } else {
          ++lift_fail;
        }
      }
      // Lift call targets as regular functions (NOT vm_handler — they
      // get _native wrappers via RecoverFunctionSignatures).
      for (uint64_t va : call_targets) {
        if (lifter.Lift(va)) {
          ++lift_ok;
          std::string name =
              "sub_" + llvm::Twine::utohexstr(va).str();
          if (auto *fn = module->getFunction(name))
            fn->addFnAttr("omill.vm_newly_lifted");
        } else {
          ++lift_fail;
        }
      }

      // Fix DeclareLiftedFunction naming collisions.
      for (auto &F : llvm::make_early_inc_range(*module)) {
        if (!F.isDeclaration())
          continue;
        auto fname = F.getName();
        if (!fname.starts_with("sub_"))
          continue;
        for (int i = 1; i <= 20; ++i) {
          std::string def_name = (fname + "." + Twine(i)).str();
          if (auto *def = module->getFunction(def_name)) {
            if (!def->isDeclaration()) {
              F.replaceAllUsesWith(def);
              F.eraseFromParent();
              def->setName(fname);
              break;
            }
          }
        }
      }

      errs() << "  lifted " << lift_ok;
      if (lift_fail > 0)
        errs() << " (" << lift_fail << " failed)";
      errs() << "\n";

      if (lift_ok == 0)
        break;

      // Re-run the pipeline on the updated module.  Use a lightweight
      // configuration that skips deobfuscation (Phase 5) and iterative
      // target resolution (Phase 3.6) — the outer VM discovery loop
      // handles the iteration, and deobf is deferred to post-ABI.
      MAM.invalidate(*module, llvm::PreservedAnalyses::none());
      {
        omill::PipelineOptions vm_opts = opts;
        vm_opts.deobfuscate = false;
        vm_opts.resolve_indirect_targets = false;
        vm_opts.interprocedural_const_prop = false;
        vm_opts.scope_predicate = [](llvm::Function &F) {
          return F.hasFnAttribute("omill.vm_newly_lifted");
        };
        ModulePassManager MPM;
        omill::buildPipeline(MPM, vm_opts);
        MPM.run(*module, MAM);
      }

      // Clear the newly-lifted tags so next round starts fresh.
      for (auto &F : *module) {
        if (F.hasFnAttribute("omill.vm_newly_lifted"))
          F.removeFnAttr("omill.vm_newly_lifted");
      }

      errs() << "  pipeline re-run complete\n";

      // Checkpoint: save LL after each VM discovery round.
      repairMalformedPHIs(*module);
      {
        std::string ckpt_name =
            "vm_round_" + std::to_string(vm_round + 1) + ".ll";
        std::error_code ec;
        raw_fd_ostream os(ckpt_name, ec, sys::fs::OF_Text);
        if (!ec) {
          module->print(os, nullptr);
          errs() << "  saved checkpoint: " << ckpt_name << "\n";
        }
      }
    }
  }

  // ABI recovery
  if (!NoABI) {
    // Repair broken PHIs before saving checkpoint (otherwise LLVM parser
    // rejects the LL on reload).
    repairMalformedPHIs(*module);
    // Checkpoint before ABI recovery (enables resuming after crash).
    {
      std::error_code ec;
      raw_fd_ostream os("before_abi.ll", ec, sys::fs::OF_Text);
      if (!ec) {
        module->print(os, nullptr);
        errs() << "Saved before_abi.ll\n";
      }
    }
    ModulePassManager MPM;
    omill::buildABIRecoveryPipeline(MPM);
    MPM.run(*module, MAM);
    errs() << "ABI recovery complete\n";

    if (VerifyEach && verifyModule(*module, nullptr)) {
      errs() << "ERROR: module verification failed after ABI recovery\n";
      for (const auto &F : *module)
        if (!F.isDeclaration() && verifyFunction(F, nullptr))
          errs() << "  broken function: " << F.getName() << "\n";
      return 1;
    }

    // Patch B3 call sites: after ABI recovery created _native wrappers,
    // scan for inttoptr(i64 X to ptr) call targets where @sub_X_native
    // exists, and rewrite them to direct calls.  This resolves constant
    // targets that were discovered during VM discovery or optimization
    // but couldn't be resolved at the time (the target wasn't lifted yet
    // when RewriteLiftedCallsToNative ran).
    {
      unsigned patched = 0;
      // Collect all constant-integer values used as inttoptr call targets.
      llvm::DenseSet<uint64_t> targets_to_patch;
      for (auto &F : *module) {
        for (auto &BB : F) {
          for (auto &I : BB) {
            auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!call || call->getCalledFunction())
              continue;
            auto *callee_op = call->getCalledOperand();
            llvm::ConstantInt *ci = nullptr;
            if (auto *ce =
                    llvm::dyn_cast<llvm::ConstantExpr>(callee_op)) {
              if (ce->getOpcode() == llvm::Instruction::IntToPtr)
                ci = llvm::dyn_cast<llvm::ConstantInt>(
                    ce->getOperand(0));
            }
            if (!ci) {
              if (auto *itp =
                      llvm::dyn_cast<llvm::IntToPtrInst>(callee_op))
                ci = llvm::dyn_cast<llvm::ConstantInt>(
                    itp->getOperand(0));
            }
            if (ci && ci->getZExtValue() != 0)
              targets_to_patch.insert(ci->getZExtValue());
          }
        }
      }
      for (uint64_t pc : targets_to_patch) {
        std::string native_name =
            "sub_" + llvm::Twine::utohexstr(pc).str() + "_native";
        auto *target_fn = module->getFunction(native_name);
        if (!target_fn)
          continue;
        auto *pc_ci =
            llvm::ConstantInt::get(llvm::Type::getInt64Ty(ctx), pc);
        // ConstantExpr inttoptr — RAUW replaces all uses globally.
        auto *itp_ce = llvm::ConstantExpr::getIntToPtr(
            pc_ci, llvm::PointerType::getUnqual(ctx));
        if (itp_ce->getNumUses() > 0) {
          patched += itp_ce->getNumUses();
          itp_ce->replaceAllUsesWith(target_fn);
        }
        // IntToPtrInst with constant operand.
        // ConstantInt is a ConstantData — it may not have a use list in LLVM 21.
        if (!pc_ci->hasUseList())
          continue;
        for (auto *user : llvm::make_early_inc_range(pc_ci->users())) {
          auto *inst = llvm::dyn_cast<llvm::IntToPtrInst>(user);
          if (!inst)
            continue;
          patched += inst->getNumUses();
          inst->replaceAllUsesWith(target_fn);
          if (inst->use_empty())
            inst->eraseFromParent();
        }
      }
      if (patched > 0)
        errs() << "Patched " << patched
               << " inttoptr call sites to direct calls\n";
    }

    // Post-ABI deobfuscation on _native functions.  When recover_abi is
    // false (VM mode), Phase 5 ran on pre-ABI sub_* functions, so _native
    // wrappers created by ABI recovery haven't been deobfuscated yet.
    if (Deobfuscate) {
      llvm::FunctionPassManager FPM;
      omill::buildDeobfuscationPipeline(FPM);
      for (auto &F : *module) {
        if (F.isDeclaration() || !F.getName().ends_with("_native"))
          continue;
        auto &FAM =
            MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(*module)
                .getManager();
        auto PA = FPM.run(F, FAM);
        if (!PA.areAllPreserved())
          FAM.invalidate(F, PA);
      }
      errs() << "Post-ABI deobfuscation complete\n";
    }
  }

  // Late target discovery: after ABI recovery folds MBA chains (via
  // EliminateStateStruct + RecoverStackFrame + SROA + GVN), scan for
  // constant inttoptr call targets that point to unlifted code addresses.
  // Lift them into a FRESH semantics module (the main module's remill
  // state was destroyed by the pipeline), run the pipeline + ABI on it,
  // then link the resulting _native functions back into the main module.
  if (ResolveTargets && !NoABI) {
    for (unsigned round = 0; round < 3; ++round) {
      // Collect constant inttoptr call targets.
      // Match both ConstantExpr::IntToPtr and IntToPtrInst with constant
      // operands — LLVM 21 no longer folds inttoptr(const) instructions
      // to ConstantExpr form, so B3 dynamic rewrites from
      // RewriteLiftedCallsToNative produce IntToPtrInst after GVN folds.
      llvm::DenseSet<uint64_t> late_targets;
      for (auto &F : *module) {
        for (auto &BB : F) {
          for (auto &I : BB) {
            auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
            if (!call || call->getCalledFunction())
              continue;
            auto *callee_op = call->getCalledOperand();
            llvm::ConstantInt *ci = nullptr;
            // Case 1: ConstantExpr inttoptr.
            if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(callee_op)) {
              if (ce->getOpcode() == llvm::Instruction::IntToPtr)
                ci = llvm::dyn_cast<llvm::ConstantInt>(ce->getOperand(0));
            }
            // Case 2: IntToPtrInst with constant operand.
            if (!ci) {
              if (auto *itp = llvm::dyn_cast<llvm::IntToPtrInst>(callee_op))
                ci = llvm::dyn_cast<llvm::ConstantInt>(itp->getOperand(0));
            }
            if (!ci)
              continue;
            uint64_t target = ci->getZExtValue();
            if (target == 0)
              continue;
            bool in_code = false;
            if (RawBinary) {
              in_code = (target >= BaseAddress &&
                         target < BaseAddress + raw_code.size());
            } else {
              for (auto &sec : pe.code_sections) {
                if (target >= sec.va && target < sec.va + sec.size) {
                  in_code = true;
                  break;
                }
              }
            }
            if (!in_code)
              continue;
            std::string name = "sub_" + llvm::Twine::utohexstr(target).str();
            if (module->getFunction(name) ||
                module->getFunction(name + "_native"))
              continue;
            late_targets.insert(target);
          }
        }
      }

      if (late_targets.empty())
        break;

      errs() << "Late discovery round " << (round + 1) << ": "
             << late_targets.size() << " new target(s)\n";

      // Load fresh arch + semantics for lifting (the main module's
      // remill ISEL stubs and intrinsics were deleted by the pipeline).
      auto late_arch =
          remill::Arch::Get(ctx, os_name, remill::kArchAMD64_AVX);
      auto late_module = remill::LoadArchSemantics(late_arch.get());

      BufferTraceManager late_manager;
      late_manager.setModuleAndArch(late_module.get(), late_arch.get());
      if (RawBinary) {
        late_manager.setCode(raw_code.data(), raw_code.size(), BaseAddress);
      } else {
        for (const auto &cs : pe.code_sections) {
          auto &stored = pe.section_storage[cs.storage_index];
          late_manager.setCode(stored.data(), stored.size(), cs.va);
        }
      }

      omill::TraceLifter late_lifter(late_arch.get(), late_manager);

      // Lift the target functions and their full callee graphs.
      for (uint64_t pc : late_targets) {
        late_lifter.Lift(pc);
      }

      // Fix up DeclareLiftedFunction naming collisions.  When the
      // TraceLifter creates a declaration for a callee reference and
      // later defines it, LLVM appends ".N" to the definition because
      // the declaration already occupies the name.  Replace uses of
      // the empty declaration with the actual definition, then rename.
      for (auto &F : llvm::make_early_inc_range(*late_module)) {
        if (!F.isDeclaration())
          continue;
        auto name = F.getName();
        if (!name.starts_with("sub_"))
          continue;
        for (int i = 1; i <= 20; ++i) {
          std::string def_name =
              (name + "." + llvm::Twine(i)).str();
          if (auto *def = late_module->getFunction(def_name)) {
            if (!def->isDeclaration()) {
              F.replaceAllUsesWith(def);
              F.eraseFromParent();
              def->setName(name);
              break;
            }
          }
        }
      }

      if (DumpIR) {
        std::error_code ec;
        raw_fd_ostream os("late_after_lift.ll", ec, sys::fs::OF_Text);
        late_module->print(os, nullptr);
      }

      // Run the pipeline on the fresh module.
      {
        PassBuilder late_PB;
        LoopAnalysisManager late_LAM;
        FunctionAnalysisManager late_FAM;
        CGSCCAnalysisManager late_CGAM;
        ModuleAnalysisManager late_MAM;

        late_FAM.registerPass([&late_PB] {
          auto AAM = late_PB.buildDefaultAAPipeline();
          omill::registerAAWithManager(AAM);
          return AAM;
        });
        late_PB.registerModuleAnalyses(late_MAM);
        late_PB.registerCGSCCAnalyses(late_CGAM);
        late_PB.registerFunctionAnalyses(late_FAM);
        late_PB.registerLoopAnalyses(late_LAM);
        late_PB.crossRegisterProxies(late_LAM, late_FAM, late_CGAM,
                                     late_MAM);
        omill::registerAnalyses(late_FAM);

        late_MAM.registerPass([memory_map_holder] {
          return omill::BinaryMemoryAnalysis(*memory_map_holder);
        });
        late_MAM.registerPass([&] {
          return omill::CallingConventionAnalysis();
        });
        late_MAM.registerPass([&] {
          return omill::CallGraphAnalysis();
        });
        late_MAM.registerPass([&] {
          return omill::LiftedFunctionAnalysis();
        });
        late_MAM.registerPass([&] {
          return omill::ExceptionInfoAnalysis();
        });
        late_MAM.registerPass([] {
          return omill::TraceLiftAnalysis(omill::TraceLiftCallback{});
        });
        late_MAM.registerPass([&] {
          return omill::VMHandlerGraphAnalysis();
        });

        omill::PipelineOptions late_opts = opts;
        late_opts.resolve_indirect_targets = false;
        {
          ModulePassManager MPM;
          omill::buildPipeline(MPM, late_opts);
          MPM.run(*late_module, late_MAM);
        }
        if (DumpIR) {
          std::error_code ec;
          raw_fd_ostream os("late_after_pipeline.ll", ec,
                            sys::fs::OF_Text);
          late_module->print(os, nullptr);
        }
        {
          ModulePassManager MPM;
          omill::buildABIRecoveryPipeline(MPM);
          MPM.run(*late_module, late_MAM);
        }
      }

      if (DumpIR) {
        std::error_code ec;
        raw_fd_ostream os("late_after_abi.ll", ec, sys::fs::OF_Text);
        late_module->print(os, nullptr);
      }

      // Remove conflicting definitions from the late module.  The main
      // module's initial callee graph may already contain some of the
      // same functions; keep those and let the linker resolve the late
      // module's references to the existing definitions.
      for (auto &F : llvm::make_early_inc_range(*late_module)) {
        if (F.isDeclaration())
          continue;
        if (auto *existing = module->getFunction(F.getName())) {
          if (!existing->isDeclaration()) {
            F.deleteBody();
            F.setLinkage(llvm::GlobalValue::ExternalLinkage);
          }
        }
      }

      // Link the late module into the main module.  Linker replaces
      // declarations with definitions and handles type merging.
      if (llvm::Linker::linkModules(*module, std::move(late_module))) {
        errs() << "WARNING: linking late module failed\n";
        break;
      }

      // Patch call sites: replace inttoptr(i64 <const>) → @sub_<hex>_native
      // Handles both ConstantExpr and IntToPtrInst forms.
      for (uint64_t pc : late_targets) {
        std::string native_name =
            "sub_" + llvm::Twine::utohexstr(pc).str() + "_native";
        auto *target_fn = module->getFunction(native_name);
        if (!target_fn)
          continue;
        auto *pc_ci = llvm::ConstantInt::get(
            llvm::Type::getInt64Ty(ctx), pc);

        // Case 1: ConstantExpr inttoptr — RAUW replaces all uses globally.
        auto *itp = llvm::ConstantExpr::getIntToPtr(
            pc_ci, llvm::PointerType::getUnqual(ctx));
        if (itp->getNumUses() > 0)
          itp->replaceAllUsesWith(target_fn);

        // Case 2: IntToPtrInst instructions with this constant operand.
        // Each instruction is a separate Value, so scan and replace each.
        // ConstantInt (ConstantData) may not have a use list in LLVM 21.
        if (!pc_ci->hasUseList())
          continue;
        for (auto *user : llvm::make_early_inc_range(pc_ci->users())) {
          auto *inst = llvm::dyn_cast<llvm::IntToPtrInst>(user);
          if (!inst)
            continue;
          inst->replaceAllUsesWith(target_fn);
          if (inst->use_empty())
            inst->eraseFromParent();
        }
      }

      errs() << "Late discovery round " << (round + 1) << " complete\n";
    }
  }

  if (OmillTimePasses)
    TimingHandler.print();

  // Verify (use nullptr to avoid crash in SlotTracker on corrupted modules)
  if (verifyModule(*module, nullptr)) {
    errs() << "WARNING: module verification failed (use --verify-each to "
              "identify the culprit pass)\n";
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

  if (DumpIR) {
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
