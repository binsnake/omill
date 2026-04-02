#include "InputLoader.h"

#include <algorithm>
#include <cstring>

#include <llvm/ADT/Twine.h>
#include <llvm/BinaryFormat/COFF.h>
#include <llvm/BinaryFormat/MachO.h>
#include <llvm/BinaryFormat/Magic.h>
#include <llvm/Object/COFF.h>
#include <llvm/Object/MachO.h>
#include <llvm/Object/MachOUniversal.h>
#include <llvm/Object/ObjectFile.h>
#include <llvm/Support/Error.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/Win64EH.h>
#include <llvm/Support/raw_ostream.h>

using namespace llvm;

bool sectionContainsVA(const SectionInfo &section, uint64_t va) {
  return va >= section.va && va < (section.va + section.size);
}

bool matchesSectionName(const SectionInfo &section,
                        llvm::StringRef requested_name) {
  if (requested_name == section.section_name)
    return true;
  if (!section.segment_name.empty() &&
      requested_name ==
          (Twine(section.segment_name) + "," + section.section_name).str()) {
    return true;
  }
  return false;
}

const SectionInfo *findCodeSection(const PEInfo &pe, uint64_t va) {
  for (const auto &section : pe.code_sections) {
    if (sectionContainsVA(section, va))
      return &section;
  }
  return nullptr;
}

const SectionInfo *findCodeSectionByName(const PEInfo &pe,
                                         llvm::StringRef name) {
  for (const auto &section : pe.code_sections) {
    if (matchesSectionName(section, name))
      return &section;
  }
  return nullptr;
}

std::vector<uint64_t> collectBatchFunctionStarts(const PEInfo &pe) {
  std::vector<uint64_t> starts;
  if (pe.is_macho) {
    starts = pe.discovered_function_starts;
  } else {
    starts.reserve(pe.exception_info.entries().size());
    for (const auto &entry : pe.exception_info.entries())
      starts.push_back(entry.begin_va);
  }

  llvm::sort(starts);
  starts.erase(std::unique(starts.begin(), starts.end()), starts.end());
  return starts;
}

// Parse .pdata (exception table) from a PE binary.
// Populates exception_info with RUNTIME_FUNCTION entries that have
// language-specific exception handlers.
static void parsePData(const object::COFFObjectFile &coff, uint64_t image_base,
                       omill::ExceptionInfo &exception_info) {
  const object::data_directory *dd =
      coff.getDataDirectory(COFF::EXCEPTION_TABLE);
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

    uint64_t handler_va = 0;
    uint64_t handler_data_va = 0;
    uint32_t current_unwind_rva = unwind_rva;

    for (unsigned depth = 0; depth < 16; ++depth) {
      uintptr_t unwind_ptr = 0;
      if (auto err = coff.getRvaPtr(current_unwind_rva, unwind_ptr)) {
        consumeError(std::move(err));
        break;
      }

      auto *uwi = reinterpret_cast<const Win64EH::UnwindInfo *>(unwind_ptr);
      uint8_t flags = uwi->getFlags();

      if (flags & Win64EH::UNW_ExceptionHandler) {
        uint32_t handler_rva = uwi->getLanguageSpecificHandlerOffset();
        handler_va = image_base + handler_rva;

        auto *lsd = reinterpret_cast<const support::ulittle32_t *>(
            uwi->getLanguageSpecificData());
        uint32_t data_rva = lsd[1];
        if (data_rva != 0)
          handler_data_va = image_base + data_rva;
        break;
      }

      if (flags & Win64EH::UNW_ChainInfo) {
        auto *chained = uwi->getChainedFunctionEntry();
        current_unwind_rva = chained->UnwindInfoOffset;
        continue;
      }

      break;
    }

    exception_info.addEntry({image_base + begin_rva, image_base + end_rva,
                             handler_va, handler_data_va, 0, 0});
  }
}

bool loadPE(StringRef path, PEInfo &out) {
  out.is_macho = false;
  auto buf_or_err = MemoryBuffer::getFile(path);
  if (!buf_or_err) {
    errs() << "Cannot open " << path << ": "
           << buf_or_err.getError().message() << "\n";
    return false;
  }

  auto obj_or_err =
      object::COFFObjectFile::create((*buf_or_err)->getMemBufferRef());
  if (!obj_or_err) {
    errs() << "Not a valid COFF/PE: " << toString(obj_or_err.takeError())
           << "\n";
    return false;
  }
  auto &coff = **obj_or_err;
  out.image_base = coff.getImageBase();

  for (const auto &dir : coff.import_directories()) {
    StringRef dll_name;
    if (dir.getName(dll_name))
      continue;

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

  for (const auto &exp : coff.export_directories()) {
    bool is_forwarder = false;
    if (auto err = exp.isForwarder(is_forwarder)) {
      consumeError(std::move(err));
      continue;
    }
    if (is_forwarder)
      continue;

    uint32_t export_rva = 0;
    if (auto err = exp.getExportRVA(export_rva)) {
      consumeError(std::move(err));
      continue;
    }
    if (!export_rva)
      continue;

    out.exported_function_starts.push_back(out.image_base + export_rva);
  }
  llvm::sort(out.exported_function_starts);
  out.exported_function_starts.erase(
      std::unique(out.exported_function_starts.begin(),
                  out.exported_function_starts.end()),
      out.exported_function_starts.end());

  uint64_t image_size = 0;
  if (auto *pe32p = coff.getPE32PlusHeader())
    image_size = pe32p->SizeOfImage;
  else if (auto *pe32 = coff.getPE32Header())
    image_size = pe32->SizeOfImage;
  out.memory_map.setImageBase(out.image_base);
  out.memory_map.setImageSize(image_size);

  if (out.memory_map.isSuspiciousImageBase()) {
    errs() << "WARNING: suspicious preferred image base 0x"
           << Twine::utohexstr(out.image_base)
           << " - ASLR will likely produce a non-zero delta.\n"
           << "         Relocated constants in the binary may be unreliable.\n";
  }

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
      continue;

    out.memory_map.addRelocation(out.image_base + rva, reloc_size);
  }
  out.memory_map.finalizeRelocations();

  for (const auto &sec : coff.sections()) {
    auto contents_or_err = sec.getContents();
    if (!contents_or_err) {
      consumeError(contents_or_err.takeError());
      continue;
    }
    StringRef contents = *contents_or_err;

    uint64_t va = sec.getAddress();
    size_t idx = out.section_storage.size();
    out.section_storage.emplace_back(
        reinterpret_cast<const uint8_t *>(contents.data()),
        reinterpret_cast<const uint8_t *>(contents.data()) + contents.size());
    auto &stored = out.section_storage.back();
    const auto *coff_sec = coff.getCOFFSection(sec);
    bool read_only = true;
    if (coff_sec && (coff_sec->Characteristics & COFF::IMAGE_SCN_MEM_WRITE))
      read_only = false;
    bool executable =
        coff_sec &&
        (coff_sec->Characteristics &
         (COFF::IMAGE_SCN_CNT_CODE | COFF::IMAGE_SCN_MEM_EXECUTE));
    out.memory_map.addRegion(va, stored.data(), stored.size(), read_only,
                             executable);

    Expected<StringRef> name_or = sec.getName();
    std::string section_name;
    if (name_or)
      section_name = name_or->str();
    else
      consumeError(name_or.takeError());
    if (coff_sec &&
        (coff_sec->Characteristics &
         (COFF::IMAGE_SCN_CNT_CODE | COFF::IMAGE_SCN_MEM_EXECUTE))) {
      out.code_sections.push_back({va, stored.size(), idx, "", section_name});
    }
  }

  parsePData(coff, out.image_base, out.exception_info);
  out.exception_info.setImageBase(out.image_base);

  out.exception_info.buildSyntheticDCs(out.synthetic_dc_storage, out.memory_map,
                                       out.image_base);

  return true;
}

static void collectMachOFunctionStarts(object::MachOObjectFile &macho,
                                       PEInfo &out) {
  for (uint64_t start : macho.getFunctionStarts()) {
    if (findCodeSection(out, start))
      out.discovered_function_starts.push_back(start);
  }

  for (const auto &sym : macho.symbols()) {
    auto type_or = sym.getType();
    if (!type_or) {
      consumeError(type_or.takeError());
      continue;
    }
    if (*type_or != object::SymbolRef::ST_Function)
      continue;

    auto flags_or = sym.getFlags();
    if (!flags_or) {
      consumeError(flags_or.takeError());
      continue;
    }
    if (*flags_or & object::BasicSymbolRef::SF_Undefined)
      continue;

    auto addr_or = sym.getAddress();
    if (!addr_or) {
      consumeError(addr_or.takeError());
      continue;
    }
    if (*addr_or == 0)
      continue;
    if (findCodeSection(out, *addr_or))
      out.discovered_function_starts.push_back(*addr_or);
  }

  llvm::sort(out.discovered_function_starts);
  out.discovered_function_starts.erase(
      std::unique(out.discovered_function_starts.begin(),
                  out.discovered_function_starts.end()),
      out.discovered_function_starts.end());
}

static void parseMachOContents(object::MachOObjectFile &macho, PEInfo &out) {
  uint64_t text_vmaddr = 0;
  uint64_t max_addr = 0;
  for (const auto &cmd : macho.load_commands()) {
    if (cmd.C.cmd == MachO::LC_SEGMENT_64) {
      auto seg = macho.getSegment64LoadCommand(cmd);
      StringRef seg_name(seg.segname, strnlen(seg.segname, 16));
      uint64_t end = seg.vmaddr + seg.vmsize;
      if (end > max_addr)
        max_addr = end;
      if (seg_name == "__TEXT" && text_vmaddr == 0)
        text_vmaddr = seg.vmaddr;
    }
  }
  out.image_base = text_vmaddr;
  out.memory_map.setImageBase(text_vmaddr);
  out.memory_map.setImageSize(
      max_addr > text_vmaddr ? max_addr - text_vmaddr : 0);

  for (const auto &sec : macho.sections()) {
    auto contents_or = sec.getContents();
    if (!contents_or) {
      consumeError(contents_or.takeError());
      continue;
    }
    StringRef contents = *contents_or;
    uint64_t va = sec.getAddress();
    size_t idx = out.section_storage.size();
    out.section_storage.emplace_back(
        reinterpret_cast<const uint8_t *>(contents.data()),
        reinterpret_cast<const uint8_t *>(contents.data()) + contents.size());
    auto &stored = out.section_storage.back();
    auto name_or = sec.getName();
    std::string section_name;
    if (name_or)
      section_name = name_or->str();
    else
      consumeError(name_or.takeError());
    std::string seg_name =
        macho.getSectionFinalSegmentName(sec.getRawDataRefImpl()).str();
    bool read_only = !llvm::StringRef(seg_name).starts_with("__DATA");
    bool executable = sec.isText() || section_name == "__stubs";
    out.memory_map.addRegion(va, stored.data(), stored.size(), read_only,
                             executable);
    if (executable) {
      out.code_sections.push_back(
          {va, stored.size(), idx, seg_name, section_name});
    }
  }

  collectMachOFunctionStarts(macho, out);

  {
    Error err = Error::success();
    for (const auto &entry : macho.bindTable(err)) {
      uint64_t addr = entry.address();
      StringRef sym = entry.symbolName();
      if (sym.starts_with("_"))
        sym = sym.drop_front(1);
      StringRef lib_name;
      int ord = entry.ordinal();
      if (ord > 0)
        macho.getLibraryShortNameByIndex(ord - 1, lib_name);
      out.memory_map.addImport(addr, lib_name.str(), sym.str());
    }
    if (err)
      consumeError(std::move(err));
  }
  {
    Error err = Error::success();
    for (const auto &entry : macho.lazyBindTable(err)) {
      uint64_t addr = entry.address();
      StringRef sym = entry.symbolName();
      if (sym.starts_with("_"))
        sym = sym.drop_front(1);
      StringRef lib_name;
      int ord = entry.ordinal();
      if (ord > 0)
        macho.getLibraryShortNameByIndex(ord - 1, lib_name);
      out.memory_map.addImport(addr, lib_name.str(), sym.str());
    }
    if (err)
      consumeError(std::move(err));
  }

  {
    Error err = Error::success();
    for (const auto &entry : macho.rebaseTable(err)) {
      out.memory_map.addRelocation(entry.address(), 8);
    }
    if (err)
      consumeError(std::move(err));
  }
  out.memory_map.finalizeRelocations();
}

bool loadMachO(StringRef path, PEInfo &out, remill::ArchName &out_arch,
               remill::OSName &out_os) {
  out.is_macho = true;
  auto buf_or_err = MemoryBuffer::getFile(path);
  if (!buf_or_err) {
    errs() << "Cannot open " << path << ": "
           << buf_or_err.getError().message() << "\n";
    return false;
  }

  MemoryBufferRef mbr = (*buf_or_err)->getMemBufferRef();
  auto magic = identify_magic(mbr.getBuffer());

  if (magic == file_magic::macho_universal_binary) {
    auto uni_or = object::MachOUniversalBinary::create(mbr);
    if (!uni_or) {
      errs() << "Invalid fat binary: " << toString(uni_or.takeError()) << "\n";
      return false;
    }
    auto &uni = **uni_or;

    const object::MachOUniversalBinary::ObjectForArch *arm64_slice = nullptr;
    const object::MachOUniversalBinary::ObjectForArch *x64_slice = nullptr;
    for (const auto &obj : uni.objects()) {
      if (obj.getCPUType() == MachO::CPU_TYPE_ARM64)
        arm64_slice = &obj;
      else if (obj.getCPUType() == MachO::CPU_TYPE_X86_64)
        x64_slice = &obj;
    }
    auto *chosen = arm64_slice ? arm64_slice : x64_slice;
    if (!chosen) {
      errs() << "Fat binary has no arm64 or x86_64 slice\n";
      return false;
    }
    auto obj_or = chosen->getAsObjectFile();
    if (!obj_or) {
      errs() << "Cannot extract slice: " << toString(obj_or.takeError())
             << "\n";
      return false;
    }
    auto &macho = **obj_or;

    if (chosen == arm64_slice) {
      out_arch = remill::kArchAArch64LittleEndian;
    } else {
      out_arch = remill::kArchAMD64_AVX;
    }
    out_os = remill::kOSmacOS;

    parseMachOContents(macho, out);
    return true;
  }

  auto obj_or = object::ObjectFile::createMachOObjectFile(mbr);
  if (!obj_or) {
    errs() << "Not a valid Mach-O: " << toString(obj_or.takeError()) << "\n";
    return false;
  }
  auto &macho = *llvm::cast<object::MachOObjectFile>(obj_or->get());

  auto header = macho.getHeader();
  if (header.cputype == MachO::CPU_TYPE_ARM64) {
    out_arch = remill::kArchAArch64LittleEndian;
  } else if (header.cputype == MachO::CPU_TYPE_X86_64) {
    out_arch = remill::kArchAMD64_AVX;
  } else {
    errs() << "Unsupported Mach-O CPU type: " << header.cputype << "\n";
    return false;
  }
  out_os = remill::kOSmacOS;

  parseMachOContents(macho, out);
  return true;
}

bool looksLikeMachOInput(StringRef path) {
  auto probe_buf = MemoryBuffer::getFile(path);
  if (!probe_buf)
    return false;

  auto magic = identify_magic((*probe_buf)->getBuffer());
  return magic == file_magic::macho_object ||
         magic == file_magic::macho_executable ||
         magic == file_magic::macho_dynamically_linked_shared_lib ||
         magic == file_magic::macho_bundle ||
         magic == file_magic::macho_universal_binary;
}
