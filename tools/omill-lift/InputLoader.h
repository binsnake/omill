#pragma once

#include <cstddef>
#include <cstdint>
#include <deque>
#include <string>
#include <vector>

#include <llvm/ADT/StringRef.h>

#include <remill/Arch/Name.h>
#include <remill/OS/OS.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/ExceptionInfo.h"

struct SectionInfo {
  uint64_t va;
  size_t size;
  size_t storage_index;  // index into section_storage
  std::string segment_name;
  std::string section_name;
};

// Historical name kept for minimal churn in the omill-lift driver.
// This structure now carries both PE and Mach-O loader results.
struct PEInfo {
  std::deque<std::vector<uint8_t>> section_storage;
  omill::BinaryMemoryMap memory_map;
  omill::ExceptionInfo exception_info;
  std::vector<SectionInfo> code_sections;
  std::vector<uint64_t> discovered_function_starts;
  std::vector<uint64_t> exported_function_starts;
  std::deque<std::vector<uint8_t>> synthetic_dc_storage;
  uint64_t image_base = 0;
  bool is_macho = false;
};

bool sectionContainsVA(const SectionInfo &section, uint64_t va);
bool matchesSectionName(const SectionInfo &section,
                        llvm::StringRef requested_name);
const SectionInfo *findCodeSection(const PEInfo &pe, uint64_t va);
const SectionInfo *findCodeSectionByName(const PEInfo &pe,
                                         llvm::StringRef name);
std::vector<uint64_t> collectBatchFunctionStarts(const PEInfo &pe);

bool loadPE(llvm::StringRef path, PEInfo &out);
bool loadMachO(llvm::StringRef path, PEInfo &out, remill::ArchName &out_arch,
               remill::OSName &out_os);
bool looksLikeMachOInput(llvm::StringRef path);
