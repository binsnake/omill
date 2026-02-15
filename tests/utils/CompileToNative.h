#pragma once

#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IR/Module.h>
#include <llvm/MC/TargetRegistry.h>
#include <llvm/Object/COFF.h>
#include <llvm/Object/ObjectFile.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Target/TargetMachine.h>
#include <llvm/Target/TargetOptions.h>
#include <llvm/TargetParser/Triple.h>

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

namespace omill::test {

/// One-time LLVM target initialization. Safe to call multiple times.
inline void initializeX86Target() {
  static bool done = false;
  if (done) return;
  LLVMInitializeX86TargetInfo();
  LLVMInitializeX86Target();
  LLVMInitializeX86TargetMC();
  LLVMInitializeX86AsmPrinter();
  LLVMInitializeX86AsmParser();
  done = true;
}

/// Result of compiling a module to native code.
struct NativeCode {
  std::vector<uint8_t> text;   // .text section bytes
  uint64_t text_addr = 0;      // virtual address of .text
  std::string error;           // non-empty on failure

  bool ok() const { return error.empty() && !text.empty(); }
};

/// Compile an LLVM module to x86-64 COFF object code and extract the .text
/// section.  The module's data layout and triple are overwritten to match
/// x86_64-pc-windows-msvc.
inline NativeCode compileToNative(llvm::Module &M) {
  initializeX86Target();

  NativeCode result;
  std::string err;
  const llvm::Target *target =
      llvm::TargetRegistry::lookupTarget("x86_64-pc-windows-msvc", err);
  if (!target) {
    result.error = "Target lookup failed: " + err;
    return result;
  }

  llvm::TargetOptions opts;
  auto *TM = target->createTargetMachine(
      llvm::Triple("x86_64-pc-windows-msvc"), "x86-64", "", opts,
      llvm::Reloc::Static, llvm::CodeModel::Small,
      llvm::CodeGenOptLevel::Default);
  if (!TM) {
    result.error = "Failed to create TargetMachine";
    return result;
  }

  M.setDataLayout(TM->createDataLayout());
  M.setTargetTriple(llvm::Triple("x86_64-pc-windows-msvc"));

  llvm::SmallVector<char, 4096> obj_buf;
  llvm::raw_svector_ostream obj_stream(obj_buf);

  llvm::legacy::PassManager PM;
  if (TM->addPassesToEmitFile(PM, obj_stream, nullptr,
                               llvm::CodeGenFileType::ObjectFile)) {
    result.error = "addPassesToEmitFile failed";
    delete TM;
    return result;
  }
  PM.run(M);
  delete TM;

  // Parse the COFF object to extract .text.
  auto buf = llvm::MemoryBuffer::getMemBuffer(
      llvm::StringRef(obj_buf.data(), obj_buf.size()), "", false);
  auto obj_or_err =
      llvm::object::ObjectFile::createObjectFile(buf->getMemBufferRef());
  if (!obj_or_err) {
    result.error = "Failed to parse object: " +
                   llvm::toString(obj_or_err.takeError());
    return result;
  }

  auto &obj = *obj_or_err.get();
  for (const auto &sec : obj.sections()) {
    auto name_or_err = sec.getName();
    if (!name_or_err) continue;
    if (*name_or_err == ".text") {
      auto data_or_err = sec.getContents();
      if (!data_or_err) continue;
      result.text.assign(data_or_err->begin(), data_or_err->end());
      result.text_addr = sec.getAddress();
      break;
    }
  }

  if (result.text.empty()) {
    result.error = "No .text section found in object";
  }
  return result;
}

}  // namespace omill::test
