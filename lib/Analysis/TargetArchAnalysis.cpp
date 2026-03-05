#include "omill/Analysis/TargetArchAnalysis.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Metadata.h>
#include <llvm/IR/Module.h>

namespace omill {

llvm::AnalysisKey TargetArchAnalysis::Key;

TargetArchAnalysis::Result TargetArchAnalysis::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &) {
  TargetArch arch = TargetArch::kX86_64;
  std::string os = "windows";

  if (auto *md = M.getModuleFlag("omill.target_arch")) {
    if (auto *ci = llvm::mdconst::dyn_extract<llvm::ConstantInt>(md)) {
      arch = static_cast<TargetArch>(ci->getZExtValue());
    }
  }
  if (auto *md = M.getModuleFlag("omill.target_os")) {
    if (auto *mds = llvm::dyn_cast<llvm::MDString>(md)) {
      os = mds->getString().str();
    }
  }

  return ArchABI::get(arch, os);
}

void setTargetArchMetadata(llvm::Module &M, TargetArch arch,
                           llvm::StringRef os) {
  auto &ctx = M.getContext();
  // Use Override so that Linker::linkModules silently keeps the first value
  // when merging the late-discovery module (which carries the same flags)
  // into the main module.  Error behavior would abort on duplicate keys.
  if (!M.getModuleFlag("omill.target_arch"))
    M.addModuleFlag(llvm::Module::Override, "omill.target_arch",
                    static_cast<uint32_t>(arch));
  if (!M.getModuleFlag("omill.target_os"))
    M.addModuleFlag(llvm::Module::Override, "omill.target_os",
                    llvm::MDString::get(ctx, os));
}

}  // namespace omill
