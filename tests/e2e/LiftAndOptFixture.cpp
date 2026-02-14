#include "LiftAndOptFixture.h"

#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/raw_ostream.h>

#include <remill/BC/IntrinsicTable.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/CallingConventionAnalysis.h"

#include <cstdlib>

namespace omill::e2e {

void LiftAndOptFixture::SetUp() {
  arch_ = remill::Arch::Get(ctx_, remill::kOSWindows, remill::kArchAMD64_AVX);
  ASSERT_NE(arch_, nullptr) << "Failed to create AMD64 arch";
}

void LiftAndOptFixture::setCode(const uint8_t *data, size_t size,
                                 uint64_t base) {
  manager_.setCode(data, size, base);
}

llvm::Module *LiftAndOptFixture::lift() {
  // Load the semantics module for this architecture.
  module_ = remill::LoadArchSemantics(arch_.get());
  EXPECT_NE(module_, nullptr) << "Failed to load arch semantics";
  if (!module_) return nullptr;

  // Lift traces starting from the base address.
  remill::TraceLifter lifter(arch_.get(), manager_);
  bool ok = lifter.Lift(manager_.baseAddr());
  EXPECT_TRUE(ok) << "TraceLifter::Lift() failed";

  return module_.get();
}

void LiftAndOptFixture::optimize(const PipelineOptions &opts) {
  ASSERT_NE(module_, nullptr) << "Must call lift() before optimize()";

  dumpIR("before");

  llvm::PassBuilder PB;
  llvm::LoopAnalysisManager LAM;
  llvm::FunctionAnalysisManager FAM;
  llvm::CGSCCAnalysisManager CGAM;
  llvm::ModuleAnalysisManager MAM;

  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

  // Register omill-specific analyses.
  omill::registerAnalyses(FAM);
  omill::registerModuleAnalyses(MAM);

  llvm::ModulePassManager MPM;
  omill::buildPipeline(MPM, opts);
  MPM.run(*module_, MAM);

  dumpIR("after");
}

void LiftAndOptFixture::optimizeWithMemoryMap(const PipelineOptions &opts,
                                               BinaryMemoryMap memory_map) {
  ASSERT_NE(module_, nullptr) << "Must call lift() before optimizeWithMemoryMap()";

  llvm::PassBuilder PB;
  llvm::LoopAnalysisManager LAM;
  llvm::FunctionAnalysisManager FAM;
  llvm::CGSCCAnalysisManager CGAM;
  llvm::ModuleAnalysisManager MAM;

  // Register BinaryMemoryAnalysis BEFORE standard analyses so it takes priority.
  MAM.registerPass([&] {
    return omill::BinaryMemoryAnalysis(std::move(memory_map));
  });

  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

  omill::registerAnalyses(FAM);
  // Note: don't call registerModuleAnalyses() — we already registered
  // BinaryMemoryAnalysis with our custom map above. Register the rest manually.
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  dumpIR("before");

  // Run the main pipeline (without ABI recovery, even if requested).
  PipelineOptions main_opts = opts;
  main_opts.recover_abi = false;
  {
    llvm::ModulePassManager MPM;
    omill::buildPipeline(MPM, main_opts);
    MPM.run(*module_, MAM);
  }

  dumpIR("after");

  // Run ABI recovery as a separate stage so we get a snapshot before and after.
  if (opts.recover_abi) {
    llvm::ModulePassManager MPM;
    omill::buildABIRecoveryPipeline(MPM);
    MPM.run(*module_, MAM);

    dumpIR("after_abi");
  }
}

std::string LiftAndOptFixture::getDumpDir() {
  const char *env = std::getenv("OMILL_DUMP_IR");
  // Default to dumping in the current directory.
  if (!env || env[0] == '\0' || (env[0] == '1' && env[1] == '\0'))
    return ".";
  // "0" disables dumping.
  if (env[0] == '0' && env[1] == '\0')
    return {};
  return env;
}

void LiftAndOptFixture::dumpIR(llvm::StringRef tag) {
  std::string dir = getDumpDir();
  if (dir.empty() || !module_)
    return;

  const auto *info = ::testing::UnitTest::GetInstance()->current_test_info();
  std::string filename =
      dir + "/" + info->test_suite_name() + "_" + info->name() + "_" +
      tag.str() + ".ll";

  std::error_code ec;
  llvm::raw_fd_ostream os(filename, ec, llvm::sys::fs::OF_Text);
  if (ec) {
    llvm::errs() << "dumpIR: cannot open " << filename << ": "
                 << ec.message() << "\n";
    return;
  }
  module_->print(os, nullptr);
  llvm::errs() << "dumpIR: wrote " << filename << "\n";
}

bool LiftAndOptFixture::verifyModule() {
  if (!module_) return false;
  return !llvm::verifyModule(*module_, &llvm::errs());
}

}  // namespace omill::e2e
