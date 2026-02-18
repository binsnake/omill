#include "LiftAndOptFixture.h"

#include <llvm/IR/PassInstrumentation.h>
#include <llvm/IR/PassTimingInfo.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/raw_ostream.h>

#include <remill/BC/IntrinsicTable.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/CallGraphAnalysis.h"
#include "omill/Analysis/CallingConventionAnalysis.h"
#include "omill/Analysis/ExceptionInfo.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Omill.h"
#include "omill/Support/MemoryLimit.h"

#include <cstdlib>
#include <optional>

namespace omill::e2e {

// Apply 32 GB memory limit before any test runs (gtest_main provides main()).
static const bool kMemLimitSet = omill::setProcessMemoryLimit(
    32ULL * 1024 * 1024 * 1024);

namespace {

std::optional<bool> parseBoolEnv(const char *name) {
  const char *v = std::getenv(name);
  if (!v || v[0] == '\0') {
    return std::nullopt;
  }
  if ((v[0] == '1' && v[1] == '\0') ||
      (v[0] == 't' && v[1] == '\0') ||
      (v[0] == 'T' && v[1] == '\0')) {
    return true;
  }
  if ((v[0] == '0' && v[1] == '\0') ||
      (v[0] == 'f' && v[1] == '\0') ||
      (v[0] == 'F' && v[1] == '\0')) {
    return false;
  }
  return std::nullopt;
}

void maybeSetBoolFromEnv(const char *name, bool &out) {
  if (auto v = parseBoolEnv(name); v.has_value()) {
    out = *v;
  }
}

void applyPipelineEnvOverrides(PipelineOptions &opts) {
  maybeSetBoolFromEnv("OMILL_OPT_LOWER_INTRINSICS", opts.lower_intrinsics);
  maybeSetBoolFromEnv("OMILL_OPT_OPTIMIZE_STATE", opts.optimize_state);
  maybeSetBoolFromEnv("OMILL_OPT_STOP_AFTER_STATE",
                      opts.stop_after_state_optimization);
  maybeSetBoolFromEnv("OMILL_OPT_LOWER_CONTROL_FLOW", opts.lower_control_flow);
  maybeSetBoolFromEnv("OMILL_OPT_RECOVER_ABI", opts.recover_abi);
  maybeSetBoolFromEnv("OMILL_OPT_DEOBFUSCATE", opts.deobfuscate);
  maybeSetBoolFromEnv("OMILL_OPT_RESOLVE_TARGETS",
                      opts.resolve_indirect_targets);
  maybeSetBoolFromEnv("OMILL_OPT_IPCP", opts.interprocedural_const_prop);
}

void logPipelineOptions(const PipelineOptions &opts) {
  llvm::errs() << "[OPT] lower_intrinsics=" << opts.lower_intrinsics
               << " optimize_state=" << opts.optimize_state
               << " stop_after_state=" << opts.stop_after_state_optimization
               << " lower_control_flow=" << opts.lower_control_flow
               << " recover_abi=" << opts.recover_abi
               << " deobfuscate=" << opts.deobfuscate
               << " resolve_targets=" << opts.resolve_indirect_targets
               << " ipcp=" << opts.interprocedural_const_prop << "\n";
}

}  // namespace

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

llvm::Module *LiftAndOptFixture::liftMultiple(llvm::ArrayRef<uint64_t> addrs) {
  module_ = remill::LoadArchSemantics(arch_.get());
  EXPECT_NE(module_, nullptr) << "Failed to load arch semantics";
  if (!module_) return nullptr;

  remill::TraceLifter lifter(arch_.get(), manager_);
  for (uint64_t addr : addrs) {
    bool ok = lifter.Lift(addr);
    EXPECT_TRUE(ok) << "TraceLifter::Lift() failed for 0x" << std::hex << addr;
  }

  return module_.get();
}

void LiftAndOptFixture::optimize(const PipelineOptions &opts) {
  ASSERT_NE(module_, nullptr) << "Must call lift() before optimize()";

  bool timing = wantTimePasses();
  llvm::PassInstrumentationCallbacks PIC;
  llvm::TimePassesHandler TimingHandler(timing);
  if (timing)
    TimingHandler.registerCallbacks(PIC);

  dumpIR("before");

  llvm::PassBuilder PB(nullptr, llvm::PipelineTuningOptions(), std::nullopt,
                        &PIC);
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
  if (timing)
    TimingHandler.print();
}

void LiftAndOptFixture::optimizeWithMemoryMap(const PipelineOptions &opts,
                                               BinaryMemoryMap memory_map) {
  ASSERT_NE(module_, nullptr) << "Must call lift() before optimizeWithMemoryMap()";

  bool timing = wantTimePasses();
  llvm::PassInstrumentationCallbacks PIC;
  llvm::TimePassesHandler TimingHandler(timing);
  if (timing)
    TimingHandler.registerCallbacks(PIC);

  llvm::PassBuilder PB(nullptr, llvm::PipelineTuningOptions(), std::nullopt,
                        &PIC);
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
  MAM.registerPass([&] { return omill::CallGraphAnalysis(); });
  MAM.registerPass([&] { return omill::LiftedFunctionAnalysis(); });
  MAM.registerPass([&] { return omill::ExceptionInfoAnalysis(); });

  dumpIR("before");

  PipelineOptions requested_opts = opts;
  applyPipelineEnvOverrides(requested_opts);

  // Run the main pipeline once (without ABI recovery, even if requested).
  // Splitting state/control-flow phases can produce invalid intermediate CFGs
  // for complex OLLVM functions (e.g. SHA256), so keep execution cohesive.
  PipelineOptions main_opts = requested_opts;
  main_opts.recover_abi = false;
  logPipelineOptions(main_opts);
  {
    llvm::ModulePassManager MPM;
    omill::buildPipeline(MPM, main_opts);
    MPM.run(*module_, MAM);
  }

  // Keep this snapshot label for compatibility with existing IR dump tooling.
  dumpIR("after_state");
  dumpIR("after");

  // Run ABI recovery as a separate stage so we get a snapshot before and after.
  if (requested_opts.recover_abi) {
    llvm::ModulePassManager MPM;
    omill::buildABIRecoveryPipeline(MPM);
    MPM.run(*module_, MAM);

    dumpIR("after_abi");
  }

  if (timing)
    TimingHandler.print();
}

void LiftAndOptFixture::optimizeWithExceptions(
    const PipelineOptions &opts, ExceptionInfo exc_info,
    BinaryMemoryMap memory_map) {
  ASSERT_NE(module_, nullptr)
      << "Must call lift()/liftMultiple() before optimizeWithExceptions()";

  // Build synthetic DCs in the memory map.
  // Storage must outlive the pipeline run (deque is stable across push_back).
  std::deque<std::vector<uint8_t>> dc_storage;
  exc_info.buildSyntheticDCs(dc_storage, memory_map, exc_info.imageBase());

  bool timing = wantTimePasses();
  llvm::PassInstrumentationCallbacks PIC;
  llvm::TimePassesHandler TimingHandler(timing);
  if (timing)
    TimingHandler.registerCallbacks(PIC);

  llvm::PassBuilder PB(nullptr, llvm::PipelineTuningOptions(), std::nullopt,
                        &PIC);
  llvm::LoopAnalysisManager LAM;
  llvm::FunctionAnalysisManager FAM;
  llvm::CGSCCAnalysisManager CGAM;
  llvm::ModuleAnalysisManager MAM;

  // Register custom analyses BEFORE standard ones.
  MAM.registerPass([&] {
    return omill::BinaryMemoryAnalysis(std::move(memory_map));
  });
  MAM.registerPass([&] {
    return omill::ExceptionInfoAnalysis(std::move(exc_info));
  });

  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

  omill::registerAnalyses(FAM);
  // Register remaining module analyses (skip BinaryMemoryAnalysis and
  // ExceptionInfoAnalysis since we already registered them above).
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });
  MAM.registerPass([&] { return omill::CallGraphAnalysis(); });
  MAM.registerPass([&] { return omill::LiftedFunctionAnalysis(); });

  dumpIR("before");

  {
    llvm::ModulePassManager MPM;
    omill::buildPipeline(MPM, opts);
    MPM.run(*module_, MAM);
  }

  dumpIR("after");
  if (timing)
    TimingHandler.print();
}

bool LiftAndOptFixture::wantTimePasses() {
  const char *env = std::getenv("OMILL_TIME_PASSES");
  return env && env[0] != '\0' && !(env[0] == '0' && env[1] == '\0');
}

std::string LiftAndOptFixture::getDumpDir() {
  const char *env = std::getenv("OMILL_DUMP_IR");
  // Not set or empty → no dumping.
  if (!env || env[0] == '\0')
    return {};
  // "0" disables dumping.
  if (env[0] == '0' && env[1] == '\0')
    return {};
  // "1" means dump to current directory.
  if (env[0] == '1' && env[1] == '\0')
    return ".";
  // Otherwise use the value as a directory path.
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
