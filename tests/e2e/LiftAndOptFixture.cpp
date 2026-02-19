#include "LiftAndOptFixture.h"

#include <llvm/IR/PassInstrumentation.h>
#include <llvm/IR/PassTimingInfo.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/raw_ostream.h>

#if __has_include(<glog/logging.h>)
#include <glog/logging.h>
#define OMILL_E2E_HAS_GLOG 1
#else
#define OMILL_E2E_HAS_GLOG 0
#endif

#include <remill/BC/IntrinsicTable.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/CallGraphAnalysis.h"
#include "omill/Analysis/CallingConventionAnalysis.h"
#include "omill/Analysis/ExceptionInfo.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Omill.h"
#include "omill/Support/MemoryLimit.h"

#include <cstdlib>
#include <memory>
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

bool wantVerboseLogs() {
  if (auto v = parseBoolEnv("OMILL_E2E_VERBOSE"); v.has_value()) {
    return *v;
  }
  return false;
}

void setEnvIfUnset(const char *name, const char *value) {
  const char *cur = std::getenv(name);
  if (cur && cur[0] != '\0')
    return;
#if defined(_WIN32)
  _putenv_s(name, value);
#else
  setenv(name, value, 0);
#endif
}

void configureDefaultE2ELogging() {
  // Some remill logs fire before glog is initialized in gtest_main mode.
  // Initialize once in the fixture before any lifting/arch setup work.
#if OMILL_E2E_HAS_GLOG
  static bool glog_inited = false;
  if (!glog_inited) {
    google::InitGoogleLogging("omill-e2e-tests");
    glog_inited = true;
  }
#endif

  if (wantVerboseLogs()) {
    return;
  }
  // Keep e2e output quiet by default. Users can override by explicitly
  // setting glog env vars or enabling OMILL_E2E_VERBOSE=1.
  setEnvIfUnset("GLOG_minloglevel", "2");
#if OMILL_E2E_HAS_GLOG
  if (FLAGS_minloglevel < 2) {
    FLAGS_minloglevel = 2;
  }
  if (FLAGS_stderrthreshold < 3) {
    FLAGS_stderrthreshold = 3;
  }
#endif
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
  if (!wantVerboseLogs()) {
    return;
  }
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
  configureDefaultE2ELogging();
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

  // Register BinaryMemoryAnalysis BEFORE standard analyses so it takes
  // priority. Keep a stable copy because the analysis may be re-created.
  auto memory_map_holder =
      std::make_shared<BinaryMemoryMap>(std::move(memory_map));
  MAM.registerPass([memory_map_holder] {
    return omill::BinaryMemoryAnalysis(*memory_map_holder);
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

  // Run the full requested pipeline in one pass so pass ordering matches
  // production (including ABI recovery before deobfuscation when enabled).
  logPipelineOptions(requested_opts);
  {
    llvm::ModulePassManager MPM;
    omill::buildPipeline(MPM, requested_opts);
    MPM.run(*module_, MAM);
  }

  // Keep these snapshot labels for compatibility with existing IR dump tooling.
  dumpIR("after_state");
  dumpIR("after");
  if (requested_opts.recover_abi) {
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

  // Register custom analyses BEFORE standard ones. Keep stable copies because
  // analyses may be re-created.
  auto memory_map_holder =
      std::make_shared<BinaryMemoryMap>(std::move(memory_map));
  auto exc_info_holder =
      std::make_shared<ExceptionInfo>(std::move(exc_info));
  MAM.registerPass([memory_map_holder] {
    return omill::BinaryMemoryAnalysis(*memory_map_holder);
  });
  MAM.registerPass([exc_info_holder] {
    return omill::ExceptionInfoAnalysis(*exc_info_holder);
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
