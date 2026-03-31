#include <gtest/gtest.h>

#include <llvm/ADT/SmallVector.h>
#include <llvm/Support/JSON.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/Program.h>

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <optional>
#include <string>
#include <vector>

namespace {

struct CorpusCase {
  std::string label;
  std::string binary;
  std::string va;
  bool no_abi = false;
};

std::string requireLiftExe() {
#if defined(OMILL_LIFT_EXE_PATH)
  return OMILL_LIFT_EXE_PATH;
#else
  return {};
#endif
}

std::vector<CorpusCase> loadManifest() {
  const char *manifest_path = std::getenv("OMILL_CORPUS_REGRESSION_MANIFEST");
  if (!manifest_path || manifest_path[0] == '\0')
    return {};

  auto buffer = llvm::MemoryBuffer::getFile(manifest_path);
  if (!buffer)
    return {};
  auto parsed = llvm::json::parse((*buffer)->getBuffer());
  if (!parsed)
    return {};
  const auto *root = parsed->getAsObject();
  if (!root)
    return {};
  const auto *cases = root->getArray("cases");
  if (!cases)
    return {};

  std::vector<CorpusCase> loaded;
  for (const auto &item : *cases) {
    const auto *obj = item.getAsObject();
    if (!obj)
      continue;
    auto label = obj->getString("label");
    auto binary = obj->getString("binary");
    auto va = obj->getString("va");
    if (!label || !binary || !va)
      continue;
    CorpusCase c;
    c.label = std::string(*label);
    c.binary = std::string(*binary);
    c.va = std::string(*va);
    if (auto no_abi = obj->getBoolean("no_abi"))
      c.no_abi = *no_abi;
    loaded.push_back(std::move(c));
  }
  return loaded;
}

std::string readFile(const std::filesystem::path &path) {
  std::ifstream in(path, std::ios::binary);
  return std::string((std::istreambuf_iterator<char>(in)),
                     std::istreambuf_iterator<char>());
}

bool eventLogContains(const std::filesystem::path &path, llvm::StringRef kind) {
  std::ifstream in(path);
  std::string line;
  while (std::getline(in, line)) {
    if (line.empty())
      continue;
    auto parsed = llvm::json::parse(line);
    if (!parsed)
      continue;
    const auto *obj = parsed->getAsObject();
    auto event_kind = obj ? obj->getString("kind") : std::optional<llvm::StringRef>{};
    if (event_kind && *event_kind == kind)
      return true;
  }
  return false;
}

TEST(CorpusDevirtualizationRegressionTest, ManifestDrivenSweep) {
  const std::string exe = requireLiftExe();
  if (exe.empty())
    GTEST_SKIP() << "OMILL_LIFT_EXE_PATH not defined";

  const auto cases = loadManifest();
  if (cases.empty())
    GTEST_SKIP() << "OMILL_CORPUS_REGRESSION_MANIFEST not configured";

  const auto tmp = std::filesystem::temp_directory_path();
  for (const auto &test_case : cases) {
    ASSERT_TRUE(std::filesystem::exists(test_case.binary))
        << "Missing corpus binary: " << test_case.binary;

    const auto stem = "omill_corpus_" + test_case.label;
    const auto out_path = (tmp / (stem + ".ll")).string();
    const auto events_path = (tmp / (stem + ".jsonl")).string();

    llvm::SmallVector<llvm::StringRef, 16> argv;
    argv.push_back(exe);
    argv.push_back(test_case.binary);
    argv.push_back("--va");
    argv.push_back(test_case.va);
    argv.push_back("--devirtualize");
    if (test_case.no_abi)
      argv.push_back("--no-abi");
    argv.push_back("-o");
    argv.push_back(out_path);
    argv.push_back("--event-jsonl");
    argv.push_back(events_path);
    argv.push_back("--event-detail");
    argv.push_back("detailed");

    std::string err;
    bool exec_failed = false;
    const int rc = llvm::sys::ExecuteAndWait(exe, argv, std::nullopt, {}, 0, 0,
                                             &err, &exec_failed);
    ASSERT_FALSE(exec_failed) << err;
    ASSERT_EQ(rc, 0) << err;

    const auto output = readFile(out_path);
    EXPECT_FALSE(output.empty()) << test_case.label;
    EXPECT_EQ(output.find("__omill_dispatch_jump"), std::string::npos)
        << test_case.label;
    EXPECT_EQ(output.find("__omill_dispatch_call"), std::string::npos)
        << test_case.label;
    if (test_case.no_abi) {
      EXPECT_EQ(output.find("__remill_read_memory_"), std::string::npos)
          << test_case.label;
      EXPECT_EQ(output.find("__remill_write_memory_"), std::string::npos)
          << test_case.label;
    }

    EXPECT_TRUE(eventLogContains(events_path,
                                 "devirtualization_detection_completed"))
        << test_case.label;
    EXPECT_TRUE(eventLogContains(events_path, "devirtualization_plan_selected"))
        << test_case.label;
    EXPECT_TRUE(
        eventLogContains(events_path, "devirtualization_invariants_verified") ||
        eventLogContains(events_path, "devirtualization_invariants_failed"))
        << test_case.label;
  }
}

}  // namespace
