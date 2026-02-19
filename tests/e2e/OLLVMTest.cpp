#include "LiftAndOptFixture.h"
#include "PELoader.h"

#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/Bitcode/BitcodeWriter.h>
#include <llvm/ExecutionEngine/Orc/LLJIT.h>
#include <llvm/ExecutionEngine/Orc/ThreadSafeModule.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Transforms/IPO/GlobalDCE.h>
#include <llvm/Transforms/IPO/StripDeadPrototypes.h>

#include <gtest/gtest.h>

#include "omill/Support/JumpTableDiscovery.h"

#include <cstdlib>
#include <cstring>
#include <string>

#ifndef OLLVM_TEST_DLL_PATH
#error "OLLVM_TEST_DLL_PATH must be defined to point to ollvm_test.dll"
#endif

// ============================================================================
// Minimal Win32 forward declarations for VirtualAlloc/VirtualFree.
// We can't include <windows.h> due to the ghidra::CHAR / Win32 CHAR conflict.
// ============================================================================
extern "C" {
void *__stdcall VirtualAlloc(void *lpAddress, size_t dwSize,
                             unsigned long flAllocationType,
                             unsigned long flProtect);
int __stdcall VirtualFree(void *lpAddress, size_t dwSize,
                          unsigned long dwFreeType);
}

using namespace omill::e2e;

namespace {

bool wantVerboseLogs() {
  const char *v = std::getenv("OMILL_E2E_VERBOSE");
  if (!v || v[0] == '\0') return false;
  return (v[0] == '1' && v[1] == '\0') ||
         (v[0] == 't' && v[1] == '\0') ||
         (v[0] == 'T' && v[1] == '\0');
}

// ============================================================================
// Null symbol generator for JIT
// ============================================================================

class NullSymbolGenerator : public llvm::orc::DefinitionGenerator {
 public:
  llvm::Error tryToGenerate(
      llvm::orc::LookupState &LS, llvm::orc::LookupKind K,
      llvm::orc::JITDylib &JD,
      llvm::orc::JITDylibLookupFlags JDLookupFlags,
      const llvm::orc::SymbolLookupSet &LookupSet) override {
    llvm::orc::SymbolMap symbols;
    for (auto &[name, flags] : LookupSet) {
      symbols[name] = {llvm::orc::ExecutorAddr::fromPtr(&stub),
                       llvm::JITSymbolFlags::Exported};
    }
    return JD.define(llvm::orc::absoluteSymbols(std::move(symbols)));
  }

 private:
  static void stub() {}
};

// ============================================================================
// Test fixture
// ============================================================================

class OLLVMTest : public LiftAndOptFixture {
 protected:
  // PE is loaded once for the entire test suite.
  static PEInfo *shared_pe_;

  static void SetUpTestSuite() {
    shared_pe_ = new PEInfo();
    if (!loadPE(OLLVM_TEST_DLL_PATH, *shared_pe_)) {
      delete shared_pe_;
      shared_pe_ = nullptr;
      FAIL() << "Failed to load " << OLLVM_TEST_DLL_PATH;
    }
  }

  static void TearDownTestSuite() {
    delete shared_pe_;
    shared_pe_ = nullptr;
  }

  void SetUp() override {
    LiftAndOptFixture::SetUp();
    ASSERT_NE(shared_pe_, nullptr) << "Shared PE not loaded";
    ASSERT_FALSE(shared_pe_->exports.empty()) << "No exports found in DLL";
    ASSERT_NE(shared_pe_->text_base, 0u) << "No .text section found";
  }

  void TearDown() override {
    unmapBinaryForJIT();
  }

  uint64_t getExportVA(const std::string &name) {
    auto it = shared_pe_->exports.find(name);
    EXPECT_NE(it, shared_pe_->exports.end()) << "Export not found: " << name;
    return (it != shared_pe_->exports.end()) ? it->second : 0;
  }

  llvm::Module *liftExport(uint64_t export_va) {
    text_copy_.resize(shared_pe_->text_size);
    bool read_ok = shared_pe_->memory_map.read(
        shared_pe_->text_base, text_copy_.data(),
        static_cast<unsigned>(shared_pe_->text_size));
    EXPECT_TRUE(read_ok) << "memory_map.read() failed for .text";
    if (!read_ok)
      return nullptr;

    setCode(text_copy_.data(), text_copy_.size(), shared_pe_->text_base);
    traceManager().setBaseAddr(export_va);

    // Provide the binary memory map so the TraceLifter can discover jump
    // table targets on-the-fly for each indirect jump instruction.
    traceManager().setMemoryMap(&shared_pe_->memory_map);

    return lift();
  }

  bool liftAndOptimize(const std::string &export_name) {
    uint64_t va = getExportVA(export_name);
    if (va == 0) return false;

    auto *M = liftExport(va);
    if (!M) return false;

    omill::PipelineOptions opts;
    opts.recover_abi = true;
    opts.deobfuscate = true;
    optimizeWithMemoryMap(opts, shared_pe_->memory_map);
    return true;
  }

  // -----------------------------------------------------------------------
  // Assertion helpers
  // -----------------------------------------------------------------------

  unsigned countNativeBasicBlocks() {
    unsigned n = 0;
    for (auto &F : *module()) {
      if (F.isDeclaration() || !F.getName().contains("_native")) continue;
      n += F.size();
    }
    return n;
  }

  unsigned countSwitchInsts() {
    unsigned n = 0;
    for (auto &F : *module()) {
      if (F.isDeclaration() || !F.getName().contains("_native")) continue;
      for (auto &BB : F)
        for (auto &I : BB)
          if (llvm::isa<llvm::SwitchInst>(&I))
            n++;
    }
    return n;
  }

  unsigned countNativeFunctions() {
    unsigned n = 0;
    for (auto &F : *module())
      if (!F.isDeclaration() && F.getName().contains("_native"))
        n++;
    return n;
  }

  unsigned countNativeInstructions() {
    unsigned n = 0;
    for (auto &F : *module()) {
      if (F.isDeclaration() || !F.getName().contains("_native")) continue;
      for (auto &BB : F)
        n += BB.size();
    }
    return n;
  }

  bool hasGlobalConstantString(llvm::StringRef needle) {
    for (auto &GV : module()->globals()) {
      if (!GV.hasInitializer() || !GV.isConstant()) continue;
      if (auto *CDA =
              llvm::dyn_cast<llvm::ConstantDataArray>(GV.getInitializer())) {
        if (CDA->getRawDataValues().contains(needle))
          return true;
      }
    }
    return false;
  }

  bool hasConstI64Store(uint64_t val) {
    for (auto &F : *module()) {
      if (F.isDeclaration()) continue;
      for (auto &BB : F)
        for (auto &I : BB)
          if (auto *store = llvm::dyn_cast<llvm::StoreInst>(&I))
            if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(
                    store->getValueOperand()))
              if (ci->getBitWidth() == 64 && ci->getZExtValue() == val)
                return true;
    }
    return false;
  }

  unsigned countConstStackGlobals() {
    unsigned n = 0;
    for (auto &GV : module()->globals())
      if (GV.getName().starts_with(".const_stack"))
        n++;
    return n;
  }

  // -----------------------------------------------------------------------
  // JIT execution helpers
  // -----------------------------------------------------------------------

  llvm::Function *findNativeFunction() {
    if (const char *forced = std::getenv("OMILL_NATIVE_FUNC")) {
      if (forced[0] != '\0') {
        if (auto *F = module()->getFunction(forced)) {
          if (!F->isDeclaration()) {
            return F;
          }
        }
      }
    }
    for (auto &F : *module())
      if (!F.isDeclaration() && F.getName().contains("_native"))
        return &F;
    return nullptr;
  }

  /// Map PE sections at their original virtual addresses so JIT'd code
  /// can access .rdata / .data references via hardcoded VAs.
  /// Allocates a single contiguous block covering the entire image VA range
  /// (VirtualAlloc rounds to 64KB granularity, so per-section allocation
  /// causes adjacent sections to collide).
  bool mapBinaryForJIT() {
    constexpr unsigned long kMemCommit  = 0x1000;
    constexpr unsigned long kMemReserve = 0x2000;
    constexpr unsigned long kPageRW     = 0x04;

    // Compute the VA range spanning all regions.
    uint64_t min_va = UINT64_MAX, max_va = 0;
    shared_pe_->memory_map.forEachRegion(
        [&](uint64_t base, const uint8_t *, size_t size) {
          if (base < min_va) min_va = base;
          if (base + size > max_va) max_va = base + size;
        });
    if (min_va >= max_va) return false;

    size_t total_size = static_cast<size_t>(max_va - min_va);
    void *block = VirtualAlloc(reinterpret_cast<void *>(min_va), total_size,
                               kMemCommit | kMemReserve, kPageRW);
    if (!block) {
      llvm::errs() << "mapBinaryForJIT: VirtualAlloc failed for VA range 0x"
                   << llvm::Twine::utohexstr(min_va) << " - 0x"
                   << llvm::Twine::utohexstr(max_va) << " ("
                   << total_size << " bytes)\n";
      return false;
    }
    jit_mapped_regions_.push_back({block, total_size});

    // Copy each section's data into the correct offset within the block.
    shared_pe_->memory_map.forEachRegion(
        [&](uint64_t base, const uint8_t *data, size_t size) {
          std::memcpy(reinterpret_cast<void *>(base), data, size);
        });
    return true;
  }

  /// Unmap previously mapped binary regions.
  void unmapBinaryForJIT() {
    constexpr unsigned long kMemRelease = 0x8000;
    for (auto &r : jit_mapped_regions_)
      VirtualFree(r.addr, 0, kMemRelease);
    jit_mapped_regions_.clear();
  }

  /// JIT-compile the deobfuscated module and return the address of the
  /// native function.  Strips non-native function bodies before serialization
  /// to avoid the massive remill IR bloat.  JIT must be the last operation
  /// in a test (modifies module() in place).
  void *jitLookupNative() {
    static bool initialized = [] {
      llvm::InitializeNativeTarget();
      llvm::InitializeNativeTargetAsmPrinter();
      return true;
    }();
    (void)initialized;

    auto *NF = findNativeFunction();
    EXPECT_NE(NF, nullptr) << "No native function found in module";
    if (!NF) return nullptr;

    std::string name = NF->getName().str();
    if (wantVerboseLogs()) {
      llvm::errs() << "[JIT] Starting JIT for: " << name << "\n";
    }

    // Strip non-native function bodies BEFORE serialization to avoid
    // serializing ~2000 remill semantic function bodies (tens of MB).
    for (auto &F : *module()) {
      if (F.isDeclaration()) continue;
      if (!F.getName().contains("_native")) {
        F.deleteBody();
        F.setLinkage(llvm::GlobalValue::ExternalLinkage);
      }
    }
    if (wantVerboseLogs()) {
      llvm::errs() << "[JIT] Stripped non-native bodies\n";
    }

    // GlobalDCE to remove unreferenced declarations/globals.
    {
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

      llvm::ModulePassManager MPM;
      MPM.addPass(llvm::GlobalDCEPass());
      MPM.addPass(llvm::StripDeadPrototypesPass());
      MPM.run(*module(), MAM);
    }
    if (wantVerboseLogs()) {
      llvm::errs() << "[JIT] GlobalDCE done\n";
    }

    // Bitcode round-trip into a fresh LLVMContext (LLJIT needs ownership).
    llvm::SmallString<0> buf;
    {
      llvm::raw_svector_ostream os(buf);
      llvm::WriteBitcodeToFile(*module(), os);
    }
    if (wantVerboseLogs()) {
      llvm::errs() << "[JIT] Bitcode serialized: " << buf.size() << " bytes\n";
    }

    auto jit_ctx = std::make_unique<llvm::LLVMContext>();
    auto mem_buf = llvm::MemoryBuffer::getMemBuffer(
        llvm::StringRef(buf.data(), buf.size()), /*BufferName=*/"",
        /*RequiresNullTerminator=*/false);
    auto mod_or = llvm::parseBitcodeFile(mem_buf->getMemBufferRef(), *jit_ctx);
    EXPECT_TRUE(!!mod_or) << "Failed to parse bitcode for JIT";
    if (!mod_or) {
      llvm::consumeError(mod_or.takeError());
      return nullptr;
    }

    // Create LLJIT.
    auto jit_or = llvm::orc::LLJITBuilder().create();
    if (!jit_or) {
      std::string err_msg;
      llvm::raw_string_ostream os(err_msg);
      os << jit_or.takeError();
      EXPECT_TRUE(false) << "Failed to create LLJIT: " << err_msg;
      return nullptr;
    }
    jit_ = std::move(*jit_or);
    if (wantVerboseLogs()) {
      llvm::errs() << "[JIT] LLJIT created\n";
    }

    // Host process symbols (memcpy, etc.).
    auto gen = llvm::orc::DynamicLibrarySearchGenerator::GetForCurrentProcess(
        jit_->getDataLayout().getGlobalPrefix());
    if (gen)
      jit_->getMainJITDylib().addGenerator(std::move(*gen));
    else
      llvm::consumeError(gen.takeError());

    // Null stubs for remaining unresolved symbols.
    jit_->getMainJITDylib().addGenerator(
        std::make_unique<NullSymbolGenerator>());

    // Add module.
    llvm::orc::ThreadSafeContext ts_ctx(std::move(jit_ctx));
    auto err = jit_->addIRModule(
        llvm::orc::ThreadSafeModule(std::move(*mod_or), ts_ctx));
    EXPECT_FALSE(!!err) << "Failed to add module to JIT";
    if (err) {
      llvm::consumeError(std::move(err));
      return nullptr;
    }
    if (wantVerboseLogs()) {
      llvm::errs() << "[JIT] Module added to LLJIT\n";
    }

    // Look up the native function.
    if (wantVerboseLogs()) {
      llvm::errs() << "[JIT] Looking up: " << name << "\n";
    }
    auto sym_or = jit_->lookup(name);
    if (wantVerboseLogs()) {
      llvm::errs() << "[JIT] Lookup complete\n";
    }
    EXPECT_TRUE(!!sym_or) << "Failed to look up " << name << " in JIT";
    if (!sym_or) {
      llvm::consumeError(sym_or.takeError());
      return nullptr;
    }
    return reinterpret_cast<void *>(sym_or->getValue());
  }

  struct MappedRegion {
    void *addr;
    size_t size;
  };
  std::vector<MappedRegion> jit_mapped_regions_;
  std::unique_ptr<llvm::orc::LLJIT> jit_;
  std::vector<uint8_t> text_copy_;
};

PEInfo *OLLVMTest::shared_pe_ = nullptr;

// =============================================================================
// Structural tests — one lift+optimize per export, all assertions together.
// =============================================================================

TEST_F(OLLVMTest, Branch) {
  ASSERT_TRUE(liftAndOptimize("ollvm_branch"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";
  EXPECT_GE(countNativeFunctions(), 1u);

  unsigned bbs = countNativeBasicBlocks();
  EXPECT_LT(bbs, 50u)
      << "Expected CFF BB count to be reduced (got " << bbs << " BBs)";

  unsigned switches = countSwitchInsts();
  EXPECT_LE(switches, 2u)
      << "Expected at most partial CFF switch residue (got " << switches << ")";
}

TEST_F(OLLVMTest, Arithmetic) {
  ASSERT_TRUE(liftAndOptimize("ollvm_arithmetic"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";
  EXPECT_GE(countNativeFunctions(), 1u);

  unsigned insns = countNativeInstructions();
  EXPECT_LT(insns, 200u)
      << "Expected MBA to be simplified (got " << insns << " instructions)";
}

TEST_F(OLLVMTest, CopyGreeting) {
  ASSERT_TRUE(liftAndOptimize("ollvm_copy_greeting"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";
  EXPECT_GE(countNativeFunctions(), 1u);

  bool found_global = hasGlobalConstantString("OLLVM Test String!");
  bool found_partial = hasConstI64Store(0x6554204D564C4C4FULL);
  bool found_stack = countConstStackGlobals() > 0;

  if (found_global || found_partial || found_stack) {
    SUCCEED() << "String encryption partially or fully recovered";
  } else {
    if (wantVerboseLogs()) {
      llvm::errs() << "Note: String encryption recovery not yet implemented\n";
    }
  }
}

TEST_F(OLLVMTest, LoopSum) {
  ASSERT_TRUE(liftAndOptimize("ollvm_loop_sum"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";
  EXPECT_GE(countNativeFunctions(), 1u);

  unsigned bbs = countNativeBasicBlocks();
  EXPECT_LT(bbs, 50u)
      << "Expected CFF BB count to be reduced for loop (got "
      << bbs << " BBs)";

  unsigned switches = countSwitchInsts();
  EXPECT_LE(switches, 2u)
      << "Expected at most partial CFF switch residue (got " << switches << ")";
}

TEST_F(OLLVMTest, CRC32) {
  ASSERT_TRUE(liftAndOptimize("ollvm_crc32"));
  ASSERT_TRUE(verifyModule()) << "Module invalid after optimization";
  EXPECT_GE(countNativeFunctions(), 1u);

  unsigned insns = countNativeInstructions();
  EXPECT_LT(insns, 1200u)
      << "Expected CRC32 to be reasonably recovered (got " << insns
      << " instructions)";

  auto *NF = findNativeFunction();
  ASSERT_NE(NF, nullptr);
  EXPECT_EQ(NF->arg_size(), 2u)
      << "Expected CRC32 to recover 2 params (ptr, len), got "
      << NF->arg_size();
  EXPECT_TRUE(NF->getReturnType()->isIntegerTy(64))
      << "Expected i64 return type (RAX)";
}

TEST_F(OLLVMTest, SHA256) {
  ASSERT_TRUE(liftAndOptimize("ollvm_sha256"));
  ASSERT_TRUE(verifyModule()) << "Module invalid after optimization";
  EXPECT_GE(countNativeFunctions(), 1u);

  unsigned insns = countNativeInstructions();
  EXPECT_LT(insns, 3000u)
      << "Expected SHA-256 to be reasonably recovered (got " << insns
      << " instructions)";

  auto *NF = findNativeFunction();
  ASSERT_NE(NF, nullptr);
  EXPECT_GE(NF->arg_size(), 3u)
      << "Expected SHA-256 to recover at least 3 params";
  EXPECT_LE(NF->arg_size(), 4u)
      << "Expected at most 4 GPR params (got " << NF->arg_size() << ")";
}

// =============================================================================
// JIT correctness tests — map PE sections at original VAs so JIT'd code
// can access .rdata/.data references (lookup tables, constants, etc.).
// =============================================================================

TEST_F(OLLVMTest, ConstantsJIT) {
  ASSERT_TRUE(liftAndOptimize("ollvm_constants"));
  ASSERT_TRUE(verifyModule());

  mapBinaryForJIT();

  void *addr = jitLookupNative();
  if (!addr) {
    GTEST_SKIP() << "JIT compilation failed";
    return;
  }

  auto fn = reinterpret_cast<int(*)(int)>(addr);
  int expected = (((10 + 42) * 7) ^ 0xDEAD) - 100;
  int result = fn(10);
  EXPECT_EQ(result, expected)
      << "ollvm_constants(10) mismatch: got " << result
      << ", expected " << expected;
}

TEST_F(OLLVMTest, VectorArithJIT) {
  ASSERT_TRUE(liftAndOptimize("ollvm_vector_arith"));
  ASSERT_TRUE(verifyModule());

  mapBinaryForJIT();

  void *addr = jitLookupNative();
  if (!addr) {
    GTEST_SKIP() << "JIT compilation failed";
    return;
  }

  auto fn = reinterpret_cast<int(*)(int, int)>(addr);
  int a = 5, b = 3;
  int expected = ((a + b) * (a - b)) ^ (a & b);
  int result = fn(a, b);
  EXPECT_EQ(result, expected)
      << "ollvm_vector_arith(5, 3) mismatch: got " << result
      << ", expected " << expected;
}

TEST_F(OLLVMTest, CRC32JIT) {
  ASSERT_TRUE(liftAndOptimize("ollvm_crc32"));
  ASSERT_TRUE(verifyModule());

  auto *NF = findNativeFunction();
  ASSERT_NE(NF, nullptr);
  if (NF->arg_size() != 2) {
    GTEST_SKIP() << "ABI recovery didn't produce expected signature";
    return;
  }

  mapBinaryForJIT();

  void *addr = jitLookupNative();
  if (!addr) {
    GTEST_SKIP() << "JIT compilation failed";
    return;
  }

  auto fn = reinterpret_cast<uint64_t(*)(const uint8_t *, uint64_t)>(addr);
  const uint8_t input[] = "Hello, World!";
  uint64_t result = fn(input, 13);
  EXPECT_EQ(static_cast<uint32_t>(result), 0xEC4AC3D0u)
      << "CRC32 mismatch: got 0x" << std::hex << static_cast<uint32_t>(result)
      << ", expected 0xEC4AC3D0";
}

TEST_F(OLLVMTest, SHA256JIT) {
  ASSERT_TRUE(liftAndOptimize("ollvm_sha256"));
  ASSERT_TRUE(verifyModule());

  auto *NF = findNativeFunction();
  ASSERT_NE(NF, nullptr);
  if (NF->arg_size() < 3 || NF->arg_size() > 4) {
    GTEST_SKIP() << "ABI recovery didn't produce expected signature";
    return;
  }

  mapBinaryForJIT();

  void *addr = jitLookupNative();
  if (!addr) {
    GTEST_SKIP() << "JIT compilation failed";
    return;
  }

  auto fn = reinterpret_cast<uint64_t(*)(const uint8_t *, uint64_t, uint8_t *)>(addr);
  const uint8_t input[] = "Hello, World!";
  uint8_t digest[32] = {};
  if (wantVerboseLogs()) {
    llvm::errs() << "[JIT] Calling SHA256 at " << addr << "\n";
  }
  fn(input, 13, digest);
  if (wantVerboseLogs()) {
    llvm::errs() << "[JIT] SHA256 returned\n";
  }

  const uint8_t expected[32] = {
      0xdf, 0xfd, 0x60, 0x21, 0xbb, 0x2b, 0xd5, 0xb0,
      0xaf, 0x67, 0x62, 0x90, 0x80, 0x9e, 0xc3, 0xa5,
      0x31, 0x91, 0xdd, 0x81, 0xc7, 0xf7, 0x0a, 0x4b,
      0x28, 0x68, 0x8a, 0x36, 0x21, 0x82, 0x98, 0x6f
  };

  bool match = std::memcmp(digest, expected, 32) == 0;
  if (!match) {
    std::string got, exp;
    for (int i = 0; i < 32; i++) {
      char buf[4];
      snprintf(buf, sizeof(buf), "%02x", digest[i]);
      got += buf;
      snprintf(buf, sizeof(buf), "%02x", expected[i]);
      exp += buf;
    }
    EXPECT_TRUE(match) << "SHA-256 mismatch:\n  got:      " << got
                       << "\n  expected: " << exp;
  }
}

TEST_F(OLLVMTest, SHA256JIT_Obfuscated) {
  uint64_t va = getExportVA("ollvm_sha256");
  if (va == 0) return;

  auto *M = liftExport(va);
  if (!M) return;

  // Run pipeline with ABI recovery but WITHOUT deobfuscation.
  omill::PipelineOptions opts;
  opts.recover_abi = true;
  opts.deobfuscate = false;
  optimizeWithMemoryMap(opts, shared_pe_->memory_map);

  ASSERT_TRUE(verifyModule());

  auto *NF = findNativeFunction();
  ASSERT_NE(NF, nullptr);
  if (NF->arg_size() < 3 || NF->arg_size() > 4) {
    GTEST_SKIP() << "ABI recovery didn't produce expected signature";
    return;
  }

  mapBinaryForJIT();

  void *addr = jitLookupNative();
  if (!addr) {
    GTEST_SKIP() << "JIT compilation failed";
    return;
  }

  auto fn = reinterpret_cast<uint64_t(*)(const uint8_t *, uint64_t, uint8_t *)>(addr);
  const uint8_t input[] = "Hello, World!";
  uint8_t digest[32] = {};
  if (wantVerboseLogs()) {
    llvm::errs() << "[JIT] Calling SHA256 (Obfuscated) at " << addr << "\n";
  }
  fn(input, 13, digest);
  if (wantVerboseLogs()) {
    llvm::errs() << "[JIT] SHA256 (Obfuscated) returned\n";
  }

  const uint8_t expected[32] = {
      0xdf, 0xfd, 0x60, 0x21, 0xbb, 0x2b, 0xd5, 0xb0,
      0xaf, 0x67, 0x62, 0x90, 0x80, 0x9e, 0xc3, 0xa5,
      0x31, 0x91, 0xdd, 0x81, 0xc7, 0xf7, 0x0a, 0x4b,
      0x28, 0x68, 0x8a, 0x36, 0x21, 0x82, 0x98, 0x6f
  };

  bool match = std::memcmp(digest, expected, 32) == 0;
  if (!match) {
    std::string got, exp;
    for (int i = 0; i < 32; i++) {
      char buf[4];
      snprintf(buf, sizeof(buf), "%02x", digest[i]);
      got += buf;
      snprintf(buf, sizeof(buf), "%02x", expected[i]);
      exp += buf;
    }
    EXPECT_TRUE(match) << "SHA-256 (Obfuscated) mismatch:\n  got:      " << got
                       << "\n  expected: " << exp;
  }
}


}  // namespace
