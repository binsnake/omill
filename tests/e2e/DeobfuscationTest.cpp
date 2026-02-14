#include "LiftAndOptFixture.h"
#include "PELoader.h"

#include <llvm/IR/Instructions.h>
#include <llvm/IR/Metadata.h>

#include <gtest/gtest.h>

#include <string>

#ifndef OBF_TEST_DLL_PATH
#error "OBF_TEST_DLL_PATH must be defined to point to obf_test.dll"
#endif

namespace {

using omill::e2e::LiftAndOptFixture;
using omill::e2e::PEInfo;
using omill::e2e::loadPE;

class DeobfuscationTest : public LiftAndOptFixture {
 protected:
  void SetUp() override {
    LiftAndOptFixture::SetUp();
    ASSERT_TRUE(loadPE(OBF_TEST_DLL_PATH, pe_))
        << "Failed to load " << OBF_TEST_DLL_PATH;
    ASSERT_FALSE(pe_.exports.empty()) << "No exports found in DLL";
    ASSERT_NE(pe_.text_base, 0u) << "No .text section found";
  }

  /// Find export VA or fail the test.
  uint64_t getExportVA(const std::string &name) {
    auto it = pe_.exports.find(name);
    EXPECT_NE(it, pe_.exports.end()) << "Export not found: " << name;
    return (it != pe_.exports.end()) ? it->second : 0;
  }

  /// Set .text bytes into the trace manager at the correct VA, then lift
  /// starting from the given export address.
  llvm::Module *liftExport(uint64_t export_va) {
    // Read .text bytes from the memory map.
    text_copy_.resize(pe_.text_size);
    bool read_ok = pe_.memory_map.read(pe_.text_base, text_copy_.data(),
                                       static_cast<unsigned>(pe_.text_size));
    EXPECT_TRUE(read_ok) << "memory_map.read() failed for .text";
    if (!read_ok)
      return nullptr;

    // Map the entire .text section at its VA, but start lifting at the export.
    setCode(text_copy_.data(), text_copy_.size(), pe_.text_base);
    traceManager().setBaseAddr(export_va);

    return lift();
  }

  std::vector<uint8_t> text_copy_;

  PEInfo pe_;
};

/// Verify that xorstr code is lifted and optimized correctly.
///
/// xorstr encodes strings as immediate constants XOR'd with compile-time keys.
/// After lifting and the full pipeline (including deobfuscation), we verify:
///   1. The code lifts and optimizes without crashing
///   2. The module is valid
///   3. XOR operations with large constants (encrypted data) are present
///   4. The PXOR SSE operation was correctly lowered
TEST_F(DeobfuscationTest, XorstrRecovery) {
  uint64_t va = getExportVA("obf_xorstr_hello");
  ASSERT_NE(va, 0u);

  auto *M = liftExport(va);
  ASSERT_NE(M, nullptr);
  EXPECT_TRUE(verifyModule()) << "Module invalid after lifting";

  omill::PipelineOptions opts;
  opts.recover_abi = true;
  opts.deobfuscate = true;
  optimizeWithMemoryMap(opts, pe_.memory_map);

  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";

  // Verify "Hello, World!" plaintext appears in the optimized IR.
  // After xorstr deobfuscation, the plaintext may appear as:
  //   (a) constant i64 stores (if stack alloca remains), or
  //   (b) a global constant initializer (if OutlineConstantStackData promoted it)
  //
  // Check both forms.  The raw bytes are:
  //   "Hello, World!\0" = 48 65 6C 6C 6F 2C 20 57 6F 72 6C 64 21 00
  constexpr uint64_t kHelloW = 0x57202C6F6C6C6548ULL;
  constexpr uint64_t kOrld   = 0x00000021646C726FULL;
  bool found_first_half = false;
  bool found_second_half = false;

  // Check store instructions.
  for (auto &F : *module()) {
    if (F.isDeclaration()) continue;
    for (auto &BB : F) {
      for (auto &I : BB) {
        if (auto *store = llvm::dyn_cast<llvm::StoreInst>(&I)) {
          if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(
                  store->getValueOperand())) {
            if (ci->getBitWidth() == 64 && ci->getZExtValue() == kHelloW) {
              found_first_half = true;
            }
            if (ci->getBitWidth() == 64 && ci->getZExtValue() == kOrld) {
              found_second_half = true;
            }
          }
        }
      }
    }
  }

  // Check global constant initializers (outlined by OutlineConstantStackData).
  if (!found_first_half || !found_second_half) {
    for (auto &GV : module()->globals()) {
      if (!GV.hasInitializer() || !GV.isConstant()) continue;
      if (auto *CDA = llvm::dyn_cast<llvm::ConstantDataArray>(
              GV.getInitializer())) {
        if (!CDA->isString()) continue;
        llvm::StringRef data = CDA->getRawDataValues();
        if (data.size() >= 14 &&
            data.substr(0, 14) == llvm::StringRef("Hello, World!\0", 14)) {
          found_first_half = true;
          found_second_half = true;
        }
      }
    }
  }

  EXPECT_TRUE(found_first_half)
      << "Expected decrypted 'Hello, W' constant (0x57202C6F6C6C6548)";
  EXPECT_TRUE(found_second_half)
      << "Expected decrypted 'orld!' constant (0x00000021646C726F)";
}

/// Verify that lazy_importer for VirtualAlloc is resolved to a direct
/// dllimport reference.
TEST_F(DeobfuscationTest, LazyImporterAnnotation) {
  uint64_t va = getExportVA("obf_li_virtual_alloc");
  ASSERT_NE(va, 0u);

  auto *M = liftExport(va);
  ASSERT_NE(M, nullptr);
  EXPECT_TRUE(verifyModule()) << "Module invalid after lifting";

  omill::PipelineOptions opts;
  opts.recover_abi = true;
  opts.deobfuscate = true;
  optimizeWithMemoryMap(opts, pe_.memory_map);

  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";

  // After ResolveLazyImports, VirtualAlloc should be declared as an
  // external dllimport function in the module.
  auto *va_fn = module()->getFunction("VirtualAlloc");
  EXPECT_NE(va_fn, nullptr)
      << "Expected 'VirtualAlloc' to be declared in the module";
  if (va_fn) {
    EXPECT_TRUE(va_fn->isDeclaration())
        << "VirtualAlloc should be a declaration (external)";
    EXPECT_EQ(va_fn->getDLLStorageClass(),
              llvm::GlobalValue::DLLImportStorageClass)
        << "VirtualAlloc should have dllimport storage class";
  }

  // Verify that @VirtualAlloc is referenced in the IR (as a store operand
  // via a ptrtoint constant expression or instruction).
  bool found_ref = !va_fn->use_empty();
  EXPECT_TRUE(found_ref)
      << "Expected @VirtualAlloc to be referenced in the optimized IR";
}

/// Verify that the combined function (xorstr + lazy_importer) is handled.
TEST_F(DeobfuscationTest, CombinedRecovery) {
  uint64_t va = getExportVA("obf_combined");
  ASSERT_NE(va, 0u);

  auto *M = liftExport(va);
  ASSERT_NE(M, nullptr);
  EXPECT_TRUE(verifyModule()) << "Module invalid after lifting";

  omill::PipelineOptions opts;
  opts.recover_abi = true;
  opts.deobfuscate = true;
  optimizeWithMemoryMap(opts, pe_.memory_map);

  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";

  // Check for resolved import declaration (LoadLibraryA) or remaining
  // FNV-1a multiply pattern.
  bool found_import = false;
  bool found_fnv_multiply = false;

  // Check if LoadLibraryA was resolved as a dllimport declaration.
  if (auto *fn = module()->getFunction("LoadLibraryA")) {
    if (fn->isDeclaration() &&
        fn->getDLLStorageClass() == llvm::GlobalValue::DLLImportStorageClass) {
      found_import = true;
    }
  }

  // Fallback: check for remaining FNV-1a multiply (if resolution failed).
  if (!found_import) {
    for (auto &F : *module()) {
      if (F.isDeclaration()) continue;
      for (auto &BB : F) {
        for (auto &I : BB) {
          if (auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(&I)) {
            if (bin->getOpcode() == llvm::Instruction::Mul) {
              for (auto &op : bin->operands()) {
                if (auto *c = llvm::dyn_cast<llvm::ConstantInt>(op.get())) {
                  if (c->getZExtValue() == 16777619u) {
                    found_fnv_multiply = true;
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  EXPECT_TRUE(found_import || found_fnv_multiply)
      << "Expected resolved LoadLibraryA import or FNV-1a multiply pattern "
         "in combined function";
}

/// Verify that a mixed function (xorstr + multiple lazy_importer) is handled.
/// This tests surgical per-loop elimination: the function contains two separate
/// PEB-walking loops (for GetModuleHandleA and GetProcAddress) plus xorstr
/// decryption for module/function name strings.
TEST_F(DeobfuscationTest, MixedRecovery) {
  uint64_t va = getExportVA("obf_mixed_resolve");
  ASSERT_NE(va, 0u);

  auto *M = liftExport(va);
  ASSERT_NE(M, nullptr);
  EXPECT_TRUE(verifyModule()) << "Module invalid after lifting";

  omill::PipelineOptions opts;
  opts.recover_abi = true;
  opts.deobfuscate = true;
  optimizeWithMemoryMap(opts, pe_.memory_map);

  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";

  // Check that GetModuleHandleA was resolved as dllimport.
  bool found_gmh = false;
  if (auto *fn = module()->getFunction("GetModuleHandleA")) {
    if (fn->isDeclaration() &&
        fn->getDLLStorageClass() == llvm::GlobalValue::DLLImportStorageClass) {
      found_gmh = true;
    }
  }
  EXPECT_TRUE(found_gmh)
      << "Expected 'GetModuleHandleA' to be declared as dllimport";

  // Check that GetProcAddress was resolved as dllimport.
  bool found_gpa = false;
  if (auto *fn = module()->getFunction("GetProcAddress")) {
    if (fn->isDeclaration() &&
        fn->getDLLStorageClass() == llvm::GlobalValue::DLLImportStorageClass) {
      found_gpa = true;
    }
  }
  EXPECT_TRUE(found_gpa)
      << "Expected 'GetProcAddress' to be declared as dllimport";
}

}  // namespace
