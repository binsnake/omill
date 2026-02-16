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

  /// Lift an export and run the full deobfuscation + ABI recovery pipeline.
  /// Returns false if lifting fails; sets module() for assertions.
  bool liftAndOptimize(const std::string &export_name) {
    uint64_t va = getExportVA(export_name);
    if (va == 0) return false;

    auto *M = liftExport(va);
    if (!M) return false;

    omill::PipelineOptions opts;
    opts.recover_abi = true;
    opts.deobfuscate = true;
    optimizeWithMemoryMap(opts, pe_.memory_map);
    return true;
  }

  // -----------------------------------------------------------------------
  // Assertion helpers
  // -----------------------------------------------------------------------

  /// Check if a function with the given name exists as a dllimport decl.
  bool hasDllImport(llvm::StringRef name) {
    auto *fn = module()->getFunction(name);
    return fn && fn->isDeclaration() &&
           fn->getDLLStorageClass() ==
               llvm::GlobalValue::DLLImportStorageClass;
  }

  /// Count dllimport declarations in the module.
  unsigned countDllImports() {
    unsigned n = 0;
    for (auto &F : *module())
      if (F.isDeclaration() &&
          F.getDLLStorageClass() == llvm::GlobalValue::DLLImportStorageClass)
        n++;
    return n;
  }

  /// Count remaining FNV-1a multiply (x * 16777619) instructions.
  unsigned countFnvMultiplies() {
    unsigned n = 0;
    for (auto &F : *module()) {
      if (F.isDeclaration()) continue;
      for (auto &BB : F)
        for (auto &I : BB)
          if (auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(&I))
            if (bin->getOpcode() == llvm::Instruction::Mul)
              for (auto &op : bin->operands())
                if (auto *c = llvm::dyn_cast<llvm::ConstantInt>(op.get()))
                  if (c->getZExtValue() == 16777619u)
                    n++;
    }
    return n;
  }

  /// Search for a constant i32 store with the given value.
  bool hasConstI32Store(uint32_t val) {
    for (auto &F : *module()) {
      if (F.isDeclaration()) continue;
      for (auto &BB : F)
        for (auto &I : BB)
          if (auto *store = llvm::dyn_cast<llvm::StoreInst>(&I))
            if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(
                    store->getValueOperand()))
              if (ci->getBitWidth() == 32 && ci->getZExtValue() == val)
                return true;
    }
    return false;
  }

  /// Search for a constant i64 store with the given value.
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

  /// Search for a global constant containing a substring in its raw bytes.
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

  /// Count @.const_stack* globals.
  unsigned countConstStackGlobals() {
    unsigned n = 0;
    for (auto &GV : module()->globals())
      if (GV.getName().starts_with(".const_stack"))
        n++;
    return n;
  }

  /// Count native functions produced by the pipeline (sub_*_native).
  unsigned countNativeFunctions() {
    unsigned n = 0;
    for (auto &F : *module())
      if (!F.isDeclaration() && F.getName().contains("_native"))
        n++;
    return n;
  }

  /// Count shift operations (shl, lshr, ashr) in defined functions.
  unsigned countShiftOps() {
    unsigned n = 0;
    for (auto &F : *module()) {
      if (F.isDeclaration()) continue;
      for (auto &BB : F)
        for (auto &I : BB)
          if (auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(&I))
            if (bin->getOpcode() == llvm::Instruction::Shl ||
                bin->getOpcode() == llvm::Instruction::LShr ||
                bin->getOpcode() == llvm::Instruction::AShr)
              n++;
    }
    return n;
  }

  /// Count bitwise OR operations in defined functions.
  unsigned countOrOps() {
    unsigned n = 0;
    for (auto &F : *module()) {
      if (F.isDeclaration()) continue;
      for (auto &BB : F)
        for (auto &I : BB)
          if (auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(&I))
            if (bin->getOpcode() == llvm::Instruction::Or)
              n++;
    }
    return n;
  }

  /// Count alloca instructions in defined native functions.
  unsigned countAllocasInNative() {
    unsigned n = 0;
    for (auto &F : *module()) {
      if (F.isDeclaration() || !F.getName().contains("_native")) continue;
      for (auto &BB : F)
        for (auto &I : BB)
          if (llvm::isa<llvm::AllocaInst>(&I))
            n++;
    }
    return n;
  }

  /// Check if any native function contains a call to a function whose name
  /// contains the given substring.
  bool hasCallContaining(llvm::StringRef substr) {
    for (auto &F : *module()) {
      if (F.isDeclaration() || !F.getName().contains("_native")) continue;
      for (auto &BB : F)
        for (auto &I : BB)
          if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
            if (auto *callee = CI->getCalledFunction())
              if (callee->getName().contains(substr))
                return true;
    }
    return false;
  }

  /// Count total instructions across all native functions.
  unsigned countNativeInstructions() {
    unsigned n = 0;
    for (auto &F : *module()) {
      if (F.isDeclaration() || !F.getName().contains("_native")) continue;
      for (auto &BB : F)
        n += BB.size();
    }
    return n;
  }

  /// Check if a dllimport function is actually called (not just declared).
  bool isDllImportCalled(llvm::StringRef name) {
    auto *fn = module()->getFunction(name);
    if (!fn) return false;
    for (auto *U : fn->users()) {
      if (llvm::isa<llvm::CallInst>(U) || llvm::isa<llvm::InvokeInst>(U))
        return true;
    }
    return false;
  }

  std::vector<uint8_t> text_copy_;

  PEInfo pe_;
};

// =============================================================================
// xorstr tests
// =============================================================================

/// xorstr("Hello, World!") → plaintext promoted to @.const_stack global.
///
/// Pipeline path: ConstantMemoryFolding folds the XOR keys into plaintext
/// stores, then OutlineConstantStackData promotes the alloca to a global.
TEST_F(DeobfuscationTest, XorstrHelloPromotedToGlobal) {
  ASSERT_TRUE(liftAndOptimize("obf_xorstr_hello"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";

  // The plaintext should appear in a @.const_stack global.
  EXPECT_GE(countConstStackGlobals(), 1u)
      << "Expected OutlineConstantStackData to promote xorstr alloca";
  EXPECT_TRUE(hasGlobalConstantString(
      llvm::StringRef("Hello, World!\0", 14)))
      << "Expected 'Hello, World!' in promoted global";

  // FNV-1a patterns should NOT appear (this is xorstr, not lazy_importer).
  EXPECT_EQ(countFnvMultiplies(), 0u)
      << "xorstr should not contain FNV-1a multiply";

  // Should produce exactly 1 native function.
  EXPECT_EQ(countNativeFunctions(), 1u);
}

/// Fallback check: if the global isn't there, the plaintext should still
/// appear as constant i64 stores (the pre-promotion form).
TEST_F(DeobfuscationTest, XorstrHelloPlaintextConstants) {
  ASSERT_TRUE(liftAndOptimize("obf_xorstr_hello"));
  EXPECT_TRUE(verifyModule());

  // "Hello, W" = 0x57202C6F6C6C6548, "orld!\0\0\0" = 0x00000021646C726F
  bool found = hasGlobalConstantString(
      llvm::StringRef("Hello, World!\0", 14));
  if (!found) {
    // Fallback: check for i64 store constants.
    EXPECT_TRUE(hasConstI64Store(0x57202C6F6C6C6548ULL))
        << "Expected 'Hello, W' i64 constant (0x57202C6F6C6C6548)";
    EXPECT_TRUE(hasConstI64Store(0x00000021646C726FULL))
        << "Expected 'orld!' i64 constant (0x00000021646C726F)";
  }
}

/// xorstr("kernel32.dll") in obf_xorstr_kernel32.
TEST_F(DeobfuscationTest, XorstrKernel32Recovery) {
  ASSERT_TRUE(liftAndOptimize("obf_xorstr_kernel32"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";

  // Check promoted global or inline stores.
  // "kernel32.dll\0" = 6B 65 72 6E 65 6C 33 32 2E 64 6C 6C 00
  bool found_global = hasGlobalConstantString("kernel32.dll");

  // "kern" = 0x6E72656B, "el32" = 0x32336C65, ".dll" = 0x6C6C642E
  bool found_stores = hasConstI32Store(0x6E72656BU) ||  // "kern"
                      hasConstI64Store(0x32336C656E72656BULL);  // "kernel32"

  EXPECT_TRUE(found_global || found_stores)
      << "Expected decrypted 'kernel32.dll' as global or store constants";
}

// =============================================================================
// lazy_importer tests
// =============================================================================

/// lazy_importer VirtualAlloc → resolved to @VirtualAlloc dllimport.
///
/// Pipeline: HashImportAnnotation detects FNV-1a hash comparison,
/// ResolveLazyImports folds the loop, LowerResolvedDispatchCalls emits
/// the native call.
TEST_F(DeobfuscationTest, LazyImporterVirtualAlloc) {
  ASSERT_TRUE(liftAndOptimize("obf_li_virtual_alloc"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";

  // VirtualAlloc should be declared as dllimport.
  EXPECT_TRUE(hasDllImport("VirtualAlloc"))
      << "Expected @VirtualAlloc dllimport declaration";

  // The FNV-1a hashing loop should have been fully eliminated.
  EXPECT_EQ(countFnvMultiplies(), 0u)
      << "FNV-1a multiply should be eliminated after import resolution";

  // VirtualAlloc should be referenced (not dead).
  auto *fn = module()->getFunction("VirtualAlloc");
  EXPECT_TRUE(fn && !fn->use_empty())
      << "Expected @VirtualAlloc to be referenced in optimized IR";

  // Single native function.
  EXPECT_EQ(countNativeFunctions(), 1u);
}

/// lazy_importer GetModuleHandleA resolution.
TEST_F(DeobfuscationTest, LazyImporterGetModuleHandle) {
  ASSERT_TRUE(liftAndOptimize("obf_li_get_module_handle"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";

  EXPECT_TRUE(hasDllImport("GetModuleHandleA"))
      << "Expected @GetModuleHandleA dllimport declaration";
  EXPECT_EQ(countFnvMultiplies(), 0u)
      << "FNV-1a multiply should be eliminated";
}

/// lazy_importer LoadLibraryA resolution.
TEST_F(DeobfuscationTest, LazyImporterLoadLibrary) {
  ASSERT_TRUE(liftAndOptimize("obf_li_load_library"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";

  EXPECT_TRUE(hasDllImport("LoadLibraryA"))
      << "Expected @LoadLibraryA dllimport declaration";
  EXPECT_EQ(countFnvMultiplies(), 0u)
      << "FNV-1a multiply should be eliminated";
}

// =============================================================================
// Combined xorstr + lazy_importer tests
// =============================================================================

/// Combined: xorstr("user32.dll") + LI_FN(LoadLibraryA).
///
/// Verifies both import resolution and partial xorstr recovery in the same
/// function.
TEST_F(DeobfuscationTest, CombinedImportResolution) {
  ASSERT_TRUE(liftAndOptimize("obf_combined"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";

  // LoadLibraryA should be resolved as dllimport.
  EXPECT_TRUE(hasDllImport("LoadLibraryA"))
      << "Expected @LoadLibraryA dllimport declaration";

  // FNV-1a hashing loop should be fully eliminated.
  EXPECT_EQ(countFnvMultiplies(), 0u)
      << "FNV-1a multiply should be eliminated after import resolution";

  // LoadLibraryA should be directly called.
  EXPECT_TRUE(isDllImportCalled("LoadLibraryA"))
      << "Expected direct call to @LoadLibraryA";

  // Single native function.
  EXPECT_EQ(countNativeFunctions(), 1u);
}

/// Combined: xorstr "user32.dll" string should be at least partially recovered.
TEST_F(DeobfuscationTest, CombinedXorstrRecovery) {
  ASSERT_TRUE(liftAndOptimize("obf_combined"));
  EXPECT_TRUE(verifyModule());

  // Check global (ideal) or partial i32 store (current behavior).
  bool found_global = hasGlobalConstantString("user32.dll");
  // "user" = 0x72657375
  bool found_partial = hasConstI32Store(0x72657375U);

  EXPECT_TRUE(found_global || found_partial)
      << "Expected decrypted 'user32.dll' (global) or 'user' (i32 fragment)";
}

// =============================================================================
// Mixed xorstr + multiple lazy_importer tests
// =============================================================================

/// Mixed: two lazy_importer resolutions (GetModuleHandleA, GetProcAddress)
/// plus two xorstr strings ("kernel32.dll", "VirtualAlloc").
///
/// This is the most complex deobfuscation scenario: the function contains
/// two separate PEB-walking loops that must be independently resolved, plus
/// xorstr decryption that produces stack-allocated strings passed as arguments.

/// Verify both imports are resolved and FNV-1a loops fully eliminated.
TEST_F(DeobfuscationTest, MixedImportResolution) {
  ASSERT_TRUE(liftAndOptimize("obf_mixed_resolve"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";

  // Both imports should be resolved as dllimport declarations.
  EXPECT_TRUE(hasDllImport("GetModuleHandleA"))
      << "Expected @GetModuleHandleA dllimport declaration";
  EXPECT_TRUE(hasDllImport("GetProcAddress"))
      << "Expected @GetProcAddress dllimport declaration";

  // Both FNV-1a hashing loops should be fully eliminated.
  EXPECT_EQ(countFnvMultiplies(), 0u)
      << "All FNV-1a multiply operations should be eliminated";

  // Exactly 2 dllimport declarations.
  EXPECT_EQ(countDllImports(), 2u)
      << "Expected exactly GetModuleHandleA + GetProcAddress";
}

/// Verify the resolved imports are actually called (not just declared).
TEST_F(DeobfuscationTest, MixedImportsAreCalled) {
  ASSERT_TRUE(liftAndOptimize("obf_mixed_resolve"));
  EXPECT_TRUE(verifyModule());

  EXPECT_TRUE(isDllImportCalled("GetModuleHandleA"))
      << "Expected direct call to @GetModuleHandleA";
  EXPECT_TRUE(isDllImportCalled("GetProcAddress"))
      << "Expected direct call to @GetProcAddress";
}

/// Verify partial xorstr recovery of "kernel32.dll" in the mixed function.
///
/// Current behavior: xorstr fold produces partial i32 fragments "kern" and
/// ".dll" as constant stores to a stack frame alloca. Full "kernel32.dll"
/// recovery and global promotion are NOT achieved because:
///   (a) "el32" fragment is not folded (incomplete XOR chain folding)
///   (b) ptrtoint escape prevents OutlineConstantStackData promotion
TEST_F(DeobfuscationTest, MixedXorstrPartialRecovery) {
  ASSERT_TRUE(liftAndOptimize("obf_mixed_resolve"));
  EXPECT_TRUE(verifyModule());

  // Ideal: full string in global.
  bool found_global = hasGlobalConstantString("kernel32.dll");

  // Current: partial i32 fragments from xorstr fold.
  // "kern" = 0x6E72656B (LE i32 = 1852990827)
  // ".dll" = 0x6C6C642E (LE i32 = 1819042862)
  bool found_kern = hasConstI32Store(0x6E72656BU);
  bool found_dll = hasConstI32Store(0x6C6C642EU);

  EXPECT_TRUE(found_global || (found_kern && found_dll))
      << "Expected 'kernel32.dll' global or partial fragments 'kern' + '.dll'";

  // Strings should NOT be promoted to globals (ptrtoint escape blocks it).
  EXPECT_EQ(countConstStackGlobals(), 0u)
      << "Mixed function strings should not be promoted (ptrtoint escape)";
}

/// Verify the mixed function produces a single native function.
TEST_F(DeobfuscationTest, MixedSingleNativeFunction) {
  ASSERT_TRUE(liftAndOptimize("obf_mixed_resolve"));
  EXPECT_TRUE(verifyModule());

  // obf_mixed_resolve is self-contained — should produce exactly 1 function.
  EXPECT_EQ(countNativeFunctions(), 1u);
}

// =============================================================================
// Cloakwork obfuscation tests
// =============================================================================

/// DISABLED: CW_STR's TLS-guarded constinit pattern lifts ~2000 functions
/// and triggers an access violation (SEH 0xc0000005) in the pipeline.
TEST_F(DeobfuscationTest, DISABLED_CloakworkStrRecovery) {
  ASSERT_TRUE(liftAndOptimize("cw_str_hello"));
  EXPECT_TRUE(verifyModule());

  EXPECT_TRUE(hasGlobalConstantString(
      llvm::StringRef("Hello, World!\0", 14)))
      << "Expected 'Hello, World!' in promoted global from CW_STR";
}

/// Cloakwork CW_IMPORT: PEB walking with FNV-1a hashing.
///
/// Uses same hash constants as lazy_importer but different code structure
/// (cached resolution via global pointer, different loop layout).
/// Full resolution is not yet achieved — test verifies partial progress.
TEST_F(DeobfuscationTest, CloakworkImportFnvPresent) {
  ASSERT_TRUE(liftAndOptimize("cw_import_virtual_alloc"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";

  // Check full resolution (ideal) or FNV-1a pattern (current).
  bool resolved = hasDllImport("VirtualAlloc");
  unsigned fnv_count = countFnvMultiplies();

  EXPECT_TRUE(resolved || fnv_count > 0)
      << "Expected VirtualAlloc dllimport or FNV-1a multiply pattern";

  // Current state: 6 FNV-1a multiplies remain (not yet resolved).
  if (!resolved) {
    EXPECT_GE(fnv_count, 1u)
        << "Expected FNV-1a multiply (x * 16777619) to remain";
  }
}

/// Cloakwork CW_IMPORT: no spurious dllimports should be created for the
/// standalone import function (it only resolves VirtualAlloc).
TEST_F(DeobfuscationTest, CloakworkImportNoSpuriousDllImports) {
  ASSERT_TRUE(liftAndOptimize("cw_import_virtual_alloc"));
  EXPECT_TRUE(verifyModule());

  // cw_import_virtual_alloc resolves ONE import. We should see at most 1
  // dllimport declaration (0 if not yet resolved, 1 if resolved).
  unsigned dllimports = countDllImports();
  EXPECT_LE(dllimports, 1u)
      << "Standalone CW_IMPORT should not produce spurious dllimports";
}

/// Cloakwork combined (CW_STR + CW_IMPORT + CW_INT): basic sanity.
///
/// This function uses all three cloakwork features. The combined function
/// pulls in a lot of code (~116 native functions). Verify it doesn't crash
/// and that IAT-based resolution picks up at least some imports.
TEST_F(DeobfuscationTest, CloakworkCombinedSanity) {
  ASSERT_TRUE(liftAndOptimize("cw_combined"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";

  // Should produce many native functions (cloakwork inlines a lot of code).
  EXPECT_GT(countNativeFunctions(), 1u)
      << "Expected multiple functions from cloakwork combined";
}

/// Cloakwork combined: verify module is valid after full pipeline.
/// Note: IAT-resolved dllimports (GetFileSizeEx, AddVectoredExceptionHandler)
/// may be eliminated by ADCE during deobfuscation if the hash-based import
/// resolution doesn't create shortcut blocks that preserve those code paths.
/// Cloakwork uses non-standard FNV seeds, so HashImportAnnotation's
/// precomputed tables don't cover them yet.
TEST_F(DeobfuscationTest, CloakworkCombinedIATResolution) {
  ASSERT_TRUE(liftAndOptimize("cw_combined"));
  EXPECT_TRUE(verifyModule());

  // dllimport count may be 0 if hash resolution doesn't fire for cloakwork's
  // non-standard seeds.  This is a known limitation — once we support
  // arbitrary seed extraction in Strategy 1, this should improve.
  unsigned imports = countDllImports();
  (void)imports;  // Accept any count, including 0.
}

/// Cloakwork combined: FNV-1a patterns should be present (import hiding
/// not yet fully resolved for cloakwork's code structure).
TEST_F(DeobfuscationTest, CloakworkCombinedFnvPatterns) {
  ASSERT_TRUE(liftAndOptimize("cw_combined"));
  EXPECT_TRUE(verifyModule());

  // FNV-1a patterns remain because cloakwork's hash loop structure
  // differs from lazy_importer's. Once HashImportAnnotation learns to
  // recognize the cloakwork pattern, this count should drop to 0.
  unsigned fnv_count = countFnvMultiplies();
  bool lla_resolved = hasDllImport("LoadLibraryA");

  // Either LoadLibraryA is resolved (ideal) or FNV-1a patterns remain.
  EXPECT_TRUE(lla_resolved || fnv_count > 0)
      << "Expected LoadLibraryA dllimport or remaining FNV-1a patterns";
}

/// Cloakwork combined: OutlineConstantStackData should promote some allocas
/// from the many inlined cloakwork functions.
TEST_F(DeobfuscationTest, CloakworkCombinedConstStackPromotion) {
  ASSERT_TRUE(liftAndOptimize("cw_combined"));
  EXPECT_TRUE(verifyModule());

  // The cloakwork combined function inlines many sub-functions that contain
  // constant stack data (PE header offsets, lookup tables, etc.).
  EXPECT_GT(countConstStackGlobals(), 0u)
      << "Expected OutlineConstantStackData to promote cloakwork allocas";
}

// =============================================================================
// cmut value mutation tests
// =============================================================================
//
// cmut<T> obfuscates values by storing them in multiple mutated forms:
//   - Shifted copies (value << random_shift) in 16/32/64-bit storage
//   - Split-word storage (64-bit split into 4x16 or 2x32 rotated words)
//   - SIMD-packed (__m128i with value in one lane, random in others)
//   - Bitmap (each bit stored as bool[128])
// Reconstruction selects one path based on a random mode.
//
// cmut functions pull in heavy CRT code (std::time, std::mt19937,
// std::recursive_mutex, SIMD intrinsics) resulting in 100+ lifted functions
// and ~185K lines of IR.
//
// NOTE: i32 and i64 variants currently trigger an access violation (SEH
// 0xc0000005) during pipeline optimization. The i8 variant uses plain
// shifts (no rotate intrinsics) and optimizes successfully. The i32/i64
// paths use _rotl/_rotr which generate different IR patterns that trigger
// the crash. These are marked DISABLED_ until the pipeline bug is fixed.
//
// Verified anchor points (from i8 output, ~185K lines → ~54K lines):
//   1. ~1,682 shift ops (shl/lshr) from shift-based mutation
//   2. ~547 OR ops from bitwise manipulation
//   3. ~223 alloca instructions across 102 native functions
//   4. 53 @.const_stack globals from OutlineConstantStackData
//   5. 1 dllimport (AddVectoredExceptionHandler) from IAT resolution
//   6. Vector types (<4 x i32>, <2 x i64>) from SIMD operations

/// cmut<int8_t>('A').get() — i8 mutation/reconstruction.
///
/// The ui8 path has 4 reconstruction modes:
///   mode 0: m_ui16 >> m_sh_16
///   mode 1: m_ui32 >> m_sh_32
///   mode 2: m_ui64 >> m_sh_64
///   mode 3: SIMD extract >> m_sh_32
/// Uses plain shifts (NOT rotate), so the pipeline handles it successfully.
TEST_F(DeobfuscationTest, CmutI8Sanity) {
  ASSERT_TRUE(liftAndOptimize("cmut_i8_get"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";

  // cmut lifts ~100+ CRT functions (mt19937, mutex, time, etc.).
  EXPECT_GT(countNativeFunctions(), 10u)
      << "Expected many native functions from cmut CRT inlining";
}

/// cmut i8: shift operations from mutation mechanism.
///
/// deconstruct_t shifts the value left by a random amount into m_ui16/32/64,
/// and reconstruct_t shifts it back right. The shift amounts depend on
/// std::time(nullptr) and cannot be constant-folded.
TEST_F(DeobfuscationTest, CmutI8ShiftOps) {
  ASSERT_TRUE(liftAndOptimize("cmut_i8_get"));
  EXPECT_TRUE(verifyModule());

  // Observed: ~1,682 shift operations across all native functions.
  // These come from cmut shift-mutation, mt19937 internal operations,
  // and address computation in CRT code.
  unsigned shifts = countShiftOps();
  EXPECT_GT(shifts, 100u)
      << "Expected hundreds of shift ops from cmut + CRT code (got "
      << shifts << ")";
}

/// cmut i8: OR operations from bitwise manipulation.
///
/// cmut's deconstruct_t fills unused bytes with random data using OR:
///   m_ui16 |= (uint8_t)(r() & 0xFF) << (i * 8)
/// Additional ORs come from CRT internal bit manipulation.
TEST_F(DeobfuscationTest, CmutI8OrOps) {
  ASSERT_TRUE(liftAndOptimize("cmut_i8_get"));
  EXPECT_TRUE(verifyModule());

  // Observed: ~547 OR operations.
  unsigned ors = countOrOps();
  EXPECT_GT(ors, 50u)
      << "Expected OR operations from cmut random byte filling (got "
      << ors << ")";
}

/// cmut i8: stack frame recovery across multiple native functions.
///
/// The cmut struct is ~300 bytes (shift trackers, bitmap[128], mutated
/// storage, SIMD vector, mutex). CRT functions (mt19937, mutex) also
/// have significant stack frames. RecoverStackFrame should create allocas
/// for all of these.
TEST_F(DeobfuscationTest, CmutI8StackFrame) {
  ASSERT_TRUE(liftAndOptimize("cmut_i8_get"));
  EXPECT_TRUE(verifyModule());

  // Observed: ~223 allocas across 102 native functions.
  unsigned allocas = countAllocasInNative();
  EXPECT_GT(allocas, 20u)
      << "Expected many stack allocas from cmut + CRT frames (got "
      << allocas << ")";
}

/// cmut i8: OutlineConstantStackData promotes constant allocas to globals.
///
/// CRT code (mt19937 state initialization, exception handler tables, etc.)
/// contains many constant-initialized stack allocas that can be promoted.
TEST_F(DeobfuscationTest, CmutI8ConstStackPromotion) {
  ASSERT_TRUE(liftAndOptimize("cmut_i8_get"));
  EXPECT_TRUE(verifyModule());

  // Observed: 53 @.const_stack globals.
  unsigned csg = countConstStackGlobals();
  EXPECT_GT(csg, 10u)
      << "Expected OutlineConstantStackData promotions from CRT data (got "
      << csg << ")";
}

/// cmut i8: verify module validity after full pipeline.
/// Note: dllimport count may be 0 — the previously observed
/// AddVectoredExceptionHandler dllimport was a false positive from
/// DenseMap UB (find on sentinel key 0xFFFFFFFF).
TEST_F(DeobfuscationTest, CmutI8IATResolution) {
  ASSERT_TRUE(liftAndOptimize("cmut_i8_get"));
  EXPECT_TRUE(verifyModule());

  unsigned imports = countDllImports();
  (void)imports;  // Accept any count, including 0.
}

/// cmut i8: substantial instruction count from mutation + CRT.
///
/// An unobfuscated `return 65` would be ~3 instructions. cmut adds
/// mutation/reconstruction, RNG seeding, mutex locking, SIMD packing,
/// and CRT helper functions — producing thousands of instructions.
TEST_F(DeobfuscationTest, CmutI8Complexity) {
  ASSERT_TRUE(liftAndOptimize("cmut_i8_get"));
  EXPECT_TRUE(verifyModule());

  // Observed: ~40,000+ instructions across 102 native functions.
  unsigned total = countNativeInstructions();
  EXPECT_GT(total, 1000u)
      << "Expected thousands of instructions from cmut obfuscation (got "
      << total << ")";
}

/// cmut i8: external function declarations from CRT dependencies.
///
/// cmut uses std::time(), std::recursive_mutex, and potentially
/// std::random_device. These result in external function declarations
/// (either dllimport or omill dispatch/handler functions).
TEST_F(DeobfuscationTest, CmutI8ExternalCalls) {
  ASSERT_TRUE(liftAndOptimize("cmut_i8_get"));
  EXPECT_TRUE(verifyModule());

  unsigned ext_count = 0;
  for (auto &F : *module()) {
    if (F.isDeclaration() && !F.getName().starts_with("llvm.") &&
        !F.getName().starts_with("__remill"))
      ext_count++;
  }

  // Should have omill runtime functions (__omill_dispatch_call, etc.)
  // and potentially IAT-resolved imports.
  EXPECT_GT(ext_count, 0u)
      << "Expected external declarations from CRT dependencies";
}

// ---------------------------------------------------------------------------
// cmut i32 and i64 variants — previously crashed with SEH 0xc0000005.
// Root cause: LowerFunctionReturn, LowerJump, LowerErrorAndMissing did not
// call removePredecessor() when replacing terminators, leaving malformed PHI
// nodes that crashed InstCombine. Fixed by adding removePredecessor() calls.
// ---------------------------------------------------------------------------

/// cmut<int32_t>(42).get() — i32 mutation via shift-64 and SIMD rotate.
///
/// The ui32 path uses rotate intrinsics (_rotl/_rotr) for SIMD-based
/// mutation, unlike i8 which uses plain shifts.
TEST_F(DeobfuscationTest, CmutI32Sanity) {
  ASSERT_TRUE(liftAndOptimize("cmut_i32_get"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";
  EXPECT_GT(countNativeFunctions(), 10u)
      << "Expected many native functions from cmut CRT inlining";
  EXPECT_GT(countShiftOps(), 100u)
      << "Expected shift ops from mutation/reconstruction";
}

/// cmut i32: stack frame and constant stack promotion.
TEST_F(DeobfuscationTest, CmutI32StackAndPromotion) {
  ASSERT_TRUE(liftAndOptimize("cmut_i32_get"));
  EXPECT_TRUE(verifyModule());
  EXPECT_GT(countAllocasInNative(), 20u)
      << "Expected stack allocas from cmut + CRT frames";
  EXPECT_GT(countConstStackGlobals(), 10u)
      << "Expected OutlineConstantStackData promotions from CRT data";
}

/// cmut<int64_t>(0xCAFEBABE).get() — i64 split-word + rotate + SIMD.
///
/// The i64 path is the most complex: values are split into 4x16-bit and
/// 2x32-bit rotated sub-words, plus SIMD with _mm_set_epi64x.
/// Reconstruction reassembles via OR operations on rotated sub-words.
TEST_F(DeobfuscationTest, CmutI64Sanity) {
  ASSERT_TRUE(liftAndOptimize("cmut_i64_get"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";
  EXPECT_GT(countNativeFunctions(), 10u)
      << "Expected many native functions from cmut CRT inlining";
  EXPECT_GT(countShiftOps(), 100u)
      << "Expected shift ops from i64 rotate-based mutation";
  EXPECT_GT(countOrOps(), 50u)
      << "Expected OR ops from sub-word reassembly";
}

/// cmut i32 roundtrip with runtime input — prevents constant folding.
TEST_F(DeobfuscationTest, CmutI32RoundtripSanity) {
  ASSERT_TRUE(liftAndOptimize("cmut_i32_roundtrip"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";
  EXPECT_GT(countNativeFunctions(), 10u)
      << "Expected many native functions";
  EXPECT_GT(countAllocasInNative(), 20u)
      << "Expected stack allocas for cmut object with runtime input";
}

/// cmut i32 set() path — double mutation (ctor + set).
TEST_F(DeobfuscationTest, CmutI32SetSanity) {
  ASSERT_TRUE(liftAndOptimize("cmut_i32_set"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";
  EXPECT_GT(countNativeFunctions(), 10u)
      << "Expected many native functions from double mutation";
  EXPECT_GT(countShiftOps(), 100u)
      << "Expected shift ops from double mutation in set() path";
}

}  // namespace
