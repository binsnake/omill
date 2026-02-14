#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Promotes stack allocas that are fully initialized with constant stores
/// to global constants.  This is primarily useful after xorstr deobfuscation,
/// where ConstantMemoryFolding + InstCombine fold the XOR decryption to
/// plaintext integer constants stored to a stack alloca.
///
/// Before:
///   %buf = alloca [16 x i8]
///   store i64 0x57202C6F6C6C6548, ptr %buf           ; "Hello, W"
///   store i64 0x0021646C726F, ptr (gep %buf, 8)      ; "orld!\0"
///   ... loop reading bytes from %buf ...
///
/// After:
///   @.const_stack = private constant [16 x i8] c"Hello, World!\00\00\00"
///   ... loop reading bytes from @.const_stack ...
///
/// Requirements for promotion:
///   - All stores to the alloca are ConstantInt values
///   - All stores are in the entry block (dominate all reads)
///   - The alloca pointer does not escape (not passed to calls or stored)
class OutlineConstantStackDataPass
    : public llvm::PassInfoMixin<OutlineConstantStackDataPass> {
 public:
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "OutlineConstantStackDataPass"; }
};

}  // namespace omill
