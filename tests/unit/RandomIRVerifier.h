#pragma once

#if OMILL_ENABLE_Z3

#include <llvm/IR/Function.h>
#include <llvm/IR/Module.h>

#include <z3++.h>

#include <memory>
#include <random>
#include <string>

namespace omill {
namespace test {

enum class PassKind {
  CoalesceByteReassembly,
  CollapsePartialXMMWrites,
  SimplifyVectorFlagComputation,
  DeadStateRoundtripElimination,
  EliminateRedundantByteStores,
  FoldConstantVectorChains,
  OutlineConstantStackData,
};

class RandomIRVerifier {
 public:
  RandomIRVerifier(z3::context &ctx, uint64_t seed);

  struct Result {
    bool all_passed = true;
    unsigned num_tested = 0;
    std::string first_failure;
  };

  Result fuzzPass(PassKind kind, unsigned iterations);

 private:
  std::mt19937_64 rng_;
  z3::context &ctx_;

  std::unique_ptr<llvm::LLVMContext> makeLLVMContext();
  std::unique_ptr<llvm::Module> makeModule(llvm::LLVMContext &Ctx);

  llvm::Function *genByteReassembly(llvm::Module &M, llvm::LLVMContext &Ctx);
  llvm::Function *genPartialXMMWrite(llvm::Module &M, llvm::LLVMContext &Ctx);
  llvm::Function *genVectorFlagComputation(llvm::Module &M,
                                            llvm::LLVMContext &Ctx);
  llvm::Function *genStateRoundtrip(llvm::Module &M, llvm::LLVMContext &Ctx);
  llvm::Function *genRedundantByteStore(llvm::Module &M,
                                         llvm::LLVMContext &Ctx);
  llvm::Function *genConstantVectorChain(llvm::Module &M,
                                          llvm::LLVMContext &Ctx);
  llvm::Function *genConstantStackData(llvm::Module &M, llvm::LLVMContext &Ctx);

  void runPassOnFunction(PassKind kind, llvm::Function &F);
};

}  // namespace test
}  // namespace omill

#endif  // OMILL_ENABLE_Z3
