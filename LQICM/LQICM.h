#ifndef LLVM_TRANSFORMS_SCALAR_LQICM_H
#define LLVM_TRANSFORMS_SCALAR_LQICM_H

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/IR/PassManager.h"

namespace llvm {

/// Performs Loop Invariant Code Motion Pass.
class LQICMPass : public PassInfoMixin<LQICMPass> {
public:
  PreservedAnalyses run(Loop &L, LoopStandardAnalysisResults &AR,
          LoopAnalysisManager &AM);
};
} // end namespace llvm

#endif // LLVM_TRANSFORMS_SCALAR_LQICM_H
