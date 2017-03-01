//===--                    - Loop peeling utilities -----------------------===//
//
//                     The LLVM Compiler Infrastructure
//
//===----------------------------------------------------------------------===//
//
//
//===----------------------------------------------------------------------===//

#include "./LQICMUtils.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/LoopIterator.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include <algorithm>

using namespace llvm;

#define DEBUG_TYPE "lqicm"

// Check whether we are capable of peeling this loop.
static bool canPeel(Loop *L) {/*{-{*/
  // Make sure the loop is in simplified form
  if (!L->isLoopSimplifyForm())
    return false;

  // Only peel loops that contain a single exit
  if (!L->getExitingBlock() || !L->getUniqueExitBlock())
    return false;

  return true;
}/*}-}*/

/// \brief Update the branch weights of the latch of a peeled-off loop
/// iteration.
/// This sets the branch weights for the latch of the recently peeled off loop
/// iteration correctly. 
/// Our goal is to make sure that:
/// a) The total weight of all the copies of the loop body is preserved.
/// b) The total weight of the loop exit is preserved.
/// c) The body weight is reasonably distributed between the peeled iterations.
///
/// \param Header The copy of the header block that belongs to next iteration.
/// \param LatchBR The copy of the latch branch that belongs to this iteration.
/// \param IterNumber The serial number of the iteration that was just
/// peeled off.
/// \param AvgIters The average number of iterations we expect the loop to have.
/// \param[in,out] PeeledHeaderWeight The total number of dynamic loop
/// iterations that are unaccounted for. As an input, it represents the number
/// of times we expect to enter the header of the iteration currently being
/// peeled off. The output is the number of times we expect to enter the
/// header of the next iteration.
static void updateBranchWeights(BasicBlock *Header, BranchInst *LatchBR,/*{-{*/
                                unsigned IterNumber, unsigned AvgIters,
                                uint64_t &PeeledHeaderWeight) {

  // FIXME: Pick a more realistic distribution.
  // Currently the proportion of weight we assign to the fall-through
  // side of the branch drops linearly with the iteration number, and we use
  // a 0.9 fudge factor to make the drop-off less sharp...
  if (PeeledHeaderWeight) {
    uint64_t FallThruWeight =
        PeeledHeaderWeight * ((float)(AvgIters - IterNumber) / AvgIters * 0.9);
    uint64_t ExitWeight = PeeledHeaderWeight - FallThruWeight;
    PeeledHeaderWeight -= ExitWeight;

    unsigned HeaderIdx = (LatchBR->getSuccessor(0) == Header ? 0 : 1);
    MDBuilder MDB(LatchBR->getContext());
    MDNode *WeightNode =
        HeaderIdx ? MDB.createBranchWeights(ExitWeight, FallThruWeight)
                  : MDB.createBranchWeights(FallThruWeight, ExitWeight);
    LatchBR->setMetadata(LLVMContext::MD_prof, WeightNode);
  }
}/*}-}*/

/// Remove a loop.
bool deleteLoop(Loop *L, DominatorTree &DT, ScalarEvolution &SE, LoopInfo/*{-{*/
                &loopInfo, BSet* BBToRemove) {
  assert(L->isLCSSAForm(DT) && "Expected LCSSA!");

  // We can only remove the loop if there is a preheader that we can
  // branch from after removing it.
  BasicBlock *preheader = L->getLoopPreheader();
  if (!preheader)
    return false;

  // If LoopSimplify form is not available, stay out of trouble.
  if (!L->hasDedicatedExits())
    return false;

  SmallVector<BasicBlock *, 4> exitingBlocks;
  L->getExitingBlocks(exitingBlocks);

  SmallVector<BasicBlock *, 4> exitBlocks;
  L->getUniqueExitBlocks(exitBlocks);

  // FIXME Do we care here? Theoritically not because we take the worst case
  // then all branches in consideration. ↓
  // We require that the loop only have a single exit block.  Otherwise, we'd
  // be in the situation of needing to be able to solve statically which exit
  // block will be branched to, or trying to preserve the branching logic in
  // a loop invariant manner.
  if (exitBlocks.size() != 1)
    return false;

  bool Changed = false;

  // Now that we know the removal is safe, remove the loop by changing the
  // branch from the preheader to go to the single exit block.
  BasicBlock *exitBlock = exitBlocks[0];

  // Because we're deleting a large chunk of code at once, the sequence in which
  // we remove things is very important to avoid invalidation issues.  Don't
  // mess with this unless you have good reason and know what you're doing.

  // Tell ScalarEvolution that the loop is deleted. Do this before
  // deleting the loop so that ScalarEvolution can look at the loop
  // to determine what it needs to clean up.
  SE.forgetLoop(L);

  // Connect the preheader directly to the exit block.
  TerminatorInst *TI = preheader->getTerminator();
  TI->replaceUsesOfWith(L->getHeader(), exitBlock);

  // Rewrite phis in the exit block to get their inputs from
  // the preheader instead of the exiting block.
  BasicBlock *exitingBlock = exitingBlocks[0];
  BasicBlock::iterator BI = exitBlock->begin();
  DEBUG(dbgs() << " Rewrite phis in the exit Block…");
  while (PHINode *P = dyn_cast<PHINode>(BI)) {
    int j = P->getBasicBlockIndex(exitingBlock);
    assert(j >= 0 && "Can't find exiting block in exit block's phi node!");
    P->setIncomingBlock(j, preheader);
    for (unsigned i = 1; i < exitingBlocks.size(); ++i)
      P->removeIncomingValue(exitingBlocks[i]);
    ++BI;
  }
  DEBUG(dbgs() << " OK\n");
      

  // Update the dominator tree and remove the instructions and blocks that will
  // be deleted from the reference counting scheme.
  SmallVector<DomTreeNode*, 8> ChildNodes;
  DEBUG(dbgs() << " Update dominator tree…");
  for (Loop::block_iterator LI = L->block_begin(), LE = L->block_end();
       LI != LE; ++LI) {
    // Move all of the block's children to be children of the preheader, which
    // allows us to remove the domtree entry for the block.
    ChildNodes.insert(ChildNodes.begin(), DT[*LI]->begin(), DT[*LI]->end());
    for (DomTreeNode *ChildNode : ChildNodes) {
      DT.changeImmediateDominator(ChildNode, DT[preheader]);
    }

    ChildNodes.clear();
    DT.eraseNode(*LI);

    // Remove the block from the reference counting scheme, so that we can
    // delete it freely later.
    (*LI)->dropAllReferences();
  }
  DEBUG(dbgs() << " OK\n");

  // Erase the instructions and the blocks without having to worry
  // about ordering because we already dropped the references.
  // NOTE: This iteration is safe because erasing the block does not remove its
  // entry from the loop's block list.  We do that in the next section.
  DEBUG(dbgs() << " remove blocks…");
  for (Loop::block_iterator LI = L->block_begin(), LE = L->block_end();
       LI != LE; ++LI){
      BBToRemove->insert(*LI);
    /* (*LI)->eraseFromParent(); */
  }
  DEBUG(dbgs() << " OK\n");

  // Finally, the blocks from loopinfo.  This has to happen late because
  // otherwise our loop iterators won't work.

  // Will be done further, follow BBToRemove ↓
  /* SmallPtrSet<BasicBlock *, 8> blocks; */
  /* blocks.insert(L->block_begin(), L->block_end()); */
  /* for (BasicBlock *BB : blocks) */
  /*   loopInfo.removeBlock(BB); */

  // The last step is to update LoopInfo now that we've eliminated this loop.
  /* loopInfo.markAsRemoved(L); */
  Changed = true;

  return Changed;
}/*}-}*/

// Remove chuncks with deg <= curDeg (except if < 0)/*{-{*/
VSet updateLoopBody(Loop* L, unsigned curDeg, MapLoopDeg* mapLoopDeg,
                    ValueToValueMapTy &VMap, ScalarEvolution *SE, DominatorTree
                    *DT,PostDominatorTree *PDT, LoopInfo *LI){
  DEBUG(dbgs() <<"CurDeg = " << curDeg << " :\n");

  // If we are here, it works
  Value* head = dyn_cast<Value>(L->getHeader());

  MapDeg *mapDeg = (*mapLoopDeg)[head];

  std::vector<Loop*> LoopToRemove;
  ISet toRemove;
  VSet toClean;
  BSet BBToRemove;
  for (BasicBlock *BB : L->blocks()){
    if(BB != L->getHeader()){
      for(BasicBlock::iterator LII = BB->begin(), LE = BB->end(); LII != LE;
          ++LII){
        Instruction &I = *LII;
        DEBUG(dbgs() << "Treating: " << I << " … " );
        if(Value* VI = dyn_cast<Value>(&I)){
          if((*mapDeg)[VI] == curDeg){
            if(isa<Instruction>(&I)){
              if(isa<TerminatorInst>(&I)){
                DEBUG(dbgs() <<"Start of a registered branch we need to hoist"<<
                      " with deg = " << (*mapDeg)[VI] << "\n");
                TerminatorInst *TInst = dyn_cast<TerminatorInst>(&I);
                // Put the branches to the garbage
                BasicBlock *Then = TInst->getSuccessor(0);
                BasicBlock *Else = TInst->getSuccessor(1);
                BBToRemove.insert(Then);
                BBToRemove.insert(Else);
                // Modify the TInst to go directly to the if.end…
                BasicBlock *IfEnd = PDT->findNearestCommonDominator(Then,Else);
                BranchInst* br = llvm::BranchInst::Create(IfEnd);
                ReplaceInstWithInst(TInst->getParent()->getInstList(),LII,br);

                // Now adjust the phi nodes in the ifEnd
                for (BasicBlock::iterator PII = IfEnd->begin(); isa<PHINode>(PII);
                     ++PII) {
                  Instruction &PI = *PII;
                  toRemove.insert(&PI);
                }
                
                // Another cleaner thing is to merge IfEnd and BB
                /* MergeBlockIntoPredecessor(IfEnd); //Does not work… why? */
                // Don't care, other passes like simplifycfg will do it ;)
              }
              else{
                toRemove.insert(&I);
                DEBUG(dbgs() << "to remove… \n");
              }
            }
            else{
              DEBUG(dbgs() <<"Trying to remove an entire block… of value "<<
                    *LII << " with deg = " << (*mapDeg)[VI] << "\n");
            }
          }
          else DEBUG(dbgs() << "OK \n");
        }
        else
          DEBUG(dbgs() <<"**************ERROR dyn_cast****************\n");
      }
    }
    if(inSubLoop(BB, L, LI)){
      DEBUG(dbgs() << " BB " << BB << " is in an innerLoop \n");
      Value* head = dyn_cast<Value>(BB);
      if((*mapLoopDeg)[head]){
        DEBUG(dbgs() << " BB " << head << " is the head of the innerloop " << 
              "with deg = " << (*mapDeg)[head] << "\n");
        if((*mapDeg)[head] == curDeg){
          Loop* innerLoop = LI->getLoopFor(BB);
          if(deleteLoop(innerLoop, *DT, *SE, *LI, &BBToRemove)){
            LoopToRemove.push_back(innerLoop);
            DEBUG(dbgs() << " LOOP REMOVED! \n");
          }
          else DEBUG(dbgs() << "ERROR: LOOP NOT REMOVED! \n");
        }
      }
    }
  }

  // Changer ça c'est moche ! FIXME
  for (auto VV = BBToRemove.begin(), E = BBToRemove.end(); VV != E; ++VV) {
    BasicBlock* BB = *VV;
    for(BasicBlock::iterator LII = BB->begin(), LE = BB->end(); LII != LE;
        ++LII){
      Instruction &I = *LII;
      toRemove.insert(&I);
    }
  }

  // Changer ça c'est moche ! FIXME
  ISet toRemoveOP;
  for(Instruction* I : toRemove){
    DEBUG(dbgs() <<"Removing OP from Instruction… "<< *I <<" \n");
    Instruction *NewInst = cast<Instruction>(VMap[&*I]);
    /* BB->dump(); */
    DEBUG(dbgs() <<"ReplaceAllUses of" << *I << " With " << *NewInst <<"\n");
    I->replaceAllUsesWith(NewInst); // With the last cloned value for I…
    toRemoveOP.insert(I);
    /* I->eraseFromParent(); */
    for(auto OP = I->op_begin(), E = I->op_end(); OP!=E; ++OP){
      DEBUG(dbgs() <<"ToRemove OP " << OP->get() <<"…\n");
      if(OP->get() && isa<PHINode>(OP->get())){
        Instruction* v = cast<Instruction>(OP->get());
        toClean.insert(v);
      }
    }
  }

  DEBUG(dbgs() <<"Removing OP…\n");
  for (auto VV = toRemoveOP.begin(), E = toRemoveOP.end(); VV != E; ++VV) {
    Instruction* V = *VV;
    DEBUG(dbgs() <<"Removing " << *V <<"…\n");
    V->eraseFromParent();
    DEBUG(dbgs() <<"Removed!\n");
  }
  for (auto VV = BBToRemove.begin(), E = BBToRemove.end(); VV != E; ++VV) {
    BasicBlock* BB = *VV;
    DEBUG(dbgs() <<"Removing " << *BB <<"…\n");
    /* Loop* LL = LI->getLoopFor(BB); */
    /* LL->removeBlockFromLoop(BB); */
    BB->eraseFromParent();
    DEBUG(dbgs() <<"Removed!\n");
  }

  // FIXME maybe we should do this at the end ^^'
  // The last step is to update LoopInfo now that we've eliminated this loop.
  for(Loop* LL : LoopToRemove){
    DEBUG(dbgs() <<"Removing " << *LL <<"…\n");
    SmallPtrSet<BasicBlock *, 8> blocks;
    blocks.insert(LL->block_begin(), LL->block_end());
    for (BasicBlock *BB : blocks){
      LI->removeBlock(BB);
    }
    LI->markAsRemoved(LL);
    DEBUG(dbgs() <<"Removed!\n");
  }

  return toClean;
}/*}-}*/

/// \brief Clones the body of the loop L, putting it between \p InsertTop and \p
/// InsertBot.
/// \param IterNumber The serial number of the iteration currently being
/// peeled off.
/// \param Exit The exit block of the original loop.
/// \param[out] NewBlocks A list of the the blocks in the newly created clone
/// \param[out] VMap The value map between the loop and the new clone.
/// \param LoopBlocks A helper for DFS-traversal of the loop.
/// \param LVMap A value-map that maps instructions from the original loop to
/// instructions in the last peeled-off iteration.
static void cloneLoopBlocks(Loop *L, unsigned IterNumber, BasicBlock *InsertTop,/*{-{*/
                            BasicBlock *InsertBot, BasicBlock *Exit,
                            SmallVectorImpl<BasicBlock *> &NewBlocks,
                            LoopBlocksDFS &LoopBlocks, ValueToValueMapTy &VMap,
                            ValueToValueMapTy &LVMap, LoopInfo *LI) {

  BasicBlock *Header = L->getHeader();
  BasicBlock *Latch = L->getLoopLatch();
  BasicBlock *PreHeader = L->getLoopPreheader();

  Function *F = Header->getParent();
  LoopBlocksDFS::RPOIterator BlockBegin = LoopBlocks.beginRPO();
  LoopBlocksDFS::RPOIterator BlockEnd = LoopBlocks.endRPO();
  Loop *ParentLoop = L->getParentLoop();

  // For each block in the original loop, create a new copy,
  // and update the value map with the newly created values.
  for (LoopBlocksDFS::RPOIterator BB = BlockBegin; BB != BlockEnd; ++BB) {
    DEBUG(dbgs() << "cloning BB : " <<"\n");
    (*BB)->dump();
    BasicBlock *NewBB = CloneBasicBlock(*BB, VMap, ".peel", F);
    NewBlocks.push_back(NewBB);

    if (ParentLoop)
      ParentLoop->addBasicBlockToLoop(NewBB, *LI);

    VMap[*BB] = NewBB;
  }

  // Hook-up the control flow for the newly inserted blocks.
  // The new header is hooked up directly to the "top", which is either
  // the original loop preheader (for the first iteration) or the previous
  // iteration's exiting block (for every other iteration)
  InsertTop->getTerminator()->setSuccessor(0, cast<BasicBlock>(VMap[Header]));

  // Similarly, for the latch:
  // The original exiting edge is still hooked up to the loop exit.
  // The backedge now goes to the "bottom", which is either the loop's real
  // header (for the last peeled iteration) or the copied header of the next
  // iteration (for every other iteration)
  BranchInst *LatchBR =
      cast<BranchInst>(cast<BasicBlock>(VMap[Latch])->getTerminator());
  /* DEBUG(dbgs() <<"LatchBR = " << *LatchBR << "\n"); */
  unsigned HeaderIdx = (LatchBR->getSuccessor(0) == Header ? 0 : 1);
  LatchBR->setSuccessor(HeaderIdx, InsertBot);
  /* DEBUG(dbgs() <<"LatchBR = " << *LatchBR << "\n"); */
  /* DEBUG(dbgs() <<"HeaderIdx = " << HeaderIdx << "\n"); */
  if((1 - HeaderIdx) < LatchBR->getNumSuccessors())
    LatchBR->setSuccessor(1 - HeaderIdx, Exit);
  DEBUG(dbgs() <<"LatchBR = " << *LatchBR << "\n");
  //FIXME ERROR here why?
  /* LatchBR->setSuccessor(1 - HeaderIdx, Exit); */

  // The new copy of the loop body starts with a bunch of PHI nodes
  // that pick an incoming value from either the preheader, or the previous
  // loop iteration. Since this copy is no longer part of the loop, we
  // resolve this statically:
  // For the first iteration, we use the value from the preheader directly.
  // For any other iteration, we replace the phi with the value generated by
  // the immediately preceding clone of the loop body (which represents
  // the previous iteration).
  for (BasicBlock::iterator I = Header->begin(); isa<PHINode>(I); ++I) {
    PHINode *NewPHI = cast<PHINode>(VMap[&*I]);
    if (IterNumber == 0) {
      VMap[&*I] = NewPHI->getIncomingValueForBlock(PreHeader);
    } else {
      Value *LatchVal = NewPHI->getIncomingValueForBlock(Latch);
      Instruction *LatchInst = dyn_cast<Instruction>(LatchVal);
      if (LatchInst && L->contains(LatchInst))
        VMap[&*I] = LVMap[LatchInst];
      else
        VMap[&*I] = LatchVal;
    }
    cast<BasicBlock>(VMap[Header])->getInstList().erase(NewPHI);
  }

  // Fix up the outgoing values - we need to add a value for the iteration
  // we've just created. Note that this must happen *after* the incoming
  // values are adjusted, since the value going out of the latch may also be
  // a value coming into the header.
  for (BasicBlock::iterator I = Exit->begin(); isa<PHINode>(I); ++I) {
    PHINode *PHI = cast<PHINode>(I);
    Value *LatchVal = PHI->getIncomingValueForBlock(Latch);
    Instruction *LatchInst = dyn_cast<Instruction>(LatchVal);
    if (LatchInst && L->contains(LatchInst))
      LatchVal = VMap[LatchVal];
    PHI->addIncoming(LatchVal, cast<BasicBlock>(VMap[Latch]));
  }

  // LastValueMap is updated with the values for the current loop
  // which are used the next time this function is called.
  for (const auto &KV : VMap)
    LVMap[KV.first] = KV.second;
}/*}-}*/

/// \brief Peel off the first \p PeelCount iterations of loop \p L.
///
/// Note that this does not peel them off as a single straight-line block.
/// Rather, each iteration is peeled off separately, and needs to check the
/// exit condition.
/// For loops that dynamically execute \p PeelCount iterations or less
/// this provides a benefit, since the peeled off iterations, which account
/// for the bulk of dynamic execution, can be further simplified by scalar
/// optimizations.
bool llvm::mypeelLoop(Loop *L, unsigned PeelCount, MapLoopDeg* mapLoopDeg,/*{-{*/
                      LoopInfo *LI, ScalarEvolution *SE, DominatorTree *DT,
                      PostDominatorTree *PDT, bool PreserveLCSSA) {
  DEBUG(dbgs() <<"**************in mypeelLoop !****************\n");
  L->print(dbgs());
  DEBUG(dbgs() <<"Loop Before peeling ↑ \n");
  if (!canPeel(L))
    return false;

  // If we are here, it works
  Value* head = dyn_cast<Value>(L->getHeader());

  MapDeg *mapDeg = (*mapLoopDeg)[head];

  LoopBlocksDFS LoopBlocks(L);
  LoopBlocks.perform(LI);

  BasicBlock *Header = L->getHeader();
  BasicBlock *PreHeader = L->getLoopPreheader();
  BasicBlock *Latch = L->getLoopLatch();
  BasicBlock *Exit = L->getUniqueExitBlock();

  Function *F = Header->getParent();

  // Set up all the necessary basic blocks. It is convenient to split the
  // preheader into 3 parts - two blocks to anchor the peeled copy of the loop
  // body, and a new preheader for the "real" loop.

  // Peeling the first iteration transforms.
  //
  // PreHeader:
  // ...
  // Header:
  //   LoopBody
  //   If (cond) goto Header
  // Exit:
  //
  // into
  //
  // InsertTop:
  //   LoopBody
  //   If (!cond) goto Exit
  // InsertBot:
  // NewPreHeader:
  // ...
  // Header:
  //  LoopBody
  //  If (cond) goto Header
  // Exit:
  //
  // Each following iteration will split the current bottom anchor in two,
  // and put the new copy of the loop body between these two blocks. That is,
  // after peeling another iteration from the example above, we'll split 
  // InsertBot, and get:
  //
  // InsertTop:
  //   LoopBody
  //   If (!cond) goto Exit
  // InsertBot:
  //   LoopBody
  //   If (!cond) goto Exit
  // InsertBot.next:
  // NewPreHeader:
  // ...
  // Header:
  //  LoopBody
  //  If (cond) goto Header
  // Exit:

  BasicBlock *InsertTop = SplitEdge(PreHeader, Header, DT, LI);
  BasicBlock *InsertBot =
      SplitBlock(InsertTop, InsertTop->getTerminator(), DT, LI);
  BasicBlock *NewPreHeader =
      SplitBlock(InsertBot, InsertBot->getTerminator(), DT, LI);

  InsertTop->setName(Header->getName() + ".peel.begin");
  InsertBot->setName(Header->getName() + ".peel.next");
  NewPreHeader->setName(PreHeader->getName() + ".peel.newph");

  ValueToValueMapTy LVMap;

  // If we have branch weight information, we'll want to update it for the
  // newly created branches.
  BranchInst *LatchBR =
      cast<BranchInst>(cast<BasicBlock>(Latch)->getTerminator());
  unsigned HeaderIdx = (LatchBR->getSuccessor(0) == Header ? 0 : 1);

  uint64_t TrueWeight, FalseWeight;
  uint64_t ExitWeight = 0, BackEdgeWeight = 0;
  if (LatchBR->extractProfMetadata(TrueWeight, FalseWeight)) {
    ExitWeight = HeaderIdx ? TrueWeight : FalseWeight;
    BackEdgeWeight = HeaderIdx ? FalseWeight : TrueWeight;
  }

  VSet toClean;
  ValueToValueMapTy VMap;
  // For each peeled-off iteration, make a copy of the loop.
  for (unsigned Iter = 0; Iter < PeelCount; ++Iter) {
    SmallVector<BasicBlock *, 8> NewBlocks;

    // The exit weight of the previous iteration is the header entry weight
    // of the current iteration. So this is exactly how many dynamic iterations
    // the current peeled-off static iteration uses up.
    // FIXME: due to the way the distribution is constructed, we need a
    // guard here to make sure we don't end up with non-positive weights.
    if (ExitWeight < BackEdgeWeight)
      BackEdgeWeight -= ExitWeight;
    else
      BackEdgeWeight = 1;

    cloneLoopBlocks(L, Iter, InsertTop, InsertBot, Exit,
                    NewBlocks, LoopBlocks, VMap, LVMap, LI);
    updateBranchWeights(InsertBot, cast<BranchInst>(VMap[LatchBR]), Iter,
                        PeelCount, ExitWeight);

    InsertTop = InsertBot;
    InsertBot = SplitBlock(InsertBot, InsertBot->getTerminator(), DT, LI);
    InsertBot->setName(Header->getName() + ".peel.next");

    F->getBasicBlockList().splice(InsertTop->getIterator(),
                                  F->getBasicBlockList(),
                                  NewBlocks[0]->getIterator(), F->end());

    // Remap to use values from the current iteration instead of the
    // previous one.
    remapInstructionsInBlocks(NewBlocks, VMap);

    // TODO
    //Remove chunck/inst with a deg <= Iter (except -1 which is infinity)
    toClean = mergeVSet(toClean, updateLoopBody(L, Iter+1, mapLoopDeg, VMap, SE,
                                                DT, PDT, LI));
    LoopBlocks.clear();
    LoopBlocks.perform(LI);

    L->print(dbgs());
  }

  // Now adjust the phi nodes in the loop header to get their initial values
  // from the last peeled-off iteration instead of the preheader.
  for (BasicBlock::iterator I = Header->begin(); isa<PHINode>(I); ++I) {
    PHINode *PHI = cast<PHINode>(I);
    Value *NewVal = PHI->getIncomingValueForBlock(Latch);
    Instruction *LatchInst = dyn_cast<Instruction>(NewVal);
    if (LatchInst && L->contains(LatchInst))
      NewVal = LVMap[LatchInst];

    PHI->setIncomingValue(PHI->getBasicBlockIndex(NewPreHeader), NewVal);
  }

  // FIXME TO optimize with a pair! ↓
  /* DEBUG(dbgs() <<"Cleaning Block after!…\n"); */
  /* for (auto VV = toClean.begin(), E = toClean.end(); VV != E; ++VV) { */
  /*   Value* V = *VV; */
  /*   if(BasicBlock* BB = dyn_cast<BasicBlock>(V)){ */
  /*     DEBUG(dbgs() <<"Removing " << *V <<"…\n"); */
  /*     for(BasicBlock::iterator LI = BB->begin(), LE = BB->end(); LI != LE; */
  /*         ++LI){ */
  /*       Instruction &I = *LI; */
  /*       Instruction *NewInst = cast<Instruction>(VMap[&I]); */
  /*       /1* BB->dump(); *1/ */
  /*       DEBUG(dbgs() <<"ReplaceAllUsesWith " << *NewInst <<"\n"); */
  /*       I.replaceAllUsesWith(NewInst); // With the last cloned value for I… */
  /*       DEBUG(dbgs() <<"Try isa<TerminatorInst>…!\n"); */
  /*       if(!isa<TerminatorInst>(&I)) */
  /*         I.eraseFromParent(); */
  /*     } */
  /*     BB->eraseFromParent(); */
  /*     DEBUG(dbgs() <<"Removed!\n"); */
  /*   } */
  /* } */

  DEBUG(dbgs() <<"Cleaning Phi!…\n");
  for (auto VV = toClean.begin(), E = toClean.end(); VV != E; ++VV) {
    Value* V = *VV;
    if(Instruction* I = dyn_cast<Instruction>(V)){
      DEBUG(dbgs() <<"Removing " << *V <<"…\n");
      I->eraseFromParent();
      DEBUG(dbgs() <<"Removed!\n");
    }
  }
  // FIXME  ↑

  // Adjust the branch weights on the loop exit.
  if (ExitWeight) {
    MDBuilder MDB(LatchBR->getContext());
    MDNode *WeightNode =
        HeaderIdx ? MDB.createBranchWeights(ExitWeight, BackEdgeWeight)
                  : MDB.createBranchWeights(BackEdgeWeight, ExitWeight);
    LatchBR->setMetadata(LLVMContext::MD_prof, WeightNode);
  }

  // If the loop is nested, we changed the parent loop, update SE.
  if (Loop *ParentLoop = L->getParentLoop())
    SE->forgetLoop(ParentLoop);

  return true;
}/*}-}*/
