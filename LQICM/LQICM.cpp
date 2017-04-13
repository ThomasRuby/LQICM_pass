//===-- LQICM.cpp - Loop Quasi-Invariant Chunk Motion Pass ------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
//===----------------------------------------------------------------------===//
//
//
//===----------------------------------------------------------------------===//

#include "./LQICM.h"
#include "./LQICMUtils.h"

/* #include "llvm/ADT/Statistic.h" */
/* #include "llvm/Analysis/LoopIterator.h" */
/* #include "llvm/Analysis/LoopPass.h" */
/* #include "llvm/Analysis/ScalarEvolution.h" */
/* #include "llvm/Analysis/TargetTransformInfo.h" */
/* #include "llvm/IR/BasicBlock.h" */
/* #include "llvm/IR/Dominators.h" */
/* #include "llvm/IR/MDBuilder.h" */
/* #include "llvm/IR/Metadata.h" */
/* #include "llvm/IR/Module.h" */
/* #include "llvm/Support/Debug.h" */
/* #include "llvm/Support/raw_ostream.h" */
/* #include "llvm/Transforms/Scalar.h" */
/* #include "llvm/Transforms/Utils/BasicBlockUtils.h" */
/* #include "llvm/Transforms/Utils/Cloning.h" */
/* #include "llvm/Transforms/Utils/LoopUtils.h" */

#include "llvm/Analysis/ValueTracking.h"
using namespace llvm;

#define DEBUG_TYPE "lqicm"


// Function from LQICM
/* static bool inSubLoop(BasicBlock *BB, Loop *CurLoop, LoopInfo *LI); */
static bool isNotUsedInLoop(const Instruction &I, const Loop *CurLoop,/*{-{*/
                            const LoopSafetyInfo *SafetyInfo);
static bool sink(Instruction &I, const LoopInfo *LI, const DominatorTree *DT,
                 const Loop *CurLoop, AliasSetTracker *CurAST,
                 const LoopSafetyInfo *SafetyInfo);
static bool isSafeToExecuteUnconditionally(const Instruction &Inst,
                                           const DominatorTree *DT,
                                           const Loop *CurLoop,
                                           const LoopSafetyInfo *SafetyInfo,
                                           const Instruction *CtxI = nullptr);
static bool pointerInvalidatedByLoop(Value *V, uint64_t Size,
                                     const AAMDNodes &AAInfo,
                                     AliasSetTracker *CurAST);
static Instruction *
CloneInstructionInExitBlock(Instruction &I, BasicBlock &ExitBlock, PHINode &PN,
                            const LoopInfo *LI,
                            const LoopSafetyInfo *SafetyInfo);/*}-}*/

// Our functions
static bool isWellFormedFork(BasicBlock* Then, BasicBlock* Else, Loop* CurLoop,
                             PostDominatorTree* PDT, DominatorTree* DT);
static Relation* computeRelationLoop(DomTreeNode *N, MapChunk* mapChunk,
                                     AliasAnalysis *AA, LoopInfo *LI,
                                     DominatorTree *DT, Loop *CurLoop,
                                     AliasSetTracker *CurAST, LoopSafetyInfo
                                     *SafetyInfo, DependenceInfo *DI,
                                     PostDominatorTree *PDT, std::vector<Value*>
                                     *OC);

bool myCanSinkOrHoistInst(Instruction &I, AAResults *AA, DominatorTree *DT,
                              Loop *CurLoop, AliasSetTracker *CurAST,
                              LoopSafetyInfo *SafetyInfo) {
  // Loads have extra constraints we have to verify before we can hoist them.
  // FIXME
  if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
    return false;
  } else if (CallInst *CI = dyn_cast<CallInst>(&I)) {
    // Don't sink or hoist dbg info; it's legal, but not useful.
    if (isa<DbgInfoIntrinsic>(I))
      return false;

    // Don't sink calls which can throw.
    if (CI->mayThrow())
      return false;

    // Handle simple cases by querying alias analysis.
    FunctionModRefBehavior Behavior = AA->getModRefBehavior(CI);
    if (Behavior == FMRB_DoesNotAccessMemory)
      return true;
    if (AliasAnalysis::onlyReadsMemory(Behavior)) {
      // A readonly argmemonly function only reads from memory pointed to by
      // it's arguments with arbitrary offsets.  If we can prove there are no
      // writes to this memory in the loop, we can hoist or sink.
      if (AliasAnalysis::onlyAccessesArgPointees(Behavior)) {
        for (Value *Op : CI->arg_operands())
          if (Op->getType()->isPointerTy() &&
              pointerInvalidatedByLoop(Op, MemoryLocation::UnknownSize,
                                       AAMDNodes(), CurAST))
            return false;
        return true;
      }
      // If this call only reads from memory and there are no writes to memory
      // in the loop, we can hoist or sink the call as appropriate.
      bool FoundMod = false;
      for (AliasSet &AS : *CurAST) {
        if (!AS.isForwardingAliasSet() && AS.isMod()) {
          FoundMod = true;
          break;
        }
      }
      if (!FoundMod)
        return true;
    }

    // FIXME: This should use mod/ref information to see if we can hoist or
    // sink the call.

    return false;
  }

  // Only these instructions are hoistable/sinkable. FIXME
  if (!isa<BinaryOperator>(I) && !isa<CastInst>(I) && !isa<SelectInst>(I) &&
      !isa<CmpInst>(I) &&
      /* !isa<InsertElementInst>(I) && !isa<ExtractElementInst>(I) && */
      /* !isa<ShuffleVectorInst>(I) && !isa<ExtractValueInst>(I) && */
      !isa<InsertValueInst>(I))
    return false;

  // SafetyInfo is nullptr if we are checking for sinking from preheader to
  // loop body. It will be always safe as there is no speculative execution.
  if (!SafetyInfo)
    return true;

  // TODO: Plumb the context instruction through to make hoisting and sinking
  // more powerful. Hoisting of loads already works due to the special casing
  // above.
  return isSafeToExecuteUnconditionally(I, DT, CurLoop, SafetyInfo, nullptr);
}

// Return Relation composed for the given BasicBlock/*{-{*/
static Relation* computeRelation(BasicBlock* BB, MapDeg* mapDeg , MapRel*
                                 mapRel, AliasAnalysis *AA, DominatorTree
                                 *DT,Loop *CurLoop,AliasSetTracker *CurAST,
                                 LoopSafetyInfo *SafetyInfo, std::vector<Value*>
                                 *OC){
    Relation *RB = new Relation(BB);
    for (BasicBlock::iterator II = BB->begin(), E = BB->end(); II != E;) {
      Instruction &I = *II++;
      DEBUG(dbgs() << "Treating: " << I << " … " << '\n');

      if (isa<PHINode>(&I)) // Phi in/out already took into account 
        continue;

      // Debug infos … ↓
      if (!myCanSinkOrHoistInst(I, AA, DT, CurLoop, CurAST, SafetyInfo))
        DEBUG(dbgs() << " canNotSinkOrHoistInst " << '\n');
      if (!isSafeToExecuteUnconditionally( //TODO ça il faut voir …
          I, DT, CurLoop, SafetyInfo,
          CurLoop->getLoopPreheader()->getTerminator()))
        DEBUG(dbgs() << " isNotSafeToExecuteUnconditionnally " << '\n');
      if (isNotUsedInLoop(I,CurLoop,SafetyInfo))
        DEBUG(dbgs() << " isNotUsedInLoop " << '\n');
      // End Debug infos … ↑

      if (myCanSinkOrHoistInst(I, AA, DT, CurLoop, CurAST, SafetyInfo) &&
          isSafeToExecuteUnconditionally( //TODO ça il faut voir …
            I, DT, CurLoop, SafetyInfo,
            CurLoop->getLoopPreheader()->getTerminator()))
        (*mapDeg)[&I]=0;
      else {
        (*mapDeg)[&I]=-1;
        if(!isa<BranchInst>(&I))
          RB->setAnchor(true);
      }
      OC->push_back(&I);
      DEBUG(dbgs() << "(*mapDeg)[&I]= " << (*mapDeg)[&I] << '\n');

      Relation *RI = new Relation(&I);
      // Save relation with instruction
      (*mapRel)[&I] = RI;
      DEBUG(RI->dump(dbgs()));
      DEBUG(dbgs() << " Composition…" << '\n');
      RB = RB->composition(RI);
      DEBUG(RB->dump(dbgs()));
    }//End of For II in BB
    return RB;
}/*}-}*/

bool IDominatesJ(Value* I, Value* J, DominatorTree* DT, Value* head){
  bool IdominatesJ = false;
  DEBUG(dbgs() << " In IDominatesJ…\n");
  if (Instruction *II = dyn_cast<Instruction>(I)) {
    if (Instruction *IM = dyn_cast<Instruction>(J)) {
      IdominatesJ = DT->dominates(II,IM);
    } //End if dyn_cast<Instruction>(J)
    else {
      DEBUG(dbgs() << " INFO: Failed to cast J to Instruction!" << 
            " Is an InnerBlock?\n");
      if (BasicBlock *BIM = dyn_cast<BasicBlock>(J)) {
        DEBUG(dbgs() << " INFO: Yes it's " << BIM->getName() << '\n');
        IdominatesJ = DT->dominates(II,BIM);
      } else 
        DEBUG(errs() << " ERROR: Failed to cast J to BasicBlock!");
    }
  } //End if dyn_cast<Instruction>(I)
  else {
    DEBUG(dbgs() << " INFO: Failed to cast I to Instruction! Is an InnerBlock?");
    if(I == head)
      DEBUG(dbgs() << "it's the CurLoop then it dominates everything\n");
    if (BasicBlock *BI = dyn_cast<BasicBlock>(I)) {
      // TODO reverse domination here?! 
      // FIXME What to do here IMPORTANT!
      // IdominatesMax = DT->dominates(IM,BI); Kind…
    } else 
      DEBUG(errs() << " ERROR: Failed to cast I to BasicBlock!");
  }
  return IdominatesJ;
}

// Dinamically computes the invariance degrees/*{-{*/
static int computeDeg(Chunk* chunk, Value* I, DominatorTree *DT, Value *head){
  MapDeg* mapDeg = chunk->getMapDeg();
  MapRel* mapRel = chunk->getMapRel();
  DEBUG(dbgs() << " Computation degree of " << *I << '\n');
  if((*mapDeg)[I]){
    DEBUG(dbgs() << "\n\tAlready in mapDeg with deg = " << (*mapDeg)[I] << '\n');
    return (*mapDeg)[I];
  }
  else{
    (*mapDeg)[I]=-1;
    if(!mapRel->count(I)){
      DEBUG(dbgs() << "\nINFO… " << I << " has not been visited or is not in this chunk " << chunk->getName() << '\n');
      // Means it was initialized outside the loop
      (*mapDeg)[I] = 1;
      DEBUG(dbgs() << "\t deg = " << (*mapDeg)[I] << '\n');
      return 1;
    }
    else{
      Relation* RI = (*mapRel)[I];
      DEBUG(dbgs() << "\tRelation found: " << '\n');
      DEBUG(RI->dump(dbgs()));
      if(RI->getDep().empty()){ // Empty dep
        (*mapDeg)[I] = 1;
        DEBUG(dbgs() << "\tNo dependence →  deg = " << (*mapDeg)[I]);
        return 1;
      }
      else{
        Value* instMax;
        int degMax=-1;
        bool isVariant = false;
        bool isOnlyOutOfLoop = true;
        VSet inInst = RI->getIn();
        DEBUG(dbgs() << "\tCompute deg on dependencies");
        DEBUG(dbgs() << "\tVariables In:" << '\n'<< '\t');
        DEBUG(printValues(inInst,dbgs()));
        // Search for the max deg of inputs variables
        for (auto VV = inInst.begin(), E = inInst.end(); VV != E; ++VV) {
          Value* V = *VV;
          DEBUG(dbgs() << "\tValue " << V << " in inputs…\n");
          VSet relations = searchForRelationsWithVAsOutput(V,mapRel);
          // Case 1 : there is no relations with V as output variable
          if(relations.empty()){
            DEBUG(dbgs() << "\tThere is no relation which has " << V << 
                  " in outputs… \n");
            // If it's in mapDeg, then it has been visited in the loop
            if((*mapDeg).count(V)){
              DEBUG(dbgs() << "\tV is in the loop…");
              // If it's not an anchor 
              if((*mapDeg)[V]!=-1){
                DEBUG(dbgs() << "\tV is not an anchor and its value = " <<
                      (*mapDeg)[V] << "…");
                // Then init to 1 and update max infos
                (*mapDeg)[I]=1;
                if((*mapDeg)[I]>=degMax){
                  degMax=(*mapDeg)[I];
                  instMax = V;
                }
                continue;
              } else {
                DEBUG(dbgs() << "\tV is an anchor and the max… finish\n");
                (*mapDeg)[I]=-1;
                return -1;
                // If it's an anchor then we already found the max, we can stop
              }
            } else{
              // If it's not a value in the loop
              DEBUG(dbgs() << "\tV is outside of the loop… ");
              // Then init to 1 and update max infos
              (*mapDeg)[I]=1;
              if((*mapDeg)[I]>=degMax){
                degMax=(*mapDeg)[I];
                instMax = V;
              }
              continue;
            }
          }
          DEBUG(dbgs() << "\tThere is " << relations.size() << " relations:");
          // TODO Optimize me!
          for(auto RR = relations.begin(), RRE = relations.end(); RR != RRE; ++RR){
            Value* VR = *RR; 
            DEBUG(dbgs() << " Relation which has " << V << " in outputs ");
            DEBUG((*mapRel)[VR]->dump(dbgs()));
            // TODO Remove this head and the value itself from here…
            if (VR == head){
              DEBUG(dbgs() << " This is the Relation of the Loop itself! ");
              continue;
            } else if (VR == I){
              DEBUG(dbgs() << " This is the Relation of the Chunk itself! ");
              continue;
            } else {
              (*mapDeg)[I]=computeDeg(chunk,VR,DT,head);
              DEBUG(dbgs() << " out of rec call of computeDeg…" << '\n');
            }
            if ((*mapDeg)[I] == -1){
              // If it's an anchor then we already found the max, we can stop
              DEBUG(dbgs() << " new value is inf… finish" << '\n');
              return -1;
            } 
            if((*mapDeg)[I]>=degMax){
              DEBUG(dbgs() << " new value is max…" << '\n');
              degMax=(*mapDeg)[I];
              instMax = VR;
            } 
          }
          if(isVariant)
            break;
        }

        //Optimize me TODO
        if(!(*mapDeg).count(instMax)){
          DEBUG(dbgs() << "\n The max is outside then return 1");
          return 1;
        }

        DEBUG(dbgs() << "\n is " << I << "\ndominates " <<
              instMax << '\n');
        bool IdominatesMax = IDominatesJ(I,instMax,DT,head);
        DEBUG(dbgs() << "\n" << IdominatesMax);
        if(degMax!=-1 && IdominatesMax) // I avant instMax
          (*mapDeg)[I]=degMax+1;
        else (*mapDeg)[I]=degMax;
        DEBUG(dbgs() << "\t deg = " << (*mapDeg)[I] << '\n');
        return (*mapDeg)[I];
      } //End else no dependencies
    } //End else no I in mapRel
  } //End else mapDeg[I] already computed
}/*}-}*/

// Sub functions
static MapDeg* computeDeg(Chunk* chunk, std::vector<Value*> *OC, DominatorTree
                          *DT, Value* head){
    for(Value* I : *OC){
      int deg = computeDeg(chunk,I,DT,head);
      DEBUG(dbgs() << "\nfinal result for "<< I << " = " << deg);
      DEBUG(dbgs() << '\n');
    }
} 

// Sub function
static MapDeg* computeDeg(Chunk* chunk, BasicBlock* BB, DominatorTree *DT,
                          Value* head){
    for (BasicBlock::iterator II = BB->begin(), E = BB->end(); II != E;) {
      Instruction &I = *II++;
      int deg = computeDeg(chunk,&I,DT,head);
      DEBUG(dbgs() << "\nfinal result for "<< I.getName() << " = " << deg);
      DEBUG(dbgs() << '\n');
    }
}

static bool isGuaranteedToExecute(BasicBlock* BB, Loop* CurLoop,/*{-{*/
                                        DominatorTree* DT){
  if (BB != CurLoop->getHeader()) {
    // Check loop exiting blocks.
    SmallVector<BasicBlock*, 8> CurrentLoopExitingBlocks;
    CurLoop->getExitingBlocks(CurrentLoopExitingBlocks);
    for (BasicBlock *CurrentLoopExitingBlock : CurrentLoopExitingBlocks)
      if (!DT->dominates(BB, CurrentLoopExitingBlock))
        return false;
  }

  return true;
}/*}-}*/

// Is a well formed fork for compositing ?/*{-{*/
static bool isWellFormedFork(BasicBlock* Then, BasicBlock* Else, Loop* CurLoop,
                             PostDominatorTree* PDT, DominatorTree* DT){

  if (CurLoop->contains(Then) && CurLoop->contains(Else)){
    if(BasicBlock *End = PDT->findNearestCommonDominator(Then,Else)){
      DEBUG(dbgs() << "Common PostDominator " << End->getName() << " … " << '\n');
      // Is End sure to be executed? In the Loop? TODO
      // Same question in LQICMPeel.cpp:114 we require that the loop only have a
      // single exit block…
      // FIXME IMPORTANT
      /* if(isGuaranteedToExecute(End,CurLoop,DT)) */
        return true;
    }
    else{
      DEBUG(dbgs() << " If not well formed " << '\n');
      return false;
    }
  }
  else{
    DEBUG(dbgs() << "Break of the loop somewhere " <<  " … " << '\n');
  }
}/*}-}*/

// Return the first BB in the Body of the current loop
static BasicBlock* getFirstBodyOfLoop(Loop *CurLoop){/*{-{*/
 BasicBlock* head = CurLoop->getHeader();
  const TerminatorInst *TInst = head->getTerminator();
  unsigned nbSucc = TInst->getNumSuccessors();
  bool found = false;
  unsigned i = 0;
  BasicBlock *next = TInst->getSuccessor(i);
  while(!found){
    if(next!=CurLoop->getExitBlock())
      found=true;
    else{
      i++;
      next = TInst->getSuccessor(i);
    }
  }
  DEBUG(dbgs() << " First body block is :" << next->getName() << '\n');
  return next;
}/*}-}*/

// Compute recursively the relation (block by block) from BB to End
// TODO too much useless args… it's a prototype…/*{-{*/
static Relation* computeRelationBBInLoop(BasicBlock *BB, BasicBlock *End,
                                         Relation *RPHI, MapChunk* mapChunk,
                                         Chunk* currentChunk, AliasAnalysis *AA,
                                         LoopInfo *LI, DominatorTree *DT, Loop
                                         *CurLoop, AliasSetTracker *CurAST,
                                         LoopSafetyInfo *SafetyInfo,
                                         DependenceInfo *DI, PostDominatorTree
                                         *PDT, std::vector<Value*> *OC){
  DEBUG(dbgs() << "\n---- computeRelationBBInLoop ----\n ");
  DEBUG(dbgs() << "INFO ---- BB = " << *BB <<'\n');
  DEBUG(dbgs() << "INFO ---- End = " << *End <<'\n');

  Relation *RB = new Relation();

  if(BB == End){
    DEBUG(errs() << "ERROR ---- BB = End it shouldn't be! \n");
    return nullptr;
  }
  
  // If we are here, it (should) works
  /* Value* head = dyn_cast<Value>(CurLoop->getHeader()); */
  Value* bb = dyn_cast<Value>(BB);

  // We are in the main loop's chunk
  /* Chunk* currentChunk = (*mapChunk)[head]; */
  MapDeg *mapDeg = currentChunk->getMapDeg();
  MapRel *mapRel = currentChunk->getMapRel();

  /* DEBUG(dbgs() << "TEST ---- Relation of " << *bb << " is already in the map?" */
  /*       << '\n'); */
  /* if((*mapRel)[bb]){ */
  /*   DEBUG(dbgs() << "Yes!" << '\n'); */
  /*   return (*mapRel)[bb]; */
  /* } */

  // Not in Loop ?
  if (!CurLoop->contains(BB)){
    DEBUG(dbgs() << "---- Not In Current Loop " << '\n');
    // Return empty Relation
    return RB;
  }


  // This case find the LoopRelation if the Block encountered is an inner Loop/*{-{*/
  // header
  if(inSubLoop(BB, CurLoop, LI)){
    DEBUG(dbgs() << "In subLoop! " << '\n');
    Loop* InnerLoop = LI->getLoopFor(BB);
    if(InnerLoop->getHeader()==BB){
      // Add phi entry relations first !!!
      Relation *RL = new Relation();
      Relation* inneRPHI = getPHIRelations(InnerLoop,currentChunk,OC,true);
      RL = RL->composition(inneRPHI);

      if(Value* InnerHead = dyn_cast<Value>(InnerLoop->getHeader())){
        if(!(*mapChunk)[InnerHead]){
          DEBUG(errs() << " ERROR! Inner Loop non analyzed → abort" <<
                InnerHead->getName() <<'\n');

          return nullptr;
          /* OC->push_back(InnerHead); // FIXME redo OC regarding to chunks */
          /* (*currentChunk->getMapDeg())[InnerHead] = -1; */
        } else {

          Chunk* innerLoopChunk = (*mapChunk)[InnerHead];
          if(innerLoopChunk->getType() == Chunk::ERROR){
            DEBUG(dbgs() << " ERROR! Relation not found for Loop with Head = " <<
                  InnerHead <<'\n');
            // FIXME should throw an exception or just stop the analysis here
            return nullptr;
          }
          DEBUG(dbgs() << " Relation found for Loop with Head = " <<
                InnerHead->getName() <<'\n');
          DEBUG(innerLoopChunk->getRel()->dump(dbgs()));
          (*currentChunk->getMapRel())[InnerHead] = innerLoopChunk->getRel();
          /* (*(*mapChunkRel)[head])[InnerHead] = innerLoopChunk->getRel(); */

          // Initialization: we suppose the loop is hoistable
          (*currentChunk->getMapDeg())[InnerHead] = 0;
          /* (*(*mapChunkDeg)[head])[InnerHead] = 0; */ 

          OC->push_back(InnerHead); // FIXME redo OC regarding to chunks
          RL = RL->composition(innerLoopChunk->getRel());
        }

        // Continue by treating while.end
        if(BasicBlock* WhileEnd = InnerLoop->getExitBlock()){
          DEBUG(dbgs() << " INFO: Exit Loop Block is :" << WhileEnd->getName()
                << '\n');
          Relation* RNextPHI =
            getPHIRelations(InnerLoop->getHeader(),WhileEnd,mapRel);
          DEBUG(dbgs() << " Composition with out phi LCSSA…" << '\n');
          RL = RL->composition(RNextPHI);
          DEBUG(RB->dump(dbgs()));
          if(WhileEnd != End){
            Relation* RWEND = computeRelationBBInLoop(WhileEnd, End, RPHI,
                                                      mapChunk, currentChunk,
                                                      AA, LI, DT, CurLoop,
                                                      CurAST, SafetyInfo, DI,
                                                      PDT, OC);
            if(RWEND)
              RB = RL->composition(RWEND);
            else {
              DEBUG(dbgs() << " ERROR: in WhilEnd " << *WhileEnd << '\n');
              currentChunk->setType(Chunk::ERROR);
              return nullptr;
            }
          } else{
            DEBUG(dbgs() << WhileEnd->getName() << " DEBUG end of chunk " <<
                  End->getName() << '\n');
            RB = RB->composition(RL);
            // If there is some phi in End take into account here the assignements
            // If it's the header of the current loop, they are already computed
            if(End == CurLoop->getHeader())
              RB = RB->composition(RPHI);
          }
        }
        else
          DEBUG(dbgs() << " WARN: Fail to find unique While.end?" << '\n');
        
      } else
        DEBUG(dbgs() << " WARN: Fail cast InnerHead to Value! :" << '\n');
      return RB;
    }
  }/*}-}*/

  // If it exists a Chunk starting with this block then we are in an inner
  // chunk/*{-{*/
  // of the main loop which is not an inner loop (for the moment it could only
  // be a "if-then-else" chunk…)
  if((*mapChunk)[bb]){
    DEBUG(dbgs() << " BB " << bb << " is the start of an inner Chunk\n");
    //TODO manage the following cases
    // 1 it's a branch -> then just use the corresponding chunk
    // 2 it's the beggining of a normal chunk (peeled thing?) juste take his
    //
    Chunk* newChunk = (*mapChunk)[bb];
    if(newChunk->isPeeled()){
      DEBUG(dbgs() << " Relation found for a peeled loop with top = " <<
            bb->getName() <<'\n');
      /* DEBUG(newChunk->getRel()->dump(dbgs())); */
      // Initialization of deg of the peeled chunk in the current chunk
      (*currentChunk->getMapDeg())[bb] = 0;
      (*currentChunk->getMapRel())[bb] = newChunk->getRel();

      OC->push_back(bb); // FIXME redo OC regarding to chunks
      RB = newChunk->getRel();
      
      BasicBlock* WhileEnd = newChunk->getEnd();
      // Continue after the chunk
      if(newChunk->getEnd() != End){
        DEBUG(dbgs() << WhileEnd->getName() << " Let's continue with " <<
              WhileEnd->getName() << '\n');
        Relation* RWEND = computeRelationBBInLoop(WhileEnd, End, RPHI, mapChunk,
                                                  currentChunk, AA, LI, DT, CurLoop,
                                                  CurAST, SafetyInfo, DI, PDT,
                                                  OC);
        if(RWEND)
          return RWEND;
        else {
          DEBUG(errs() << " ERROR: in WhilEnd " << *WhileEnd << '\n');
          return nullptr;
        }
      } else{
        DEBUG(dbgs() << WhileEnd->getName() << " DEBUG end of chunk " <<
              End->getName() << '\n');
        // If there is some phi in End take into account here the assignements
        // If it's the header of the current loop, they are already computed
        if(End == CurLoop->getHeader())
          RB = RB->composition(RPHI);
      }
    } else {
      DEBUG(dbgs() << " INFO: switch to inner chunk " << newChunk->getName() <<
            '\n');
      // Means we are in an inner chunk not analyzed yet
      currentChunk = newChunk;
      // already computed Relation and Degree and continue by taking its End BB.
      // Then don't touch the mapRel of the loop but of the current sub chunk
      mapRel = currentChunk->getMapRel();
      mapDeg = currentChunk->getMapDeg();

    }
  }/*}-}*/

  DEBUG(dbgs() << " INFO: In chunk :" << currentChunk->getName() << '\n');
  if(CurLoop->isLoopExiting(BB)){
    DEBUG(errs() << " ERROR: Loop form not managed yet… " << BB->getName() << '\n');
    return nullptr;
  }

  // If normal BB compute the corresponding relation
  RB = computeRelation(BB, mapDeg, mapRel, AA, DT,
                       CurLoop, CurAST, SafetyInfo, OC);

  // If there are several successors… if then else…
  TerminatorInst *TInst = BB->getTerminator();
  unsigned nbSucc = TInst->getNumSuccessors();
  // TODO if more than 2 we should manage by checking the commonPostDominator
  // and compute the sum anyway
  // FIXME Maybe using BranchInst information
  if(nbSucc==2){
    BasicBlock *Then = TInst->getSuccessor(0);
    BasicBlock *Else = TInst->getSuccessor(1);
      if(isWellFormedFork(Then,Else,CurLoop,PDT,DT)){
        BasicBlock *IfEnd = PDT->findNearestCommonDominator(Then,Else);
        DEBUG(dbgs() << " INFO: Exit If Block of if is :" << IfEnd->getName() <<
              '\n');

        if(!CurLoop->contains(IfEnd)){
          DEBUG(errs() << " ERROR: Exit If Block out of the loop! \n");
          return nullptr;
        }

        // No deg computed inside. Only the relation of if matters
        // One Relation for each branch
        // DEPRECATED
        /* MapRel *mapThenRel = new MapRel(); */
        /* MapRel *mapElseRel = new MapRel(); */
        std::vector<Value*> OCif;

        Value* VThen = dyn_cast<Value>(Then);
        Value* VElse = dyn_cast<Value>(Else);
        
        // Every relations of the branches will be in the corresponding map
        Chunk* ThenChunk = new Chunk(Then->getName()); // Creates mapRel
        ThenChunk->setStart(Then);
        ThenChunk->setEnd(IfEnd);
        ThenChunk->setType(Chunk::BRANCH);
        (*mapChunk)[VThen] = ThenChunk;

        Chunk* ElseChunk = new Chunk(Else->getName()); // Creates mapRel
        ElseChunk->setStart(Else);
        ElseChunk->setEnd(IfEnd);
        ElseChunk->setType(Chunk::BRANCH);
        (*mapChunk)[VElse] = ElseChunk;

        // DEPRECATED
        /* (*mapChunkRel)[VThen] = mapThenRel; */
        /* (*mapChunkRel)[VElse] = mapElseRel; */

        // it could have some phi to take into account! IMPORTANT
        DEBUG(dbgs() << " Computing RThenPHI : " << Then->getName() << " to " <<
              IfEnd->getName() << '\n');
        Relation *RThenPHI = new Relation();
        if(Then != IfEnd)
          RThenPHI = getPHIRelations(BB,Then,mapRel);

        DEBUG(dbgs() << " Computing RElsePHI : " << Then->getName() << " to " <<
              IfEnd->getName() << '\n');
        Relation *RElsePHI = new Relation();
        if(Else != IfEnd)
          RElsePHI = getPHIRelations(BB,Else,mapRel);


        // Recursive call on each branch
        Relation* RThen = new Relation();
        DEBUG(dbgs() << " Computing RThen : " << Then->getName() << " to " <<
              IfEnd->getName() << '\n');

        // DEPRECATED
        /* RThen->setStart(Then); */
        /* RThen->setEnd(IfEnd); */
        /* RThen->setBranch(true); */
        if(Then != IfEnd)
          RThen = computeRelationBBInLoop(Then, IfEnd, RPHI, mapChunk,
                                          ThenChunk, AA, LI, DT, CurLoop,
                                          CurAST, SafetyInfo, DI, PDT, &OCif);
        if(!RThen){
          DEBUG(errs() << " ERROR in RThen of: " << Then->getName() << '\n');
          ThenChunk->setType(Chunk::ERROR);
          return nullptr;
        }
        DEBUG(dbgs() << " Then : " << Then->getName() << '\n');
        DEBUG(RThen->dump(dbgs()));
        ThenChunk->setRel(RThen);

        Relation* RElse = new Relation();
        // DEPRECATED
        /* RElse->setStart(Else); */
        /* RElse->setEnd(IfEnd); */
        /* RElse->setBranch(true); */
        DEBUG(dbgs() << " Computing RElse : " << Else->getName() << " to " <<
              IfEnd->getName() << '\n');
        if(Else != IfEnd)
          RElse = computeRelationBBInLoop(Else, IfEnd, RPHI, mapChunk,
                                          ElseChunk, AA, LI, DT, CurLoop,
                                          CurAST, SafetyInfo, DI, PDT, &OCif);

        if(!RElse){
          DEBUG(errs() << " ERROR in RElse of: " << Else->getName() << '\n');
          ElseChunk->setType(Chunk::ERROR);
          return nullptr;
        }
        DEBUG(dbgs() << " Else : " << Else->getName() << '\n');
        DEBUG(RElse->dump(dbgs()));
        ElseChunk->setRel(RElse);

        // Add Phi entries
        DEBUG(dbgs() << " Composition RThenPHI ↓ " << Then->getName());
        DEBUG(RThenPHI->dump(dbgs()));
        DEBUG(dbgs() << " With RThen ↓ " << Then->getName());
        DEBUG(RThen->dump(dbgs()));
        RThen = RThenPHI->composition(RThen);

        DEBUG(dbgs() << " Composition RElsePHI ↓ " << Else->getName());
        DEBUG(RElsePHI->dump(dbgs()));
        DEBUG(dbgs() << " With RElse ↓ " << Else->getName());
        DEBUG(RElse->dump(dbgs()));
        RElse = RElsePHI->composition(RElse);
        
        
        Relation *RFork = new Relation();
        RThen->setEnd(IfEnd);
        RThen->setBranch(true);
        
        // Sum branchs
        RFork = RFork->composition(RThen->sumRelation(RElse));

        // Here RB is the relation of the If but we need to add conditions dep
        Relation *RCMP = getCondRelationsFromBB(BB,mapRel);
        if(RCMP)
          RFork->addDependencies(RCMP->getIn(),RFork->getOut());

        DEBUG(dbgs() << " FINAL Branch from " << TInst << '\n');
        DEBUG(RFork->dump(dbgs()));

        (*mapDeg)[TInst] = 0;
        (*mapRel)[TInst] = RFork;
        // Is this useless?
        // The sum will be added here, key = to TInst
        // FIXME Should we take the entire block with the TInst in the chunk?
        Chunk* branChunk = new Chunk(TInst->getName());
        branChunk->setStart(BB);
        branChunk->setEnd(IfEnd);
        branChunk->setRel(RFork);
        branChunk->setDegree(0);
        // usefull ? ↓
        (*branChunk->getMapRel())[VThen] = RThen;
        (*branChunk->getMapRel())[VElse] = RElse;
      
        (*mapChunk)[TInst] = branChunk;
        /* (*mapChunkRel)[TInst] = new MapRel(); */
        /* (*(*mapChunkRel)[TInst])[TInst] = RFork; */

        RB = RB->composition(RFork);

        if(IfEnd != End){
          Relation* Rcontinue = computeRelationBBInLoop(IfEnd, End, RPHI,
                                                        mapChunk, currentChunk,
                                                        AA, LI, DT, CurLoop,
                                                        CurAST, SafetyInfo, DI,
                                                        PDT, OC);
          if(!Rcontinue){
            DEBUG(dbgs() << " ERROR in Rcontinue of: " << IfEnd << '\n');
            return nullptr;
          }

          // Continue with the if.end block
          RB = RB->composition(Rcontinue);
        } else{
          // If there is some phi in End take into account here the assignements
          // If it's the header of the current loop, they are already computed
          if(End == CurLoop->getHeader())
            RB = RB->composition(RPHI);
        }
      }
      else {
        DEBUG(dbgs() << " WARN: Branch is not well formed for: " <<
              BB->getName() <<'\n');
      }
  }

  // If one Succ only
  else if(BasicBlock* Succ = BB->getUniqueSuccessor()){
    // End conditions of recursive call:
    // Needs to have only one successor going to the End block
    if(Succ == End){
      DEBUG(dbgs() << " Unique successor is :" <<
            End->getName() << '\n');
      // If there is some phi in End take into account here the assignements
      // If it's the header of the current loop, they are already computed
      if(End == CurLoop->getHeader())
        RB = RB->composition(RPHI);
      else{
        Relation* RNextPHI = getPHIRelations(BB,Succ,mapRel);
        DEBUG(dbgs() << " Composition with main relation…" << '\n');
        RB = RB->composition(RNextPHI);
        DEBUG(RB->dump(dbgs()));
      }
    } else {
      DEBUG(dbgs() << Succ->getName() << " DEBUG not equal? " << End->getName()
            << '\n');
      // Recursiv call on next BB and composition with the current
      //
      Relation* Rnext = computeRelationBBInLoop(Succ, End, RPHI, mapChunk,
                                                currentChunk, AA, LI, DT,
                                                CurLoop, CurAST, SafetyInfo, DI,
                                                PDT, OC);
      if(!Rnext){
        DEBUG(errs() << " ERROR in Rnext of: " << *Succ << '\n');
        return nullptr;
      }
      RB = RB->composition(Rnext);
    }
  } else {
    DEBUG(errs() << " ERROR Several successors for " << *BB << '\n');
  }

  return RB;
}/*}-}*/

/// Compute Relation for the Loop with fixpoint and cond correction/*{-{*/
static Relation* computeRelationLoop(DomTreeNode *N, MapChunk* mapChunk,
                                     AliasAnalysis *AA, LoopInfo *LI,
                                     DominatorTree *DT, Loop *CurLoop,
                                     AliasSetTracker *CurAST, LoopSafetyInfo
                                     *SafetyInfo, DependenceInfo *DI,
                                     PostDominatorTree *PDT,std::vector<Value*>
                                     *OC) {

    DEBUG(dbgs() <<"\n************ComputeRelationLoop***********\n");
    BasicBlock* Head = CurLoop->getHeader();
    if(Value* head = dyn_cast<Value>(Head)){

      // Check if there is not several exitblock here and abort if so
      // We will consider this case in the futur! TODO
      if(!CurLoop->getExitBlock()){
        DEBUG(dbgs() <<"WARN: severals exitBlock → Abort");
        NumLoopsManyExitB++;
        Relation* RL = new Relation(Head);
        return RL;
      }

      if(!CurLoop->isLoopExiting(Head)){
        DEBUG(dbgs() <<"WARN: not well formed for this analysis → Abort");
        NumLoopsManyExitB++;
        Relation* RL = new Relation(Head);
        return RL;
      }

      Chunk* loopChunk = (*mapChunk)[head];

      Relation *RPHI = getPHIRelations(CurLoop,loopChunk->getMapRel(),false);
      BasicBlock *FirstBody = getFirstBodyOfLoop(CurLoop);
      Relation *RL = computeRelationBBInLoop(FirstBody, Head, RPHI, mapChunk,
                                             loopChunk, AA, LI, DT, CurLoop,
                                             CurAST, SafetyInfo, DI, PDT, OC);
      if(!RL){
        return nullptr;
      }
      if(RL->isAnchor())
        DEBUG(dbgs() << " This Loop contains an anchor " << '\n');

      // Take the while.end into account
      DEBUG(dbgs() << " Fixpoint…" << '\n');
      RL = fixPoint(RL);
      DEBUG(RL->dump(dbgs()));

      Relation *RCMP = getCondRelationsFromBB(Head,loopChunk->getMapRel());
      RL->addDependencies(RCMP->getIn(),RL->getOut());
      DEBUG(dbgs() << " Condition correction… " << '\n');
      DEBUG(dbgs() << " FINAL LOOP OF DEPTH " << CurLoop->getLoopDepth() << 
            " and header = " << head->getName() <<'\n');
      DEBUG(RL->dump(dbgs()));
      // FIXME make it more clear↓
      /* (*loopChunk->getMapRel())[head] = RL; */
      // Should be only ↓
      loopChunk->setRel(RL);
      loopChunk->setAnchor(RL->isAnchor());
      // DEPRECATED
      /* (*(*mapChunkRel)[head])[head]=RL; */

      computeDeg(loopChunk, OC, DT,head);
      DEBUG(dbgs() << " MapDeg in chunk " << loopChunk->getName() << '\n');
      dumpMapDegOfOC(mapChunk,loopChunk->getMapDeg(),OC,dbgs());

      return RL;
    }
    else
      DEBUG(errs() << " Error dyn_cast Header in value " << '\n');
    return nullptr;
}/*}-}*/

PreservedAnalyses LQICMPass::run(Loop &L, LoopStandardAnalysisResults &AR,/*{-{*/
        LoopAnalysisManager &AM) {
  const auto &FAM =
      AM.getResult<FunctionAnalysisManagerLoopProxy>(L,AR).getManager();
  Function *F = L.getHeader()->getParent();

  auto *AA = FAM.getCachedResult<AAManager>(*F);
  auto *LI = FAM.getCachedResult<LoopAnalysis>(*F);
  auto *DT = FAM.getCachedResult<DominatorTreeAnalysis>(*F);
  /* auto *TLI = FAM.getCachedResult<TargetLibraryAnalysis>(*F); */
  auto *DI = FAM.getCachedResult<DependenceAnalysis>(*F);
  auto *PDT = FAM.getCachedResult<PostDominatorTreeAnalysis>(*F);
  auto *SE = FAM.getCachedResult<ScalarEvolutionAnalysis>(*F);
  assert((AA && LI && DT && SE) && "Analyses for LICM not available");

  LoopInvariantCodeMotion LICM;
  bool changed = LICM.runOnLoop(&L, AA, LI, DT, DI, PDT, SE, true);

  if (!changed)
    return PreservedAnalyses::all();

  // FIXME: There is no setPreservesCFG in the new PM. When that becomes
  // available, it should be used here.
  return getLoopPassPreservedAnalyses();
}/*}-}*/

char LegacyLQICMPass::ID = 0;
/* static RegisterPass<LegacyLQICMPass> X("lqicm", "Loop quasi-Invariant Code Motion"); */

// A way to register the pass
INITIALIZE_PASS_BEGIN(LegacyLQICMPass, "lqicm", "Loop quasi-Invariant Code Motion",  false, false)
INITIALIZE_PASS_DEPENDENCY(LoopPass)
INITIALIZE_PASS_DEPENDENCY(AAResultsWrapperPass)
INITIALIZE_PASS_DEPENDENCY(DependenceAnalysisWrapperPass)
INITIALIZE_PASS_DEPENDENCY(PostDominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass)
// initialize all passes which your pass needs
INITIALIZE_PASS_END(LegacyLQICMPass, "lqicm", "Loop quasi-Invariant Code Motion", false, false)

/* Pass *llvm::createLQICMPass() { return new LegacyLQICMPass(); } */


// An other way to register the pass…
static void registerLQICMPass(const PassManagerBuilder &,
                              legacy::PassManagerBase &PM){
  PM.add(createPromoteMemoryToRegisterPass());
  PM.add(createIndVarSimplifyPass());
  PM.add(createCFGSimplificationPass());
  PM.add(new AAResultsWrapperPass());
  PM.add(new DependenceAnalysisWrapperPass());
  PM.add(new PostDominatorTreeWrapperPass());
  PM.add(new LoopInfoWrapperPass());
  PM.add(new LegacyLQICMPass());
}
static RegisterStandardPasses
RegisterClangPass(PassManagerBuilder::EP_ModuleOptimizerEarly, registerLQICMPass);

int getDegMax(MapDeg *MD){/*{-{*/
  int degMax = -1;
  for(auto DD = MD->begin(), DDE = MD->end(); DD != DDE; ++DD){
    int deg = DD->second;
    if(deg>degMax)
      degMax=deg;
  }
  return degMax;
}/*}-}*/

///
bool LoopInvariantCodeMotion::runOnLoop(Loop *L, AliasAnalysis *AA,/*{-{*/
                                        LoopInfo *LI, DominatorTree *DT,
                                        DependenceInfo *DI,
                                        PostDominatorTree *PDT,
                                        ScalarEvolution *SE, bool DeleteAST) {
  bool Changed = false;

  assert(L->isLCSSAForm(*DT) && "Loop is not in LCSSA form.");

  // All verifications about the form here!
  if (!L->isLoopSimplifyForm()) { 
    DEBUG(
        dbgs() << "  Not unrolling loop which is not in loop-simplify form.\n");
    return false;
  }


  DEBUG(dbgs() <<"********************* DUMP LOOP BEFORE ******************\n");

  DEBUG(L->dump());
  
  for(auto bb : L->getBlocks()){
    DEBUG(bb->dump());
  }

  DEBUG(dbgs() <<"********************* DUMP LOOP END ******************\n");

  // FIXME get the good analysis for doing this ↓ (TTI,AC,UP) see
  // LoopUnrollPass.cpp:976 to 1045
  // TODO maybe the analysis will not be so optimizable and we will have to
  // decide to evaluate only short loops regarding to this size
  // TODO Here we can try to compute the trip count of the loop. Is it usefull
  // for us?

  AliasSetTracker *CurAST = collectAliasInfoForLoop(L, LI, AA);

  // Get the preheader block to move instructions into...
  BasicBlock *Preheader = L->getLoopPreheader();

  // Compute loop safety information.
  LoopSafetyInfo SafetyInfo;
  computeLoopSafetyInfo(&SafetyInfo, L);

  if (Preheader){
    if(Value* head = dyn_cast<Value>(L->getHeader())){

      // Check if there is not several exitblock here and abort if so
      // We will consider this case in the futur! TODO
      if(!L->getExitBlock()){
        DEBUG(dbgs() <<"WARN: severals exitBlock → Abort\n");
        NumLoopsManyExitB++;
        if (L->getParentLoop() && !DeleteAST)
          LoopToAliasSetMap[L] = CurAST;
        else
          delete CurAST;
        return false;
      }

      DEBUG(dbgs() <<"INFO: ExitBlock = " << L->getExitBlock()->getName() <<"\n");

      /* if(!L->getLoopLatch()){ */
      /*   DEBUG(dbgs() <<"WARN: severals Latchs → Abort\n"); */
      /*   NumLoopsManyLatch++; */
      /*   if (L->getParentLoop() && !DeleteAST) */
      /*     LoopToAliasSetMap[L] = CurAST; */
      /*   else */
      /*     delete CurAST; */
      /*   return false; */
      /* } */

      /* DEBUG(dbgs() <<"INFO: Latch = " << L->getLoopLatch()->getName() <<"\n"); */

      Chunk* loopChunk = new Chunk(L->getHeader()->getName());
      loopChunk->setEnd(L->getExitBlock());
      loopChunk->setStart(L->getHeader());

      // We place them in the map of maps with the value of the header as a key
      // FIXME is the head relevant to be the key?
      mapChunk[head] = loopChunk;

      // Ordered Commands
      std::vector<Value*> OC;

      // Computes the Relation of the loop by recursively computing inner
      // relations (each subLoops, branches, instructions…)
      Relation *RL = computeRelationLoop(DT->getNode(L->getHeader()), &mapChunk,
                                         AA, LI, DT, L, CurAST, &SafetyInfo, DI,
                                         PDT, &OC);
      if(!RL){
        DEBUG(errs() <<"ERROR computation Relation of Loop\n");
        NumError++;
        loopChunk->setType(Chunk::ERROR);
        if (L->getParentLoop() && !DeleteAST)
          LoopToAliasSetMap[L] = CurAST;
        else
          delete CurAST;
        return false;
      }

      loopChunk->setRel(RL);
      /* DEBUG(RL->dump(dbgs())); */

      //Here we transform the current loop!
      // - Need the max deg if deg max is -1 do nothing and return false
      int maxDeg = getDegMax(loopChunk->getMapDeg());
      DEBUG(dbgs() <<"*********************maxDeg******************\n");
      DEBUG(dbgs() << maxDeg <<"\n");
      if(maxDeg!=-1){
        DEBUG(dbgs() <<"Something has to be peeled…\n");
        // - For each deg d from 0 to degMax:
        //    - Create a CFG with all commands in the loop with deg rather than d
        //    or equal to -1(infinity)
        //    - Put this CFG in a kind of "preheader" of degree d with the same
        //    stop condition as for the loop
        // - Remove all command with a deg not equal to -1
        /* Changed = mypeelLoop(L, maxDeg, &mapChunk, &OC, LI, SE, DT, PDT, true); */
        if(Changed)
          DEBUG(dbgs() <<"PEELED!\n");
        else DEBUG(dbgs() <<"IMPOSSIBLE TO PEEL!\n");
      }
    }
  }
  if (L->getParentLoop() && !DeleteAST)
    LoopToAliasSetMap[L] = CurAST;
  else
    delete CurAST;

  return Changed;
}/*}-}*/

/// Returns true if a PHINode is a trivially replaceable with an
/// Instruction.
/// This is true when all incoming values are that instruction.
/// This pattern occurs most often with LCSSA PHI nodes.
///
static bool isTriviallyReplacablePHI(const PHINode &PN, const Instruction &I) {/*{-{*/
  for (const Value *IncValue : PN.incoming_values())
    if (IncValue != &I)
      return false;

  return true;
}/*}-}*/

static Instruction */*{-{*/
CloneInstructionInExitBlock(Instruction &I, BasicBlock &ExitBlock, PHINode &PN,
                            const LoopInfo *LI,
                            const LoopSafetyInfo *SafetyInfo) {
  Instruction *New;
  if (auto *CI = dyn_cast<CallInst>(&I)) {
    const auto &BlockColors = SafetyInfo->BlockColors;

    // Sinking call-sites need to be handled differently from other
    // instructions.  The cloned call-site needs a funclet bundle operand
    // appropriate for it's location in the CFG.
    SmallVector<OperandBundleDef, 1> OpBundles;
    for (unsigned BundleIdx = 0, BundleEnd = CI->getNumOperandBundles();
         BundleIdx != BundleEnd; ++BundleIdx) {
      OperandBundleUse Bundle = CI->getOperandBundleAt(BundleIdx);
      if (Bundle.getTagID() == LLVMContext::OB_funclet)
        continue;

      OpBundles.emplace_back(Bundle);
    }

    if (!BlockColors.empty()) {
      const ColorVector &CV = BlockColors.find(&ExitBlock)->second;
      assert(CV.size() == 1 && "non-unique color for exit block!");
      BasicBlock *BBColor = CV.front();
      Instruction *EHPad = BBColor->getFirstNonPHI();
      if (EHPad->isEHPad())
        OpBundles.emplace_back("funclet", EHPad);
    }

    New = CallInst::Create(CI, OpBundles);
  } else {
    New = I.clone();
  }

  ExitBlock.getInstList().insert(ExitBlock.getFirstInsertionPt(), New);
  if (!I.getName().empty())
    New->setName(I.getName() + ".le");

  // Build LCSSA PHI nodes for any in-loop operands. Note that this is
  // particularly cheap because we can rip off the PHI node that we're
  // replacing for the number and blocks of the predecessors.
  // OPT: If this shows up in a profile, we can instead finish sinking all
  // invariant instructions, and then walk their operands to re-establish
  // LCSSA. That will eliminate creating PHI nodes just to nuke them when
  // sinking bottom-up.
  for (User::op_iterator OI = New->op_begin(), OE = New->op_end(); OI != OE;
       ++OI)
    if (Instruction *OInst = dyn_cast<Instruction>(*OI))
      if (Loop *OLoop = LI->getLoopFor(OInst->getParent()))
        if (!OLoop->contains(&PN)) {
          PHINode *OpPN =
              PHINode::Create(OInst->getType(), PN.getNumIncomingValues(),
                              OInst->getName() + ".lcssa", &ExitBlock.front());
          for (unsigned i = 0, e = PN.getNumIncomingValues(); i != e; ++i)
            OpPN->addIncoming(OInst, PN.getIncomingBlock(i));
          *OI = OpPN;
        }
  return New;
}/*}-}*/

/// Return true if the only users of this instruction are outside of
/// the loop. If this is true, we can sink the instruction to the exit
/// blocks of the loop.
///
static bool isNotUsedInLoop(const Instruction &I, const Loop *CurLoop,/*{-{*/
                            const LoopSafetyInfo *SafetyInfo) {
  const auto &BlockColors = SafetyInfo->BlockColors;
  for (const User *U : I.users()) {
    const Instruction *UI = cast<Instruction>(U);
    if (const PHINode *PN = dyn_cast<PHINode>(UI)) {
      const BasicBlock *BB = PN->getParent();
      // We cannot sink uses in catchswitches.
      if (isa<CatchSwitchInst>(BB->getTerminator()))
        return false;

      // We need to sink a callsite to a unique funclet.  Avoid sinking if the
      // phi use is too muddled.
      if (isa<CallInst>(I))
        if (!BlockColors.empty() &&
            BlockColors.find(const_cast<BasicBlock *>(BB))->second.size() != 1)
          return false;

      // A PHI node where all of the incoming values are this instruction are
      // special -- they can just be RAUW'ed with the instruction and thus
      // don't require a use in the predecessor. This is a particular important
      // special case because it is the pattern found in LCSSA form.
      if (isTriviallyReplacablePHI(*PN, I)) {
        if (CurLoop->contains(PN))
          return false;
        else
          continue;
      }

      // Otherwise, PHI node uses occur in predecessor blocks if the incoming
      // values. Check for such a use being inside the loop.
      for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i)
        if (PN->getIncomingValue(i) == &I)
          if (CurLoop->contains(PN->getIncomingBlock(i)))
            return false;

      continue;
    }

    if (CurLoop->contains(UI))
      return false;
  }
  return true;
}/*}-}*/

/// When an instruction is found to only be used outside of the loop, this
/// function moves it to the exit blocks and patches up SSA form as needed.
/// This method is guaranteed to remove the original instruction from its
/// position, and may either delete it or move it to outside of the loop.
///
static bool sink(Instruction &I, const LoopInfo *LI, const DominatorTree *DT,/*{-{*/
                 const Loop *CurLoop, AliasSetTracker *CurAST,
                 const LoopSafetyInfo *SafetyInfo) {
  DEBUG(dbgs() << "LICM sinking instruction: " << I << "\n");
  bool Changed = false;
  Changed = true;

#ifndef NDEBUG
  SmallVector<BasicBlock *, 32> ExitBlocks;
  CurLoop->getUniqueExitBlocks(ExitBlocks);
  SmallPtrSet<BasicBlock *, 32> ExitBlockSet(ExitBlocks.begin(),
                                             ExitBlocks.end());
#endif

  // Clones of this instruction. Don't create more than one per exit block!
  SmallDenseMap<BasicBlock *, Instruction *, 32> SunkCopies;

  // If this instruction is only used outside of the loop, then all users are
  // PHI nodes in exit blocks due to LCSSA form. Just RAUW them with clones of
  // the instruction.
  while (!I.use_empty()) {
    Value::user_iterator UI = I.user_begin();
    auto *User = cast<Instruction>(*UI);
    if (!DT->isReachableFromEntry(User->getParent())) {
      User->replaceUsesOfWith(&I, UndefValue::get(I.getType()));
      continue;
    }
    // The user must be a PHI node.
    PHINode *PN = cast<PHINode>(User);

    // Surprisingly, instructions can be used outside of loops without any
    // exits.  This can only happen in PHI nodes if the incoming block is
    // unreachable.
    Use &U = UI.getUse();
    BasicBlock *BB = PN->getIncomingBlock(U);
    if (!DT->isReachableFromEntry(BB)) {
      U = UndefValue::get(I.getType());
      continue;
    }

    BasicBlock *ExitBlock = PN->getParent();
    assert(ExitBlockSet.count(ExitBlock) &&
           "The LCSSA PHI is not in an exit block!");

    Instruction *New;
    auto It = SunkCopies.find(ExitBlock);
    if (It != SunkCopies.end())
      New = It->second;
    else
      New = SunkCopies[ExitBlock] =
          CloneInstructionInExitBlock(I, *ExitBlock, *PN, LI, SafetyInfo);

    PN->replaceAllUsesWith(New);
    PN->eraseFromParent();
  }

  CurAST->deleteValue(&I);
  I.eraseFromParent();
  return Changed;
}/*}-}*/


/// Only sink or hoist an instruction if it is not a trapping instruction,
/// or if the instruction is known not to trap when moved to the preheader.
/// or if it is a trapping instruction and is guaranteed to execute.
static bool isSafeToExecuteUnconditionally(const Instruction &Inst,/*{-{*/
                                           const DominatorTree *DT,
                                           const Loop *CurLoop,
                                           const LoopSafetyInfo *SafetyInfo,
                                           const Instruction *CtxI) {
  if (isSafeToSpeculativelyExecute(&Inst, CtxI, DT))
    return true;

  return isGuaranteedToExecute(Inst, DT, CurLoop, SafetyInfo);
}/*}-}*/

/// Returns an owning pointer to an alias set which incorporates aliasing info
/// from L and all subloops of L.
/// FIXME: In new pass manager, there is no helper function to handle loop
/// analysis such as cloneBasicBlockAnalysis, so the AST needs to be recomputed
/// from scratch for every loop. Hook up with the helper functions when
/// available in the new pass manager to avoid redundant computation.
AliasSetTracker *
LoopInvariantCodeMotion::collectAliasInfoForLoop(Loop *L, LoopInfo *LI,/*{-{*/
                                                 AliasAnalysis *AA) {
  AliasSetTracker *CurAST = nullptr;
  SmallVector<Loop *, 4> RecomputeLoops;
  for (Loop *InnerL : L->getSubLoops()) {
    auto MapI = LoopToAliasSetMap.find(InnerL);
    // If the AST for this inner loop is missing it may have been merged into
    // some other loop's AST and then that loop unrolled, and so we need to
    // recompute it.
    if (MapI == LoopToAliasSetMap.end()) {
      RecomputeLoops.push_back(InnerL);
      continue;
    }
    AliasSetTracker *InnerAST = MapI->second;

    if (CurAST != nullptr) {
      // What if InnerLoop was modified by other passes ?
      CurAST->add(*InnerAST);

      // Once we've incorporated the inner loop's AST into ours, we don't need
      // the subloop's anymore.
      delete InnerAST;
    } else {
      CurAST = InnerAST;
    }
    LoopToAliasSetMap.erase(MapI);
  }
  if (CurAST == nullptr)
    CurAST = new AliasSetTracker(*AA);

  auto mergeLoop = [&](Loop *L) {
    // Loop over the body of this loop, looking for calls, invokes, and stores.
    // Because subloops have already been incorporated into AST, we skip blocks
    // in subloops.
    for (BasicBlock *BB : L->blocks())
      if (LI->getLoopFor(BB) == L) // Ignore blocks in subloops.
        CurAST->add(*BB);          // Incorporate the specified basic block
  };

  // Add everything from the sub loops that are no longer directly available.
  for (Loop *InnerL : RecomputeLoops)
    mergeLoop(InnerL);

  // And merge in this loop.
  mergeLoop(L);

  return CurAST;
}/*}-}*/

/// Simple analysis hook. Clone alias set info.
///
void LegacyLQICMPass::cloneBasicBlockAnalysis(BasicBlock *From, BasicBlock *To,/*{-{*/
                                             Loop *L) {
  AliasSetTracker *AST = LQICM.getLoopToAliasSetMap().lookup(L);
  if (!AST)
    return;

  AST->copyValue(From, To);
}/*}-}*/

/// Simple Analysis hook. Delete value V from alias set
///
void LegacyLQICMPass::deleteAnalysisValue(Value *V, Loop *L) {/*{-{*/
  AliasSetTracker *AST = LQICM.getLoopToAliasSetMap().lookup(L);
  if (!AST)
    return;

  AST->deleteValue(V);
}/*}-}*/

/// Simple Analysis hook. Delete value L from alias set map.
///
void LegacyLQICMPass::deleteAnalysisLoop(Loop *L) {/*{-{*/
  AliasSetTracker *AST = LQICM.getLoopToAliasSetMap().lookup(L);
  if (!AST)
    return;

  delete AST;
  LQICM.getLoopToAliasSetMap().erase(L);
}/*}-}*/

/// Return true if the body of this loop may store into the memory
/// location pointed to by V.
///
static bool pointerInvalidatedByLoop(Value *V, uint64_t Size,/*{-{*/
                                     const AAMDNodes &AAInfo,
                                     AliasSetTracker *CurAST) {
  // Check to see if any of the basic blocks in CurLoop invalidate *V.
  return CurAST->getAliasSetForPointer(V, Size, AAInfo).isMod();
}/*}-}*/

