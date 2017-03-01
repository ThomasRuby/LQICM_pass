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
static Relation* computeRelationLoop(DomTreeNode *N, MapLoopDeg* mapDeg, MapLoopRel*
                                     mapRel, AliasAnalysis *AA, LoopInfo *LI,
                                     DominatorTree *DT, TargetLibraryInfo *TLI,
                                     Loop *CurLoop, AliasSetTracker *CurAST,
                                     LoopSafetyInfo *SafetyInfo, DependenceInfo
                                     *DI, PostDominatorTree *PDT);

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
      if (!canSinkOrHoistInst(I, AA, DT, CurLoop, CurAST, SafetyInfo))
        DEBUG(dbgs() << " canNotSinkOrHoistInst " << '\n');
      if (!isSafeToExecuteUnconditionally( //TODO ça il faut voir …
          I, DT, CurLoop, SafetyInfo,
          CurLoop->getLoopPreheader()->getTerminator()))
        DEBUG(dbgs() << " isNotSafeToExecuteUnconditionnally " << '\n');
      if (isNotUsedInLoop(I,CurLoop,SafetyInfo))
        DEBUG(dbgs() << " isNotUsedInLoop " << '\n');
      // End Debug infos … ↑

      if (canSinkOrHoistInst(I, AA, DT, CurLoop, CurAST, SafetyInfo) &&
          isSafeToExecuteUnconditionally( //TODO ça il faut voir …
            I, DT, CurLoop, SafetyInfo,
            CurLoop->getLoopPreheader()->getTerminator()))
        (*mapDeg)[&I]=0;
      else (*mapDeg)[&I]=-1;
      OC->push_back(&I);
      DEBUG(dbgs() << "(*mapDeg)[&I]= " << (*mapDeg)[&I] << '\n');

      if(!(*mapDeg)[&I]){
        Relation *RI = new Relation(&I);
        // Save relation with instruction
        (*mapRel)[&I] = RI;
        DEBUG(RI->dump(dbgs()));
        DEBUG(dbgs() << " Composition…" << '\n');
        RB = RB->composition(RI);
        DEBUG(RB->dump(dbgs()));
      }
    }//End of For II in BB
    return RB;
}/*}-}*/

// Dinamically computes the invariance degrees/*{-{*/
static int computeDeg(MapDeg* mapDeg, Value* I, MapRel* mapRel, DominatorTree *DT, Value *head){
  DEBUG(dbgs() << "\nINFO… " << I << " Computation degree…" << '\n');
  if((*mapDeg)[I]){
    DEBUG(dbgs() << " Already in mapDeg with deg = " << (*mapDeg)[I] << '\n');
    return (*mapDeg)[I];
  }
  else{
    (*mapDeg)[I]=-1;
    if(!mapRel->count(I)){
      DEBUG(dbgs() << "\nINFO… " << I << " has not been visited" << '\n');
      // Means it was initialized outside the loop
      (*mapDeg)[I] = 1;
      return 0;
    }
    else{
      Relation* RI = (*mapRel)[I];
      DEBUG(dbgs() << " Relation found: " << '\n');
      DEBUG(RI->dump(dbgs()));
      if(RI->getDep().empty()){ // Empty dep
        DEBUG(dbgs() << " No dependence →  deg = ");
        (*mapDeg)[I] = 1;
        return 1;
      }
      else{
        Value* instMax;
        int degMax=-1;
        VSet inInst = RI->getIn();
        DEBUG(dbgs() << " Compute deg on dependencies ");
        for (auto VV = inInst.begin(), E = inInst.end(); VV != E; ++VV) {
          Value* V = *VV;
          VSet relations = searchForRelationsWithVAsOutput(V,mapRel);
          if(relations.empty()){
            DEBUG(dbgs() << " There is no relation which has " << V << 
                  " in outputs then no dependence → deg = ");
            (*mapDeg)[I]=1;
            if((*mapDeg)[I]>=degMax){
              degMax=(*mapDeg)[I];
              instMax = V;
            }
            continue;
          }
          // TODO Optimize me!
          for(auto RR = relations.begin(), RRE = relations.end(); RR != RRE; ++RR){
            Value* VR = *RR; 
            DEBUG(dbgs() << " Relation which has " << V << " in outputs ");
            DEBUG((*mapRel)[VR]->dump(dbgs()));
            if(VR == head){
              DEBUG(dbgs() << " This is the Relation of the Loop! ");
              (*mapDeg)[I]=-1;
            } else
              (*mapDeg)[I]=computeDeg(mapDeg,VR,mapRel,DT,head);
            if((*mapDeg)[I]>=degMax){
              degMax=(*mapDeg)[I];
              instMax = VR;
            }
          }
        }
        bool IdominatesMax = false;
        if (Instruction *II = dyn_cast<Instruction>(I)) {
          if (Instruction *IM = dyn_cast<Instruction>(instMax)) {
            IdominatesMax = DT->dominates(II,IM);
          } //End if dyn_cast<Instruction>(instMax)
          else {
            DEBUG(dbgs() << " INFO: Failed to cast instMax to Instruction! Is an InnerBlock?\n");
            if (BasicBlock *BIM = dyn_cast<BasicBlock>(instMax)) {
              DEBUG(dbgs() << " INFO: Yes it's " << BIM->getName());
              IdominatesMax = DT->dominates(II,BIM);
            } else 
              DEBUG(dbgs() << " ERROR: Failed to cast I to BasicBlock!");
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
            DEBUG(dbgs() << " ERROR: Failed to cast I to BasicBlock!");
        }
        if(degMax!=-1 && IdominatesMax) // I avant instMax
          (*mapDeg)[I]=degMax+1;
        else (*mapDeg)[I]=degMax;
        return (*mapDeg)[I];
      } //End else no dependencies
    } //End else no I in mapRel
  } //End else mapDeg[I] already computed
}/*}-}*/

// Sub functions/*{-{*/
static MapDeg* computeDeg(MapDeg* mapDeg, std::vector<Value*> OC, MapRel*
                          mapRel, DominatorTree *DT, Value* head){
    for(Value* I : OC){
      DEBUG(dbgs() << "Compute Deg for : " << *I << " = ");
      DEBUG(dbgs() << computeDeg(mapDeg,I,mapRel,DT,head));
      DEBUG(dbgs() << '\n');
    }
}/*}-}*/

// Sub functions
static MapDeg* computeDeg(MapDeg* mapDeg, BasicBlock* BB, MapRel* mapRel,/*{-{*/
                          DominatorTree *DT, Value* head){
    for (BasicBlock::iterator II = BB->begin(), E = BB->end(); II != E;) {
      Instruction &I = *II++;
      DEBUG(dbgs() << "Compute Deg for : " << I << " = ");
      DEBUG(dbgs() << computeDeg(mapDeg,&I,mapRel,DT,head));
      DEBUG(dbgs() << '\n');
    }
}/*}-}*/

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
                                         Relation *RPHI, MapLoopDeg* mapLoopDeg,
                                         MapLoopRel* mapLoopRel, AliasAnalysis
                                         *AA, LoopInfo *LI, DominatorTree *DT,
                                         TargetLibraryInfo *TLI, Loop *CurLoop,
                                         AliasSetTracker *CurAST, LoopSafetyInfo
                                         *SafetyInfo, DependenceInfo *DI,
                                         PostDominatorTree *PDT,
                                         std::vector<Value*> *OC){

  Relation *RB = new Relation();
  
  // If we are here, it (should) works
  Value* head = dyn_cast<Value>(CurLoop->getHeader());
  Value* bb = dyn_cast<Value>(BB);

  MapDeg *mapDeg = (*mapLoopDeg)[head];
  MapRel *mapRel = (*mapLoopRel)[head];

  // Not in Loop ?
  if (!CurLoop->contains(BB)){
    DEBUG(dbgs() << "---- Not In Current Loop " << '\n');
    // Return empty Relation
    return RB;
  }

  if((*mapLoopRel)[bb]){
    DEBUG(dbgs() << " BB " << bb << " is an innerBlock \n");
    // Then don't touch the mapRel of the loop but of the current sub chunk
    mapRel = (*mapLoopRel)[bb];
    mapDeg = new MapDeg();
  }

  // This case compute a LoopRelation if the Block encountered is an innerLoop
  // header
  if(inSubLoop(BB, CurLoop, LI)){
    DEBUG(dbgs() << "In subLoop! " << '\n');
    Loop* InnerLoop = LI->getLoopFor(BB);
    if(InnerLoop->getHeader()==BB){
      // Add phi entry relations first !!!
      Relation *RL = new Relation();
      Relation* inneRPHI = getPHIRelations(InnerLoop,mapDeg,mapRel,OC,true);
      RL = RL->composition(inneRPHI);

      if(Value* InnerHead = dyn_cast<Value>(InnerLoop->getHeader())){
        if(!(*(*mapLoopRel)[InnerHead])[InnerHead]){ // ← ugly
          DEBUG(dbgs() << " ERROR! Relation not found for Loop with Head = " <<
                InnerHead <<'\n');
        } else {
          DEBUG(dbgs() << " Relation found for Loop with Head = " << InnerHead
                <<'\n');
          DEBUG((*(*mapLoopRel)[InnerHead])[InnerHead]->dump(dbgs()));
          (*(*mapLoopRel)[head])[InnerHead] = (*(*mapLoopRel)[InnerHead])[InnerHead];
        }
        // Initialization: we suppose the loop is hoistable
        (*(*mapLoopDeg)[head])[InnerHead] = 0; 
        OC->push_back(InnerHead);
        RL = RL->composition((*(*mapLoopRel)[head])[InnerHead]);

        // Continue by treating while.end
        if(BasicBlock* WhileEnd = InnerLoop->getExitBlock()){
          DEBUG(dbgs() << " INFO: Exit Loop Block is :" << WhileEnd->getName() << '\n');
          RB = RL->composition(computeRelationBBInLoop(WhileEnd ,End ,RPHI
                                                       ,mapLoopDeg ,mapLoopRel
                                                       ,AA ,LI ,DT ,TLI ,CurLoop
                                                       ,CurAST ,SafetyInfo ,DI
                                                       ,PDT ,OC));
        }
        else
          DEBUG(dbgs() << " WARN: Fail to find unique While.end?" << '\n');
        
      } else
        DEBUG(dbgs() << " WARN: Fail cast InnerHead to Value! :" << '\n');
      return RB;
    }
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

        // No deg computed inside. Only the relation of if matters
        // One Relation for each branch
        MapRel *mapThenRel = new MapRel();
        MapRel *mapElseRel = new MapRel();
        std::vector<Value*> OCif;

        Value* VThen = dyn_cast<Value>(Then);
        Value* VElse = dyn_cast<Value>(Else);
        
        // Every relations of the branches will be in the corresponding map
        (*mapLoopRel)[VThen] = mapThenRel;
        (*mapLoopRel)[VElse] = mapElseRel;

        // it could have some phi to take into account! IMPORTANT
        Relation *RThenPHI = getPHIRelations(BB,Then,mapRel);
        Relation *RElsePHI = getPHIRelations(BB,Else,mapRel);

        // Recursive call on each branch
        Relation* RThen = computeRelationBBInLoop(Then, IfEnd, RPHI, mapLoopDeg,
                                                  mapLoopRel, AA, LI, DT, TLI,
                                                  CurLoop, CurAST, SafetyInfo,
                                                  DI, PDT, &OCif);
        Relation* RElse = computeRelationBBInLoop(Else, IfEnd, RPHI, mapLoopDeg,
                                                  mapLoopRel, AA, LI, DT, TLI,
                                                  CurLoop, CurAST, SafetyInfo,
                                                  DI, PDT, &OCif);

        DEBUG(dbgs() << " Then : " << Then << '\n');
        DEBUG(RThen->dump(dbgs()));
        DEBUG(dbgs() << " Else : " << Else << '\n');
        DEBUG(RElse->dump(dbgs()));

        // Add Phi entries
        RThen = RThenPHI->composition(RThen);
        RElse = RElsePHI->composition(RElse);

        Relation *RBranch = new Relation();
        
        // Sum branchs
        RBranch = RBranch->composition(RThen->sumRelation(RElse));

        // Here RB is the relation of the If but we need to add conditions dep
        Relation *RCMP = getCondRelationsFromBB(BB,mapRel);
        RBranch->addDependencies(RCMP->getIn(),RBranch->getOut());

        DEBUG(dbgs() << " FINAL Branch from " << TInst << '\n');
        DEBUG(RBranch->dump(dbgs()));

        (*mapDeg)[TInst] = 0;
        (*mapRel)[TInst] = RBranch;
        // Is this useless?
        // The sum will be added here, key = to TInst
        (*mapLoopRel)[TInst] = new MapRel();
        (*(*mapLoopRel)[TInst])[TInst] = RBranch;

        RB = RB->composition(RBranch);

        // Continue with the if.end block
        RB = RB->composition(computeRelationBBInLoop(IfEnd, End, RPHI,
                                                     mapLoopDeg, mapLoopRel, AA,
                                                     LI, DT, TLI, CurLoop,
                                                     CurAST, SafetyInfo, DI,
                                                     PDT, OC));
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
    if(BB->getUniqueSuccessor() == End){
      DEBUG(dbgs() << " Unique successor is :" <<
            End->getName() << '\n');
      // If there is some phi in End take into account here the assignements
      // If it's the header of the current loop, they are already computed
      if(End == CurLoop->getHeader())
        RB = RB->composition(RPHI);
      else{
        if((*mapLoopRel)[bb]){
          DEBUG(dbgs() << " getPHIRelations on inner mapRel :" << '\n');
        }
        RB = RB->composition(getPHIRelations(BB,Succ,mapRel));
      }
    }else{
      // Recursiv call on next BB and composition with the current
      RB =
        RB->composition(computeRelationBBInLoop(Succ, End, RPHI, mapLoopDeg,
                                                mapLoopRel, AA, LI, DT, TLI,
                                                CurLoop, CurAST, SafetyInfo, DI,
                                                PDT, OC));
    }
  }

  return RB;
}/*}-}*/

/// Compute Relation for the Loop with fixpoint and cond correction/*{-{*/
static Relation* computeRelationLoop(DomTreeNode *N, MapLoopDeg * mapLoopDeg,
                                     MapLoopRel* mapLoopRel, AliasAnalysis *AA,
                                     LoopInfo *LI, DominatorTree *DT,
                                     TargetLibraryInfo *TLI, Loop *CurLoop,
                                     AliasSetTracker *CurAST, LoopSafetyInfo
                                     *SafetyInfo, DependenceInfo *DI,
                                     PostDominatorTree *PDT) {

    DEBUG(dbgs() <<"\n************ComputeRelationLoop***********\n");
    BasicBlock* Head = CurLoop->getHeader();
    if(Value* head = dyn_cast<Value>(Head)){

      // Check if there is not several exitblock here and abort if so
      // We will consider this case in the futur!
      if(!CurLoop->getExitBlock()){
        DEBUG(dbgs() <<"WARN: severals exitBlock → Abort");
        return new Relation();
      }

      // Ordered Commands
      std::vector<Value*> OC;

      Relation *RPHI = getPHIRelations(CurLoop,(*mapLoopRel)[head],false);
      BasicBlock *FirstBody = getFirstBodyOfLoop(CurLoop);
      Relation *RL = computeRelationBBInLoop(FirstBody, Head, RPHI, mapLoopDeg,
                                             mapLoopRel, AA, LI, DT, TLI,
                                             CurLoop, CurAST, SafetyInfo, DI,
                                             PDT, &OC);

      // Take the while.end into account
      DEBUG(dbgs() << " Fixpoint…" << '\n');
      RL = fixPoint(RL);
      DEBUG(RL->dump(dbgs()));

      Relation *RCMP = getCondRelationsFromBB(Head,(*mapLoopRel)[head]);
      RL->addDependencies(RCMP->getIn(),RL->getOut());
      DEBUG(dbgs() << " Condition correction… " << '\n');
      DEBUG(dbgs() << " FINAL LOOP OF DEPTH " << CurLoop->getLoopDepth() << 
            " and header = " << head <<'\n');
      DEBUG(RL->dump(dbgs()));
      // FIXME make it more clear↓
      (*(*mapLoopRel)[head])[head]=RL;

      computeDeg((*mapLoopDeg)[head], OC, (*mapLoopRel)[head], DT,head);
      DEBUG(dumpMapDegOfOC(mapLoopRel,(*mapLoopDeg)[head],OC,dbgs()));

      return RL;
    }
    else
      DEBUG(dbgs() << " Error dyn_cast Header in value " << '\n');
}/*}-}*/

PreservedAnalyses LQICMPass::run(Loop &L, LoopAnalysisManager &AM) {/*{-{*/
  const auto &FAM =
      AM.getResult<FunctionAnalysisManagerLoopProxy>(L).getManager();
  Function *F = L.getHeader()->getParent();

  auto *AA = FAM.getCachedResult<AAManager>(*F);
  auto *LI = FAM.getCachedResult<LoopAnalysis>(*F);
  auto *DT = FAM.getCachedResult<DominatorTreeAnalysis>(*F);
  auto *TLI = FAM.getCachedResult<TargetLibraryAnalysis>(*F);
  auto *DI = FAM.getCachedResult<DependenceAnalysis>(*F);
  auto *PDT = FAM.getCachedResult<PostDominatorTreeAnalysis>(*F);
  auto *SE = FAM.getCachedResult<ScalarEvolutionAnalysis>(*F);
  assert((AA && LI && DT && TLI && SE) && "Analyses for LICM not available");

  LoopInvariantCodeMotion LICM;

  if (!LICM.runOnLoop(&L, AA, LI, DT, TLI, DI, PDT, SE, true))
    return PreservedAnalyses::all();

  // FIXME: There is no setPreservesCFG in the new PM. When that becomes
  // available, it should be used here.
  return getLoopPassPreservedAnalyses();
}/*}-}*/

char LegacyLQICMPass::ID = 0;
static RegisterPass<LegacyLQICMPass> X("lqicm", "Loop quasi-Invariant Code Motion");

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
                                        TargetLibraryInfo *TLI,
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
      // Map of relation for this loop
      MapRel *mapRel = new MapRel();
      // Map of degrees for this loop
      MapDeg *mapDeg = new MapDeg();

      // We place them in the map of maps with the value of the header as a key
      // FIXME is the head relevant to be the key?
      mapLoopRel[head] = mapRel;
      mapLoopDeg[head] = mapDeg;

      // Computes the Relation of the loop by recursively computing inner
      // relations (each subLoops, branches, instructions…)
      Relation *RL = computeRelationLoop(DT->getNode(L->getHeader()), &mapLoopDeg,
                                         &mapLoopRel, AA, LI, DT, TLI, L, CurAST,
                                         &SafetyInfo, DI, PDT);

      //Here we transform the current loop!
      // - Need the max deg if deg max is -1 do nothing and return false
      int maxDeg = getDegMax(mapDeg);
      DEBUG(dbgs() <<"*********************maxDeg******************\n");
      DEBUG(dbgs() << maxDeg <<"\n");
      if(maxDeg!=-1){
        // - For each deg d from 0 to degMax:
        //    - Create a CFG with all commands in the loop with deg rather than d
        //    or equal to -1(infinity)
        //    - Put this CFG in a kind of "preheader" of degree d with the same
        //    stop condition as for the loop
        // - Remove all command with a deg not equal to -1
        Changed = mypeelLoop(L, maxDeg, &mapLoopDeg, LI, SE, DT, PDT, true);
        if(Changed)
          DEBUG(dbgs() <<"PEELED!\n");
        else DEBUG(dbgs() <<"IMPOSSIBLE TO PEEL!\n");
        Changed = true; 
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

