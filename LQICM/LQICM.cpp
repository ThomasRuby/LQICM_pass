//===-- LQICM.cpp - Loop Quasi-Invariant Chunk Motion Pass ------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
//===----------------------------------------------------------------------===//
//
//
//===----------------------------------------------------------------------===//

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include "./LQICM.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/AliasSetTracker.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/LoopPassManager.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include <utility>
using namespace llvm;

#define DEBUG_TYPE "lqicm"

// Relation object TODO should be somewhere else…
namespace {

  typedef DenseMap<Value*,SmallPtrSet<Value*,8>> DepMap;
  typedef SmallPtrSet<Value*,8> VSet;
  typedef SmallDenseMap<Value*, int> MapDeg;

  static void printValues(VSet spt, raw_ostream &OS){
    OS << '[';
    for (auto VV = spt.begin(), E = spt.end(); VV != E; ++VV) {
      Value* V = *VV;
      OS << '(' << V << ':' << V->getName() << "),";
    }
    OS << "]\n";
  }

  class Relation {
  protected:
    Relation(Relation &&) = default;
    Relation &operator=(Relation &&) = default;
    void setVariables(VSet v) { variables = v; }
    void setPropag(VSet v) { propag = v; }
    void setDep(DepMap d) { dep = d; }

  public:
    Relation(){}
    ~Relation(){}

    Relation(PHINode *PHI, Loop *L, bool WantIn){ 
      instructions.insert(PHI);
      addPropag(PHI);
      DEBUG(dbgs() << "\tNew Instruction\t" << " = \t" << PHI << '\n');
      unsigned i=0;
      bool onlyConst = true;
      for(auto OP = PHI->op_begin(), E = PHI->op_end(); OP!=E;){
        Value *v = OP->get();
        bool isIn = (PHI->getIncomingBlock(i) == L->getLoopPreheader());
        // Take initialisation into account !
        if(WantIn){
          if(isIn){
            if(!isa<Constant>(v)){
              addPropag(v);
              addDependence(v,PHI);
              onlyConst = false;
            } else{
              addInit(PHI);
            }
          }
        } else{
          // Do not take initialisation into account
          if(!isa<Constant>(v) && !isIn){
            addPropag(v);
            addDependence(v,PHI);
            onlyConst = false;
          }
        }
        OP++;
        i++;
      }// End for
      if(onlyConst) // If only const operands it's a Init
        addInit(PHI);
    }

    Relation(Instruction *I){
      if(isa<UnaryInstruction>(I)){
        instructions.insert(I);
        Value* v = I->getOperand(0);
        if(isa<Constant>(v))
          addInit(I);
        else
          addDependence(v,I);
      }
      else if (isa<BinaryOperator>(I) || isa<CastInst>(I) || isa<SelectInst>(I) ||
          isa<GetElementPtrInst>(I) || isa<CmpInst>(I) ||
          isa<InsertElementInst>(I) || isa<ExtractElementInst>(I) ||
          isa<ShuffleVectorInst>(I) || isa<ExtractValueInst>(I) ||
          isa<InsertValueInst>(I)){
        instructions.insert(I);
        addPropag(I);
        DEBUG(dbgs() << "\tNew Instruction\t" << " = \t" << *I
              << "\t → \t" << I << '\n');
        bool onlyConst = true;
        for(auto OP = I->op_begin(), E = I->op_end(); OP!=E;){
          Value *v = OP->get();
          if(!isa<Constant>(v)){
            addPropag(v);
            addDependence(v,I);
            onlyConst = false;
          }
          OP++;
        } //End for operands in I
        if(onlyConst) // If only const operands it's a Init
          addInit(I);
      } //End If isa…
    }

    Relation(Value* v) {
      instructions.insert(v);
    }

    Relation(VSet variables) {
      for (auto VV = variables.begin(), E = variables.end(); VV != E; ++VV) {
        Value* V = *VV;
        instructions.insert(V);
        addPropag(V);
      }
    }

    /// Propagation of a value 
    ///
    void addPropag(Value* v){
      propag.insert(v);
      variables.insert(v);
    }

    /// Add Value to variables
    ///
    void addVariable(Value* v){
        variables.insert(v);
    }

    /// Add Direct Dependence x = y … y → x
    ///
    void addDependence(Value* v1, Value* v2){
      if(!dep.count(v1)){
        VSet spt;
        dep[v1] = spt;
      }
      dep[v1].insert(v2);
      // Add new potentially variables
      addVariable(v1);
      addVariable(v2);
      // No propagation anymore…
      propag.erase(v2);
    }

    VSet mergeVSet(const VSet s1, const VSet s2){
      VSet s(s1);
      for (auto VV = s2.begin(), E = s2.end(); VV != E; ++VV) {
        Value* V = *VV;
        s.insert(V);
      }
      return s;
    }

    DepMap mergeDep(DepMap d1, DepMap d2){
      DepMap d(d2);
      for(auto D1 = d1.begin(), D1E = d1.end(); D1 != D1E; ++D1){
        Value* X1 = D1->first;
        VSet spt1 = D1->second;
        if(d2.count(X1))
          d[X1] = mergeVSet(d1[X1],d2[X1]);
        else d[X1] = d1[X1];
      }
      return d;
    }

    void addVariables(VSet s){
          for (auto VV = s.begin(), E = s.end(); VV != E; ++VV) {
            Value* V = *VV;
            addVariable(V);
          }
    }

    void removePropag(VSet s){
          for (auto VV = s.begin(), E = s.end(); VV != E; ++VV) {
            Value* V = *VV;
            propag.erase(V);
          }

    }

    /// Add Direct Dependencies x = y … y → x
    ///
    void addDependencies(VSet sIn, VSet sOut){
      for (auto VV = sIn.begin(), E = sIn.end(); VV != E; ++VV) {
        Value* V = *VV;
        addDependencies(V,sOut);
      }
    }

    /// Add Direct Dependencies x = y … y → x
    ///
    void addDependencies(Value* v1, VSet s){
      if(!dep.count(v1)){
        VSet spt(s);
        dep[v1] = spt;
      }
      else 
        dep[v1] = mergeVSet(dep[v1],s);
      addVariables(s);

      // No propagation anymore…
      removePropag(dep[v1]);
    }

    /// Add Initialisation x = 42 … x x
    ///
    void addInit(Value* v){
      // All hold direct dep removed
      dep.erase(v);
      // No propagation anymore…
      propag.erase(v);
      // Add in init
      init.insert(v);
      addVariable(v);
    }


    /// dump - For debugging purposes, dumps a dependence to OS.
    ///
    void dump(raw_ostream &OS){
      DEBUG(dbgs() << "\n---- dumpRelation ----\n ");
      OS << "Debug Relation" << '\n'<< '\t';
      OS << "Variables:" << '\n'<< '\t';
      printValues(variables,OS);
      OS << "Dependencies:" << '\n';
      for(auto DD = dep.begin(), DE = dep.end(); DD != DE;){
        Value* v = DD->first;
        VSet spt = DD->second;
        OS << '\t' << v->getName() << ":";
        printValues(spt,OS);
        DD++;
      }
      OS << "Propagations:" << '\n'<< '\t';
      printValues(propag,OS);
      OS << "Init:" << '\n'<< '\t';
      printValues(init,OS);
      DEBUG(dbgs() << "----------------------\n ");
    }

    /// Composition with r2
    /// 
    Relation* composition(Relation* r2){
      if(variables.empty())
        return r2;
      if(r2->variables.empty())
        return this;
      Relation* comp = new Relation(mergeVSet(variables,r2->variables));
      comp->instructions = mergeVSet(instructions,r2->instructions);
      // For each dependence in r2
      for(auto D2 = r2->dep.begin(), D2E = r2->dep.end(); D2 != D2E; ++D2){
        Value* X2 = D2->first;
        VSet spt2 = D2->second;
        if(!variables.count(X2)){ // Not in r1 variables
          comp->addDependencies(X2,spt2); // All dep are taken
        }
        else if(propag.count(X2)) // In propag
          comp->addDependencies(X2,spt2); // All dep are taken
        for(auto D1 = dep.begin(), D1E = dep.end(); D1 != D1E; ++D1){
          Value* X1 = D1->first;
          VSet spt1 = D1->second;
          for (auto YY = spt1.begin(), YE = spt1.end(); YY != YE; ++YY) {
            Value* Y1 = *YY;
            if(X2 == Y1){
              comp->addDependencies(X1,spt2);
              continue;
            }
            if(!r2->variables.count(Y1)){
              comp->addDependence(X1,Y1);
              continue;
            } else if(r2->propag.count(Y1)){
              comp->addDependence(X1,Y1);
              continue;
            }
          }
        }
      }
      return comp;
    }

    Relation* sumRelation(Relation* r2){
      Relation* sum = new Relation(variables);
      sum->setVariables(mergeVSet(variables,r2->variables));
      sum->setPropag(mergeVSet(propag,r2->propag));
      sum->setDep(mergeDep(dep,r2->dep));
      return sum;
    }

    bool isEqual(VSet s1, VSet s2){
      if(s1.size() != s2.size())
        return false;
      for (auto VV = s2.begin(), E = s2.end(); VV != E; ++VV) {
        Value* V = *VV;
        if(!s1.count(V))
          return false;
      }
      return true;
    }

    bool isEqual(Relation* r2){
      if(r2->dep.size() != dep.size())
        return false;
      // All dep of this
      for(auto D = dep.begin(), DE = dep.end(); D != DE; ++D){
        Value* v= D->first;
        if(!r2->dep.count(v))
          return false;
        VSet s= D->second;
        if(!isEqual(s,r2->dep[v]))
          return false;
      }
      return true;
    }

    VSet getOut(){
      VSet out(init); // All initializations are out variables
      for(auto D = dep.begin(), DE = dep.end(); D != DE; ++D){
        out = mergeVSet(out,D->second);
      }
      return out;
    }

    VSet getIn(){
      VSet in;
      for(auto D = dep.begin(), DE = dep.end(); D != DE; ++D){
        in.insert(D->first);
      }
      return in;
    }

    std::pair<VSet,VSet> getInOut(){
      VSet out(init); // All initializations are out variables
      VSet in;
      for(auto D = dep.begin(), DE = dep.end(); D != DE; ++D){
        in.insert(D->first);
        out = mergeVSet(out,D->second);
      }
      return std::make_pair(in, out);
    }

    VSet getInstructions(){
      return instructions;
    }

    DepMap getDep(){
      return dep;
    }

  private:
    VSet instructions;
    VSet variables;
    VSet propag;
    DepMap dep;
    VSet init;

  }; // End Relation

  typedef SmallDenseMap<Value*, Relation*> MapRel;

struct LoopInvariantCodeMotion {
  bool runOnLoop(Loop *L, AliasAnalysis *AA, LoopInfo *LI, DominatorTree *DT,
                 TargetLibraryInfo *TLI, DependenceInfo *DI, ScalarEvolution
                 *SE, bool DeleteAST);

  DenseMap<Loop *, AliasSetTracker *> &getLoopToAliasSetMap() {
    return LoopToAliasSetMap;
  }
  MapDeg &getMapDeg() {
    return mapDeg;
  }
  MapRel &getMapRel() {
    return mapRel;
  }

private:
  MapDeg mapDeg;
  MapRel mapRel;

  DenseMap<Loop *, AliasSetTracker *> LoopToAliasSetMap;

  AliasSetTracker *collectAliasInfoForLoop(Loop *L, LoopInfo *LI,
                                           AliasAnalysis *AA);
};

static void dumpMapDegOfOC(MapDeg* mapDeg, std::vector<Value*> OC, raw_ostream
                           &OS){
    DEBUG(dbgs() << "\n---- MapDegOfOC ----\n ");
    for(Value* I : OC){
      DEBUG(dbgs() << "Compute Deg for : " << *I << " = ");
      DEBUG(dbgs() << (*mapDeg)[I]);
      DEBUG(dbgs() << '\n');
    }
    DEBUG(dbgs() << "--------------------\n ");
}

static void dumpMapDegOfBB(MapDeg* mapDeg, BasicBlock* BB, raw_ostream &OS){
    DEBUG(dbgs() << "\n---- MapDegOfBB ----\n ");
    for (BasicBlock::iterator II = BB->begin(), E = BB->end(); II != E;) {
      Instruction &I = *II++;
      DEBUG(dbgs() << "Compute Deg for : " << I << " = ");
      DEBUG(dbgs() << (*mapDeg)[&I]);
      DEBUG(dbgs() << '\n');
    }
    DEBUG(dbgs() << "--------------------\n ");
}

// Return Relation composed for the loop condition
static Relation* getWhileCondRelations(Loop* L, MapRel* mapRel){
    BasicBlock* BB = L->getHeader();
    Relation *RB = new Relation(BB);
    bool hasRCMP = false;
    for (BasicBlock::iterator II = BB->end(), E = BB->begin(); II != E;) {
      Instruction &I = *--II;

      if (isa<CmpInst>(&I)) {
        if(hasRCMP){
          DEBUG(dbgs() << "ERROR: 2 CMP in while.cond? " << '\n');
          // What do we do in this case? FIXME
        }
        Relation *RCMP = new Relation(&I);
        // Save relation with instruction
        (*mapRel)[&I] = RCMP;
        RB = RCMP->composition(RB);
        hasRCMP = true;
      } 
      else if (isa<BinaryOperator>(I) || isa<CastInst>(I) || isa<SelectInst>(I)
               || isa<GetElementPtrInst>(I) || isa<InsertElementInst>(I) ||
               isa<ExtractElementInst>(I) || isa<ShuffleVectorInst>(I) ||
               isa<ExtractValueInst>(I) || isa<InsertValueInst>(I)){
        if(!hasRCMP){
          DEBUG(dbgs() << "ERROR: CMP not encountered yet!" << '\n');
          // What do we do in this case? FIXME
        }
          Relation *RI = new Relation(&I);
          // Save relation with instruction
          (*mapRel)[&I] = RI;
          RB = RI->composition(RB);
      }

      // We've reached all the conditions computations
      if (isa<PHINode>(&I))
        break;
    }//End of For II in BB
    if(RB->getInstructions().empty())
      return nullptr;
    else
      return RB;
}


// Return Relation composed for the given BasicBlock
static Relation* getPHIRelations(Loop* L, MapDeg* mapDeg, MapRel* mapRel,
                                 std::vector<Value*> *OC, bool WantIn){
    BasicBlock* BB = L->getHeader();
    Relation *RB = new Relation(BB);
    for (BasicBlock::iterator II = BB->begin(), E = BB->end(); II != E;) {
      Instruction &I = *II++;

      if (PHINode *PHI = dyn_cast<PHINode>(&I)) {
        Relation *RI = new Relation(PHI,L,WantIn);
        // Save relation with instruction
        (*mapRel)[&I] = RI;
        if(WantIn)
          (*mapDeg)[&I] = 0;
        OC->push_back(&I);
        RB = RB->composition(RI);
      }
    }//End of For II in BB
    if(RB->getInstructions().empty())
      return nullptr;
    else
      return RB;
}

// Return Relation composed for the given BasicBlock FIXME Polymorphism!
static Relation* getPHIRelations(Loop* L, MapRel* mapRel, bool WantIn){
    BasicBlock* BB = L->getHeader();
    Relation *RB = new Relation(BB);
    for (BasicBlock::iterator II = BB->begin(), E = BB->end(); II != E;) {
      Instruction &I = *II++;

      if (PHINode *PHI = dyn_cast<PHINode>(&I)) {
        Relation *RI = new Relation(PHI,L,WantIn);
        // Save relation with instruction
        (*mapRel)[&I] = RI;
        RB = RB->composition(RI);
      }
    }//End of For II in BB
    if(RB->getInstructions().empty())
      return nullptr;
    else
      return RB;
}



struct LegacyLQICMPass : public LoopPass {


  static char ID; // Pass identification, replacement for typeid
  LegacyLQICMPass() : LoopPass(ID) {}

  bool runOnLoop(Loop *L, LPPassManager &LPM) override {
    if (skipLoop(L)) {
      // If we have run LQICM on a previous loop but now we are skipping
      // (because we've hit the opt-bisect limit), we need to clear the
      // loop alias information.
      for (auto &LTAS : LQICM.getLoopToAliasSetMap())
        delete LTAS.second;
      LQICM.getLoopToAliasSetMap().clear();
      return false;
    }

    auto *SE = getAnalysisIfAvailable<ScalarEvolutionWrapperPass>();
    return LQICM.runOnLoop(L,
                          &getAnalysis<AAResultsWrapperPass>().getAAResults(),
                          &getAnalysis<LoopInfoWrapperPass>().getLoopInfo(),
                          &getAnalysis<DominatorTreeWrapperPass>().getDomTree(),
                          &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(),
                          &getAnalysis<DependenceAnalysisWrapperPass>().getDI(),
                          SE ? &SE->getSE() : nullptr, false);
  }

  /// This transformation requires natural loop information & requires that
  /// loop preheaders be inserted into the CFG...
  ///
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesCFG();
    AU.addRequired<TargetLibraryInfoWrapperPass>();
    AU.addRequired<DependenceAnalysisWrapperPass>();
    getLoopAnalysisUsage(AU);
  }

  using llvm::Pass::doFinalization;

  bool doFinalization() override {
    assert(LQICM.getLoopToAliasSetMap().empty() &&
           "Didn't free loop alias sets");
    return false;
  }

private:
  LoopInvariantCodeMotion LQICM;

  /// cloneBasicBlockAnalysis - Simple Analysis hook. Clone alias set info.
  void cloneBasicBlockAnalysis(BasicBlock *From, BasicBlock *To,
                               Loop *L) override;

  /// deleteAnalysisValue - Simple Analysis hook. Delete value V from alias
  /// set.
  void deleteAnalysisValue(Value *V, Loop *L) override;

  /// Simple Analysis hook. Delete loop L from alias set map.
  void deleteAnalysisLoop(Loop *L) override;
};
}

// Function from LQICM
static bool inSubLoop(BasicBlock *BB, Loop *CurLoop, LoopInfo *LI);
static bool isSafeToExecuteUnconditionally(const Instruction &Inst,
                                           const DominatorTree *DT,
                                           const Loop *CurLoop,
                                           const LoopSafetyInfo *SafetyInfo,
                                           const Instruction *CtxI = nullptr);
static bool pointerInvalidatedByLoop(Value *V, uint64_t Size,
                                     const AAMDNodes &AAInfo,
                                     AliasSetTracker *CurAST);

// Our functions
static Relation* computeRelationLoop(DomTreeNode *N, MapDeg*
                                         mapDeg, MapRel* mapRel, AliasAnalysis
                                         *AA, LoopInfo *LI, DominatorTree *DT,
                                         TargetLibraryInfo *TLI, Loop *CurLoop,
                                         AliasSetTracker *CurAST, LoopSafetyInfo
                                         *SafetyInfo, DependenceInfo *DI);
// Computes fixpoint relation (for loops)
static Relation* fixPoint(Relation* R){
  Relation* r = new Relation();
  Relation* nextR(R);
  while(!r->isEqual(nextR)){
    r = nextR;
    nextR=r->composition(R)->sumRelation(R);
  }
  return r;
}

// Return Relation composed for the given BasicBlock
static Relation* computeRelation(BasicBlock* BB, MapDeg* mapDeg , MapRel*
                                 mapRel, AliasAnalysis *AA, DominatorTree
                                 *DT,Loop *CurLoop,AliasSetTracker *CurAST,
                                 LoopSafetyInfo *SafetyInfo, std::vector<Value*>
                                 *OC){
    Relation *RB = new Relation(BB);
    for (BasicBlock::iterator II = BB->begin(), E = BB->end(); II != E;) {
      Instruction &I = *II++;

      if (canSinkOrHoistInst(I, AA, DT, CurLoop, CurAST, SafetyInfo) &&
          isSafeToExecuteUnconditionally( 
            I, DT, CurLoop, SafetyInfo,
            CurLoop->getLoopPreheader()->getTerminator()))
        (*mapDeg)[&I]=0;
      else (*mapDeg)[&I]=-1;
      OC->push_back(&I);

      if(!(*mapDeg)[&I]){
        Relation *RI = new Relation(&I);
        // Save relation with instruction
        (*mapRel)[&I] = RI;
        RB = RB->composition(RI);
      }
    }//End of For II in BB
    return RB;
}

// Dinamically computes the invariance degrees
static int computeDeg(MapDeg* mapDeg, Value* I, MapRel* mapRel, DominatorTree *DT){
  if((*mapDeg)[I]){
    return (*mapDeg)[I];
  }
  else{
    (*mapDeg)[I]=-1;
    if(!mapRel->count(I)){
      (*mapDeg)[I]=0;
      return 0;
    }
    else{
      Relation* RI = (*mapRel)[I];
      if(RI->getDep().empty()){ // Empty dep
        (*mapDeg)[I]=1;
        return 1;
      }
      else{
        Value* instMax;
        int degMax=-1;
        VSet inInst = RI->getIn();
        for (auto VV = inInst.begin(), E = inInst.end(); VV != E; ++VV) {
          Value* V = *VV;
          (*mapDeg)[I]=computeDeg(mapDeg,V,mapRel,DT);
          if((*mapDeg)[I]>=degMax)
            degMax=(*mapDeg)[I];
            instMax = V;
        }
        if (Instruction *II = dyn_cast<Instruction>(I)) {
          if (Instruction *IM = dyn_cast<Instruction>(instMax)) {
            if(degMax!=-1 && DT->dominates(II,IM)) // I avant instMax
              (*mapDeg)[I]=degMax+1;
            else (*mapDeg)[I]=degMax;
            return (*mapDeg)[I];
          } //End if dyn_cast<Instruction>(instMax)
        } //End if dyn_cast<Instruction>(I)
      } //End else no dependencies
    } //End else no I in mapRel
  } //End else mapDeg[I] already computed
}

// Sub functions
static MapDeg* computeDeg(MapDeg* mapDeg, std::vector<Value*> OC, MapRel*
                          mapRel, DominatorTree *DT){
    for(Value* I : OC){
      DEBUG(dbgs() << "Compute Deg for : " << *I << " = ");
      DEBUG(dbgs() << computeDeg(mapDeg,I,mapRel,DT));
      DEBUG(dbgs() << '\n');
    }
}

// Sub functions
static MapDeg* computeDeg(MapDeg* mapDeg, BasicBlock* BB, MapRel* mapRel,
                          DominatorTree *DT){
    for (BasicBlock::iterator II = BB->begin(), E = BB->end(); II != E;) {
      Instruction &I = *II++;
      DEBUG(dbgs() << "Compute Deg for : " << I << " = ");
      DEBUG(dbgs() << computeDeg(mapDeg,&I,mapRel,DT));
      DEBUG(dbgs() << '\n');
    }
}

/// Compute Relation for the Loop considering phi instructions
static Relation* computeRelationBodyLoop(DomTreeNode *N, Relation *RPHI, MapDeg*
                                         mapDeg, MapRel* mapRel, AliasAnalysis
                                         *AA, LoopInfo *LI, DominatorTree *DT,
                                         TargetLibraryInfo *TLI, Loop *CurLoop,
                                         AliasSetTracker *CurAST, LoopSafetyInfo
                                         *SafetyInfo, DependenceInfo *DI) {
  // Verify inputs.
  assert(N != nullptr && AA != nullptr && LI != nullptr && DT != nullptr &&
         CurLoop != nullptr && CurAST != nullptr && SafetyInfo != nullptr &&
         "Unexpected input to computeRelationBodyLoop");

    BasicBlock *BB = N->getBlock();

  // If this subregion is not in the top level loop at all, exit.
  if (!CurLoop->contains(BB)){
    return nullptr;
  }

  // Ordered Commands
  std::vector<Value*> OC;

  // Only need to process the contents of this block if it is not part of a
  // subloop (which would already have been processed).
  bool Changed = false;
  const std::vector<BasicBlock *> &Children = CurLoop->getBlocks();

  Relation *RL = new Relation();
  for (BasicBlock *Child : Children){
    BB = Child;
    DEBUG(dbgs() << "Analysis of block " << BB->getName() << " → " << BB << '\n');
    if (!CurLoop->contains(BB)){
      DEBUG(dbgs() << "---- Not In Current Loop " << '\n');
      // Here we should add conditions and phi's dependencies
      continue;
    }
    if(inSubLoop(BB, CurLoop, LI)){
      DEBUG(dbgs() << "In subLoop! " << '\n');
      Loop* InnerLoop = LI->getLoopFor(BB);
      if(InnerLoop->getHeader()==BB){
        // Add phi entry relations first !!!
        Relation* inneRPHI = getPHIRelations(InnerLoop,mapDeg,mapRel,&OC,true);
        RL = RL->composition(inneRPHI);

        if(Value* InnerHead = dyn_cast<Value>(InnerLoop->getHeader())){
          if(!(*mapRel)[InnerHead]){
            DEBUG(dbgs() << " Relation not found for Loop with Head = " <<
                  InnerHead <<'\n');
            (*mapRel)[InnerHead] =
              computeRelationLoop(DT->getNode(InnerLoop->getHeader()), mapDeg,
                                  mapRel, AA, LI, DT, TLI, InnerLoop, CurAST,
                                  SafetyInfo, DI);
          } else {
            DEBUG(dbgs() << " Relation found for Loop with Head = " << InnerHead
                  <<'\n');
          }
          (*mapDeg)[InnerHead]=0;
          OC.push_back(InnerHead);
          RL = RL->composition((*mapRel)[InnerHead]);
        } else
          DEBUG(dbgs() << " Fail cast InnerHead to Value! :" << '\n');
        continue;
      }
    }
    else if (CurLoop->getHeader()!=BB){ //TODO Optimize
      // TODO la généricité ici!
      Relation *RB =
        computeRelation(BB,mapDeg,mapRel,AA,DT,CurLoop,CurAST,SafetyInfo,&OC);
      if(BB->getUniqueSuccessor() == CurLoop->getHeader()){
        RB = RB->composition(RPHI);
      }
      // Deprecated… need something more polymorph
      computeDeg(mapDeg, OC, mapRel, DT);
      DEBUG(dumpMapDegOfOC(mapDeg,OC,dbgs()));
      RL = RL->composition(RB);
    }//End if subLoop
  }
  DEBUG(dbgs() << "\n Return RL :" << '\n');
  DEBUG(RL->dump(dbgs()));
  return RL;
}

/// Compute Relation for the Loop with fixpoint and cond correction
static Relation* computeRelationLoop(DomTreeNode *N, MapDeg*
                                         mapDeg, MapRel* mapRel, AliasAnalysis
                                         *AA, LoopInfo *LI, DominatorTree *DT,
                                         TargetLibraryInfo *TLI, Loop *CurLoop,
                                         AliasSetTracker *CurAST, LoopSafetyInfo
                                         *SafetyInfo, DependenceInfo *DI) {
    DEBUG(dbgs() <<"\n************ComputeRelationLoop***********\n");
    Relation *RPHI = getPHIRelations(CurLoop,mapRel,false);
    Relation *RL = computeRelationBodyLoop(DT->getNode(CurLoop->getHeader()),
                                           RPHI, mapDeg, mapRel, AA, LI, DT,
                                           TLI, CurLoop, CurAST, SafetyInfo,
                                           DI);
    // Take the while.end into account
    RL = fixPoint(RL);

    Relation *RCMP = getWhileCondRelations(CurLoop,mapRel);
    RL->addDependencies(RCMP->getIn(),RL->getOut());
    DEBUG(dbgs() << " FINAL LOOP OF DEPTH " << CurLoop->getLoopDepth() <<'\n');
    DEBUG(RL->dump(dbgs()));
    if(Value* Head = dyn_cast<Value>(CurLoop->getHeader()))
      (*mapRel)[Head]=RL;
    else 
      DEBUG(dbgs() << " Error dyn_cast Header in value " << '\n');
    return RL;
}

char LegacyLQICMPass::ID = 0;
static RegisterPass<LegacyLQICMPass> X("lqicm", "Loop quasi-Invariant Code Motion");

///
bool LoopInvariantCodeMotion::runOnLoop(Loop *L, AliasAnalysis *AA,
                                        LoopInfo *LI, DominatorTree *DT,
                                        TargetLibraryInfo *TLI,
                                        DependenceInfo *DI,
                                        ScalarEvolution *SE, bool DeleteAST) {
  bool Changed = false;

  assert(L->isLCSSAForm(*DT) && "Loop is not in LCSSA form.");

  AliasSetTracker *CurAST = collectAliasInfoForLoop(L, LI, AA);

  // Get the preheader block to move instructions into...
  BasicBlock *Preheader = L->getLoopPreheader();

  // Compute loop safety information.
  LoopSafetyInfo SafetyInfo;
  computeLoopSafetyInfo(&SafetyInfo, L);

  if (Preheader){
    Relation *RL = computeRelationLoop(DT->getNode(L->getHeader()), &mapDeg,
                                           &mapRel, AA, LI, DT, TLI, L, CurAST,
                                           &SafetyInfo, DI);
  }

  if (L->getParentLoop() && !DeleteAST)
    LoopToAliasSetMap[L] = CurAST;
  else
    delete CurAST;

  return Changed;
}

/// Computes loop safety information, checks loop body & header
/// for the possibility of may throw exception.
///
void llvm::computeLoopSafetyInfo(LoopSafetyInfo *SafetyInfo, Loop *CurLoop) {
  assert(CurLoop != nullptr && "CurLoop cant be null");
  BasicBlock *Header = CurLoop->getHeader();
  // Setting default safety values.
  SafetyInfo->MayThrow = false;
  SafetyInfo->HeaderMayThrow = false;
  // Iterate over header and compute safety info.
  for (BasicBlock::iterator I = Header->begin(), E = Header->end();
       (I != E) && !SafetyInfo->HeaderMayThrow; ++I)
    SafetyInfo->HeaderMayThrow |=
        !isGuaranteedToTransferExecutionToSuccessor(&*I);

  SafetyInfo->MayThrow = SafetyInfo->HeaderMayThrow;
  // Iterate over loop instructions and compute safety info.
  for (Loop::block_iterator BB = CurLoop->block_begin(),
                            BBE = CurLoop->block_end();
       (BB != BBE) && !SafetyInfo->MayThrow; ++BB)
    for (BasicBlock::iterator I = (*BB)->begin(), E = (*BB)->end();
         (I != E) && !SafetyInfo->MayThrow; ++I)
      SafetyInfo->MayThrow |= !isGuaranteedToTransferExecutionToSuccessor(&*I);

  // Compute funclet colors if we might sink/hoist in a function with a funclet
  // personality routine.
  Function *Fn = CurLoop->getHeader()->getParent();
  if (Fn->hasPersonalityFn())
    if (Constant *PersonalityFn = Fn->getPersonalityFn())
      if (isFuncletEHPersonality(classifyEHPersonality(PersonalityFn)))
        SafetyInfo->BlockColors = colorEHFunclets(*Fn);
}

bool llvm::canSinkOrHoistInst(Instruction &I, AAResults *AA, DominatorTree *DT,
                              Loop *CurLoop, AliasSetTracker *CurAST,
                              LoopSafetyInfo *SafetyInfo) {
    
  // Loads have extra constraints we have to verify before we can hoist them.
  if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
    if (!LI->isUnordered())
      return false; // Don't hoist volatile/atomic loads!

    // Loads from constant memory are always safe to move, even if they end up
    // in the same alias set as something that ends up being modified.
    if (AA->pointsToConstantMemory(LI->getOperand(0)))
      return true;
    if (LI->getMetadata(LLVMContext::MD_invariant_load))
      return true;

    // Don't hoist loads which have may-aliased stores in loop.
    uint64_t Size = 0;
    if (LI->getType()->isSized())
      Size = I.getModule()->getDataLayout().getTypeStoreSize(LI->getType());

    AAMDNodes AAInfo;
    LI->getAAMetadata(AAInfo);

    return !pointerInvalidatedByLoop(LI->getOperand(0), Size, AAInfo, CurAST);
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

  // Only these instructions are hoistable/sinkable.
  if (!isa<BinaryOperator>(I) && !isa<CastInst>(I) && !isa<SelectInst>(I) &&
      !isa<GetElementPtrInst>(I) && !isa<CmpInst>(I) &&
      !isa<InsertElementInst>(I) && !isa<ExtractElementInst>(I) &&
      !isa<ShuffleVectorInst>(I) && !isa<ExtractValueInst>(I) &&
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

/// Only sink or hoist an instruction if it is not a trapping instruction,
/// or if the instruction is known not to trap when moved to the preheader.
/// or if it is a trapping instruction and is guaranteed to execute.
static bool isSafeToExecuteUnconditionally(const Instruction &Inst,
                                           const DominatorTree *DT,
                                           const Loop *CurLoop,
                                           const LoopSafetyInfo *SafetyInfo,
                                           const Instruction *CtxI) {
  if (isSafeToSpeculativelyExecute(&Inst, CtxI, DT))
    return true;

  return isGuaranteedToExecute(Inst, DT, CurLoop, SafetyInfo);
}

/// Returns an owning pointer to an alias set which incorporates aliasing info
/// from L and all subloops of L.
/// FIXME: In new pass manager, there is no helper function to handle loop
/// analysis such as cloneBasicBlockAnalysis, so the AST needs to be recomputed
/// from scratch for every loop. Hook up with the helper functions when
/// available in the new pass manager to avoid redundant computation.
AliasSetTracker *
LoopInvariantCodeMotion::collectAliasInfoForLoop(Loop *L, LoopInfo *LI,
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
}

/// Simple analysis hook. Clone alias set info.
///
void LegacyLQICMPass::cloneBasicBlockAnalysis(BasicBlock *From, BasicBlock *To,
                                             Loop *L) {
  AliasSetTracker *AST = LQICM.getLoopToAliasSetMap().lookup(L);
  if (!AST)
    return;

  AST->copyValue(From, To);
}

/// Simple Analysis hook. Delete value V from alias set
///
void LegacyLQICMPass::deleteAnalysisValue(Value *V, Loop *L) {
  AliasSetTracker *AST = LQICM.getLoopToAliasSetMap().lookup(L);
  if (!AST)
    return;

  AST->deleteValue(V);
}

/// Simple Analysis hook. Delete value L from alias set map.
///
void LegacyLQICMPass::deleteAnalysisLoop(Loop *L) {
  AliasSetTracker *AST = LQICM.getLoopToAliasSetMap().lookup(L);
  if (!AST)
    return;

  delete AST;
  LQICM.getLoopToAliasSetMap().erase(L);
}

/// Return true if the body of this loop may store into the memory
/// location pointed to by V.
///
static bool pointerInvalidatedByLoop(Value *V, uint64_t Size,
                                     const AAMDNodes &AAInfo,
                                     AliasSetTracker *CurAST) {
  // Check to see if any of the basic blocks in CurLoop invalidate *V.
  return CurAST->getAliasSetForPointer(V, Size, AAInfo).isMod();
}

/// Little predicate that returns true if the specified basic block is in
/// a subloop of the current one, not the current one itself.
///
static bool inSubLoop(BasicBlock *BB, Loop *CurLoop, LoopInfo *LI) {
  assert(CurLoop->contains(BB) && "Only valid if BB is IN the loop");
  return LI->getLoopFor(BB) != CurLoop;
}
