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
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include <utility>
using namespace llvm;

#define DEBUG_TYPE "lqicm"

// Relation object TODO should be somewhere else…
namespace {/*{-{*/

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

    // We may have to do something different…
    Relation(PHINode *PHI, BasicBlock *From){ 
      // In which case we consider I ?
      instructions.insert(PHI);
      addPropag(PHI);
      DEBUG(dbgs() << "\tNew Instruction\t" << " = \t" << PHI << '\n');
      unsigned i=0;
      bool onlyConst = true;
      for(auto OP = PHI->op_begin(), E = PHI->op_end(); OP!=E;){
        Value *v = OP->get();
        DEBUG(dbgs() << "\t\toperand \t" << v->getName());
        DEBUG(dbgs() << "\t → \t" << v << '\n');
        DEBUG(dbgs() << "\t Block → \t" << PHI->getIncomingBlock(i)->getName()
              << '\n');
        bool isIn = (PHI->getIncomingBlock(i) == From);
        // Take initialisation into account !
        if(isIn){
          if(!isa<Constant>(v)){
            addPropag(v);
            addDependence(v,PHI);
            onlyConst = false;
          } else{
            addInit(PHI);
          }
        }
        OP++;
        i++;
      }// End for
      if(onlyConst) // If only const operands it's a Init
        addInit(PHI);
    }

    // We may have to do something different…
    Relation(PHINode *PHI, Loop *L, bool WantIn){ 
      // In which case we consider I ?
      instructions.insert(PHI);
      addPropag(PHI);
      DEBUG(dbgs() << "\tNew Instruction\t" << " = \t" << PHI << '\n');
      unsigned i=0;
      bool onlyConst = true;
      for(auto OP = PHI->op_begin(), E = PHI->op_end(); OP!=E;){
        Value *v = OP->get();
        DEBUG(dbgs() << "\t\toperand \t" << v->getName());
        DEBUG(dbgs() << "\t → \t" << v << '\n');
        DEBUG(dbgs() << "\t Block → \t" << PHI->getIncomingBlock(i)->getName()
              << '\n');
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
          DEBUG(dbgs() << "\t\toperand \t" << v->getName());
          DEBUG(dbgs() << "\t → \t" << v << '\n');
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
      /* DEBUG(dbgs() << " Composition is called… " << '\n'); */
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
        /* DEBUG(dbgs() << " Composition de "  << '\t' << X2->getName() << ":"); */
        /* DEBUG(printValues(spt2,dbgs())); */
        /* DEBUG(dbgs() << " Mes variables "  << '\n'); */
        /* DEBUG(printValues(variables,dbgs())); */
        if(!variables.count(X2)){ // Not in r1 variables
          /* DEBUG(dbgs() << " X2 not in R1 vars…" << '\n'); */
          comp->addDependencies(X2,spt2); // All dep are taken
          /* DEBUG(printValues(comp->dep[X2],dbgs())); */
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
              comp->propag.erase(X2);
              continue;
            }
            else if(!r2->variables.count(Y1)){
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
    /* DenseMap<Value*,VSet> dep; */
    VSet init;

  }; // End Relation

  typedef SmallDenseMap<Value*, Relation*> MapRel;
  typedef SmallDenseMap<Value*, MapRel*> MapLoopRel;
  typedef SmallDenseMap<Value*, MapDeg*> MapLoopDeg;

struct LoopInvariantCodeMotion {
  bool runOnLoop(Loop *L, AliasAnalysis *AA, LoopInfo *LI, DominatorTree *DT,
                 TargetLibraryInfo *TLI, DependenceInfo *DI, PostDominatorTree
                 *PDT, ScalarEvolution *SE, bool DeleteAST);

  DenseMap<Loop *, AliasSetTracker *> &getLoopToAliasSetMap() {
    return LoopToAliasSetMap;
  }
  MapLoopDeg &getMapLoopDeg() {
    return mapLoopDeg;
  }
  MapLoopRel &getMapLoopRel() {
    return mapLoopRel;
  }

private:
  MapLoopDeg mapLoopDeg;
  MapLoopRel mapLoopRel;

  DenseMap<Loop *, AliasSetTracker *> LoopToAliasSetMap;

  AliasSetTracker *collectAliasInfoForLoop(Loop *L, LoopInfo *LI,
                                           AliasAnalysis *AA);
};

static void dumpMapDegOfOC(MapLoopRel *mapLoopRel, MapDeg* mapDeg,
                           std::vector<Value*> OC, raw_ostream &OS){
    DEBUG(dbgs() << "\n---- MapDegOfOC ----\n ");
    for(Value* I : OC){
      DEBUG(dbgs() << "Compute Deg for : " << *I << " = ");
      DEBUG(dbgs() << (*mapDeg)[I]);
      if((*mapLoopRel)[I])
        DEBUG(dbgs() << "\n\tit's an innerBloc ↑ ");
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
static Relation* getCondRelationsFromBB(BasicBlock* BB, MapRel* mapRel){
    DEBUG(dbgs() << "In getCondRelationsFromBB : " << '\n');
    Relation *RB = new Relation(BB);
    bool hasRCMP = false;
    for (BasicBlock::iterator II = BB->end(), E = BB->begin(); II != E;) {
      Instruction &I = *--II;
      DEBUG(dbgs() << "Treating: " << I << " … " << '\n');

      if (isa<CmpInst>(&I)) {
        if(hasRCMP){
          DEBUG(dbgs() << "ERROR: 2 CMP in while.cond? " << '\n');
          // What do we do in this case? FIXME
        }
        Relation *RCMP = new Relation(&I);
        // Save relation with instruction
        (*mapRel)[&I] = RCMP;
        DEBUG(RCMP->dump(dbgs()));
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
          DEBUG(RI->dump(dbgs()));
          DEBUG(dbgs() << " Composition…" << '\n');
          RB = RI->composition(RB);
          DEBUG(RB->dump(dbgs()));
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
    DEBUG(dbgs() << "In getPHIRelations : " << '\n');
    Relation *RB = new Relation(BB);
    for (BasicBlock::iterator II = BB->begin(), E = BB->end(); II != E;) {
      Instruction &I = *II++;
      DEBUG(dbgs() << "Treating: " << I << " … " << '\n');

      if (PHINode *PHI = dyn_cast<PHINode>(&I)) {
        Relation *RI = new Relation(PHI,L,WantIn);
        // Save relation with instruction
        (*mapRel)[&I] = RI;
        if(WantIn)
          (*mapDeg)[&I] = 0;
        DEBUG(RI->dump(dbgs()));
        DEBUG(dbgs() << " Composition…" << '\n');
        OC->push_back(&I);
        RB = RB->composition(RI);
        DEBUG(RB->dump(dbgs()));
      }
    }//End of For II in BB
    if(RB->getInstructions().empty())
      return nullptr;
    else
      return RB;
}

// Return Relation composed for the given BasicBlock FIXME Polymorphism!
static Relation* getPHIRelations(BasicBlock* From, BasicBlock* To, MapRel*
                                 mapRel){
    DEBUG(dbgs() << "In getPHIRelations : " << '\n');
    Relation *RB = new Relation(To);
    for (BasicBlock::iterator II = To->begin(), E = To->end(); II != E;) {
      Instruction &I = *II++;
      DEBUG(dbgs() << "Treating: " << I << " … " << '\n');

      if (PHINode *PHI = dyn_cast<PHINode>(&I)) {
        Relation *RI = new Relation(PHI,From);
        // Save relation with instruction
        (*mapRel)[&I] = RI;
        DEBUG(RI->dump(dbgs()));
        DEBUG(dbgs() << " Composition…" << '\n');
        RB = RB->composition(RI);
        DEBUG(RB->dump(dbgs()));
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
    DEBUG(dbgs() << "In getPHIRelations : " << '\n');
    Relation *RB = new Relation(BB);
    for (BasicBlock::iterator II = BB->begin(), E = BB->end(); II != E;) {
      Instruction &I = *II++;
      DEBUG(dbgs() << "Treating: " << I << " … " << '\n');

      if (PHINode *PHI = dyn_cast<PHINode>(&I)) {
        Relation *RI = new Relation(PHI,L,WantIn);
        // Save relation with instruction
        (*mapRel)[&I] = RI;
        DEBUG(RI->dump(dbgs()));
        DEBUG(dbgs() << " Composition…" << '\n');
        RB = RB->composition(RI);
        DEBUG(RB->dump(dbgs()));
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
                           &getAnalysis<PostDominatorTreeWrapperPass>().getPostDomTree(),
                           SE ? &SE->getSE() : nullptr, false); }

  /// This transformation requires natural loop information & requires that
  /// loop preheaders be inserted into the CFG...
  ///
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesCFG();
    AU.addRequired<TargetLibraryInfoWrapperPass>();
    AU.addRequired<DependenceAnalysisWrapperPass>();
    AU.addRequired<PostDominatorTreeWrapperPass>();
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
}/*}-}*/

// Function from LQICM
static bool inSubLoop(BasicBlock *BB, Loop *CurLoop, LoopInfo *LI);/*{-{*/
static bool isNotUsedInLoop(const Instruction &I, const Loop *CurLoop,
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
/* static Relation* computeRelationBodyLoop(DomTreeNode *N, Relation *RPHI, MapLoopDeg* */
/*                                          mapDeg, MapRel* mapRel, AliasAnalysis */
/*                                          *AA, LoopInfo *LI, DominatorTree *DT, */
/*                                          TargetLibraryInfo *TLI, Loop *CurLoop, */
/*                                          AliasSetTracker *CurAST, LoopSafetyInfo */
/*                                          *SafetyInfo, DependenceInfo *DI); */
static Relation* computeRelationLoop(DomTreeNode *N, MapLoopDeg* mapDeg, MapLoopRel*
                                     mapRel, AliasAnalysis *AA, LoopInfo *LI,
                                     DominatorTree *DT, TargetLibraryInfo *TLI,
                                     Loop *CurLoop, AliasSetTracker *CurAST,
                                     LoopSafetyInfo *SafetyInfo, DependenceInfo
                                     *DI, PostDominatorTree *PDT);
// Computes fixpoint relation (for loops)
static Relation* fixPoint(Relation* R){/*{-{*/
  Relation* r = new Relation();
  Relation* nextR(R);
  while(!r->isEqual(nextR)){
    r = nextR;
    nextR=r->composition(R)->sumRelation(R);
  }
  return r;
}
/*}-}*/
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

// Dinamically computes the invariance degrees
static int computeDeg(MapDeg* mapDeg, Value* I, MapRel* mapRel, DominatorTree *DT){/*{-{*/
  DEBUG(dbgs() << "\nINFO… " << I << " Computation degree…" << '\n');
  if((*mapDeg)[I]){
    DEBUG(dbgs() << " Already in mapDeg " << '\n');
    return (*mapDeg)[I];
  }
  else{
    (*mapDeg)[I]=-1;
    if(!mapRel->count(I)){
      DEBUG(dbgs() << "\nINFO… " << I << " has not been visited" << '\n');
      (*mapDeg)[I]=0;
      return 0;
    }
    else{
      Relation* RI = (*mapRel)[I];
      DEBUG(dbgs() << " Relation found: " << '\n');
      DEBUG(RI->dump(dbgs()));
      if(RI->getDep().empty()){ // Empty dep
        DEBUG(dbgs() << " No dependence ");
        (*mapDeg)[I]=1;
        return 1;
      }
      else{
        Value* instMax;
        int degMax=-1;
        VSet inInst = RI->getIn();
        DEBUG(dbgs() << " Compute deg on dependencies ");
        for (auto VV = inInst.begin(), E = inInst.end(); VV != E; ++VV) {
          Value* V = *VV;
          (*mapDeg)[I]=computeDeg(mapDeg,V,mapRel,DT);
          if((*mapDeg)[I]>=degMax)
            degMax=(*mapDeg)[I];
            instMax = V;
        }
        // Bof! FIXME
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
}/*}-}*/

// Sub functions
static MapDeg* computeDeg(MapDeg* mapDeg, std::vector<Value*> OC, MapRel*/*{-{*/
                          mapRel, DominatorTree *DT){
    for(Value* I : OC){
      DEBUG(dbgs() << "Compute Deg for : " << *I << " = ");
      DEBUG(dbgs() << computeDeg(mapDeg,I,mapRel,DT));
      DEBUG(dbgs() << '\n');
    }
}/*}-}*/

// Sub functions
static MapDeg* computeDeg(MapDeg* mapDeg, BasicBlock* BB, MapRel* mapRel,/*{-{*/
                          DominatorTree *DT){
    for (BasicBlock::iterator II = BB->begin(), E = BB->end(); II != E;) {
      Instruction &I = *II++;
      DEBUG(dbgs() << "Compute Deg for : " << I << " = ");
      DEBUG(dbgs() << computeDeg(mapDeg,&I,mapRel,DT));
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

// TODO too much useless args… it's a prototype…
static Relation* computeRelationBBInLoop(BasicBlock *BB, BasicBlock *End,
                                         Relation *RPHI, MapLoopDeg* mapLoopDeg, MapLoopRel*
                                         mapLoopRel, AliasAnalysis *AA, LoopInfo
                                         *LI, DominatorTree *DT,
                                         TargetLibraryInfo *TLI, Loop *CurLoop,
                                         AliasSetTracker *CurAST, LoopSafetyInfo
                                         *SafetyInfo, DependenceInfo *DI,
                                         PostDominatorTree *PDT,
                                         std::vector<Value*> *OC){

  Relation *RB = new Relation();
  
  // If we are here, it works
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
    // Then don't tuch the mapRel of the loop but of the current If
    mapRel = (*mapLoopRel)[bb];
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
        if(!(*(*mapLoopRel)[InnerHead])[InnerHead]){
          DEBUG(dbgs() << " ERROR! Relation not found for Loop with Head = " <<
                InnerHead <<'\n');
          /* (*(*mapLoopRel)[head])[InnerHead] = */
          /*   computeRelationLoop(DT->getNode(InnerLoop->getHeader()), mapLoopDeg, */
          /*                       mapLoopRel, AA, LI, DT, TLI, InnerLoop, CurAST, */
          /*                       SafetyInfo, DI, PDT); */
        } else {
          DEBUG(dbgs() << " Relation found for Loop with Head = " << InnerHead
                <<'\n');
          DEBUG((*(*mapLoopRel)[InnerHead])[InnerHead]->dump(dbgs()));
          (*(*mapLoopRel)[head])[InnerHead] = (*(*mapLoopRel)[InnerHead])[InnerHead];
        }
        // Initialization: we suppose the loop is hoistable
        (*(*mapLoopDeg)[head])[InnerHead]=0; 
        OC->push_back(InnerHead);
        RL = RL->composition((*(*mapLoopRel)[head])[InnerHead]);

        // Continue by treating while.end
        if(BasicBlock* WhileEnd = InnerLoop->getExitBlock()){
          DEBUG(dbgs() << " INFO: Exit Block is :" << WhileEnd->getName() << '\n');
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
  if(nbSucc==2){
    BasicBlock *Then = TInst->getSuccessor(0);
    BasicBlock *Else = TInst->getSuccessor(1);
      if(isWellFormedFork(Then,Else,CurLoop,PDT,DT)){
        BasicBlock *IfEnd = PDT->findNearestCommonDominator(Then,Else);
        DEBUG(dbgs() << " INFO: Exit Block of if is :" << IfEnd->getName() <<
              '\n');

        /* MapDeg *mapThenDeg = new MapDeg(); */
        /* MapDeg *mapElseDeg = new MapDeg(); */
        MapRel *mapThenRel = new MapRel();
        MapRel *mapElseRel = new MapRel();
        std::vector<Value*> OCif;

        Value* VThen = dyn_cast<Value>(Then);
        Value* VElse = dyn_cast<Value>(Else);

        /* (*mapLoopDeg)[VThen] = mapThenDeg; */
        /* (*mapLoopDeg)[VElse] = mapElseDeg; */
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

        // Compute Phi outputs
        Relation *RThenToEndPHI = getPHIRelations(Then,IfEnd,mapRel);
        Relation *RElseToEndPHI = getPHIRelations(Else,IfEnd,mapRel);

        // Add Phi outputs
        RThen = RThen->composition(RThenToEndPHI);
        RElse = RElse->composition(RElseToEndPHI);

        // Sum branchs
        RB = RB->composition(RThen->sumRelation(RElse));

        // Here RB is the relation of the If but we need to add conditions dep
        Relation *RCMP = getCondRelationsFromBB(BB,mapRel);
        RB->addDependencies(RCMP->getIn(),RB->getOut());

        /* (*mapRel)[VThen] = RB; */
        /* (*mapRel)[VElse] = RB; */

        DEBUG(dbgs() << " FINAL Branch from " << TInst << '\n');
        DEBUG(RB->dump(dbgs()));

        (*mapDeg)[TInst] = 0;
        (*mapRel)[TInst] = RB; // Useless FIXME
        (*mapLoopRel)[TInst] = new MapRel();
        (*(*mapLoopRel)[TInst])[TInst] = RB;

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
        // TODO to check
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
}


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

      // Deprecated
      /* Relation *RL = computeRelationBodyLoop2(DT->getNode(CurLoop->getHeader()), */
      /*                                        RPHI, mapDeg, mapRel, AA, LI, DT, */
      /*                                        TLI, CurLoop, CurAST, SafetyInfo, */
      /*                                        DI,&OC); */

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

      // Deprecated… need something more polymorph
      // FIXME
      computeDeg((*mapLoopDeg)[head], OC, (*mapLoopRel)[head], DT);
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

///
bool LoopInvariantCodeMotion::runOnLoop(Loop *L, AliasAnalysis *AA,/*{-{*/
                                        LoopInfo *LI, DominatorTree *DT,
                                        TargetLibraryInfo *TLI,
                                        DependenceInfo *DI,
                                        PostDominatorTree *PDT,
                                        ScalarEvolution *SE, bool DeleteAST) {
  bool Changed = false;

  assert(L->isLCSSAForm(*DT) && "Loop is not in LCSSA form.");

  AliasSetTracker *CurAST = collectAliasInfoForLoop(L, LI, AA);
  DEBUG(dbgs() <<"*********************AliasSetTracker*****************\n");
  CurAST->dump();

  // Get the preheader block to move instructions into...
  BasicBlock *Preheader = L->getLoopPreheader();
  DEBUG(dbgs() <<"*********************PreheaderBlock******************\n");
  Preheader->dump();

  // Compute loop safety information.
  LoopSafetyInfo SafetyInfo;
  computeLoopSafetyInfo(&SafetyInfo, L);

  if (Preheader){
    if(Value* head = dyn_cast<Value>(L->getHeader())){
      MapRel *mapRel = new MapRel();
      MapDeg *mapDeg = new MapDeg();

      mapLoopRel[head] = mapRel;
      mapLoopDeg[head] = mapDeg;

      Relation *RL = computeRelationLoop(DT->getNode(L->getHeader()), &mapLoopDeg,
                                         &mapLoopRel, AA, LI, DT, TLI, L, CurAST,
                                         &SafetyInfo, DI, PDT);
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

/// Little predicate that returns true if the specified basic block is in
/// a subloop of the current one, not the current one itself.
///
static bool inSubLoop(BasicBlock *BB, Loop *CurLoop, LoopInfo *LI) {/*{-{*/
  assert(CurLoop->contains(BB) && "Only valid if BB is IN the loop");
  return LI->getLoopFor(BB) != CurLoop;
}/*}-}*/
