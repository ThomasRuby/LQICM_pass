//===-                                                          -*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
//===----------------------------------------------------------------------===//
//
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_UTILS_LQICMUTILS_H
#define LLVM_TRANSFORMS_UTILS_LQICMUTILS_H

/* // Needed because we can't forward-declare the nested struct */
/* // TargetTransformInfo::UnrollingPreferences */
/* #include "llvm/Analysis/TargetTransformInfo.h" */
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AliasSetTracker.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/LoopPassManager.h"
#include "llvm/Analysis/LoopUnrollAnalyzer.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
/* #include <utility> */

using namespace llvm;

#define DEBUG_TYPE "lqicm"

// Relation object TODO should be somewhere else…
namespace {/*{-{*/

  typedef DenseMap<Value*,SmallPtrSet<Value*,8>> DepMap;
  typedef SmallPtrSet<Value*,8> VSet;
  typedef SmallPtrSet<Instruction*,8> ISet;
  typedef SmallPtrSet<BasicBlock*,8> BSet;
  typedef SmallDenseMap<Value*, int> MapDeg;

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

  ISet mergeISet(const ISet s1, const ISet s2){
    ISet s(s1);
    for (auto VV = s2.begin(), E = s2.end(); VV != E; ++VV) {
      Instruction* V = *VV;
      s.insert(V);
    }
    return s;
  }

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
      in.insert(v1);
      addVariable(v2);
      out.insert(v2);
      // No propagation anymore…
      propag.erase(v2);
    }


    void addOut(VSet s){
          for (auto VV = s.begin(), E = s.end(); VV != E; ++VV) {
            Value* V = *VV;
            out.insert(V);
          }
    }

    void addIn(VSet s){
          for (auto VV = s.begin(), E = s.end(); VV != E; ++VV) {
            Value* V = *VV;
            in.insert(V);
          }
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
        // Keep a trace of in and out variables would save some computation time
        // but use more space…
        addOut(sOut);
        in.insert(V);
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
      addOut(s);
      in.insert(v1);

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
      out.insert(v);
    }


    /// dump - For debugging purposes, dumps a dependence to OS.
    ///
    void dump(raw_ostream &OS){
      DEBUG(dbgs() << "\n---- dumpRelation ----\n ");
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

    /* VSet getOut(){ */
    /*   VSet out(init); // All initializations are out variables */
    /*   for(auto D = dep.begin(), DE = dep.end(); D != DE; ++D){ */
    /*     out = mergeVSet(out,D->second); */
    /*   } */
    /*   return out; */
    /* } */

    /* VSet getIn(){ */
    /*   VSet in; */
    /*   for(auto D = dep.begin(), DE = dep.end(); D != DE; ++D){ */
    /*     in.insert(D->first); */
    /*   } */
    /*   return in; */
    /* } */

    /* std::pair<VSet,VSet> getInOut(){ */
    /*   VSet out(init); // All initializations are out variables */
    /*   VSet in; */
    /*   for(auto D = dep.begin(), DE = dep.end(); D != DE; ++D){ */
    /*     in.insert(D->first); */
    /*     out = mergeVSet(out,D->second); */
    /*   } */
    /*   return std::make_pair(in, out); */
    /* } */

    std::pair<VSet,VSet> getInOut(){
      return std::make_pair(in, out);
    }

    VSet getInstructions(){
      return instructions;
    }

    DepMap getDep(){
      return dep;
    }

    VSet getOut(){
      return out;
    }

    VSet getIn(){
      return in;
    }

  private:
    VSet instructions;
    VSet variables;
    VSet in;
    VSet out;
    VSet propag;
    DepMap dep;
    /* DenseMap<Value*,VSet> dep; */
    VSet init;

  }; // End Relation

  typedef SmallDenseMap<Value*, Relation*> MapRel;
  typedef SmallDenseMap<Value*, MapRel*> MapLoopRel;
  typedef SmallDenseMap<Value*, MapDeg*> MapLoopDeg;
  typedef SmallPtrSet<Relation*,8> RSet;

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

VSet searchForRelationsWithVAsOutput(Value* V, MapRel* mapRel){
  VSet relations;
  for(auto R = mapRel->begin(), RE = mapRel->end(); R != RE; ++R){
    if(R->first == V)
      relations.insert(R->first);
    else
      if(R->second->getOut().count(V))
        relations.insert(R->first);
  }
  return relations;
}

static void dumpMapDegOfOC(MapLoopRel *mapLoopRel, MapDeg* mapDeg,
                           std::vector<Value*> OC, raw_ostream &OS){
    DEBUG(dbgs() << "\n---- MapDegOfOC ----\n ");
    for(Value* I : OC){
      DEBUG(dbgs() << "Compute Deg for : " << *I << " = ");
      DEBUG(dbgs() << (*mapDeg)[I]);
      if((*mapLoopRel)[I])
        DEBUG(dbgs() << "\n\tit's an innerBlock ↑ ");
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
    Relation *RCMP;
    bool hasRCMP = false;
    for (BasicBlock::iterator II = BB->end(), E = BB->begin(); II != E;) {
      Instruction &I = *--II;
      DEBUG(dbgs() << "Treating: " << I << " … " << '\n');

      if (isa<CmpInst>(&I)) {
        if(hasRCMP){
          DEBUG(dbgs() << "ERROR: 2 CMP in while.cond? " << '\n');
          // What do we do in this case? FIXME
        }
        RCMP = new Relation(&I);
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
          continue;
          // What do we do in this case? FIXME
        }
        bool contains_cmp_variables = false;
        for(auto OP = I.op_begin(), E = I.op_end(); OP!=E;){
          Value *v = OP->get();
          if(RCMP->getIn().count(v))
            contains_cmp_variables = true;
          OP++;
        }
        if(contains_cmp_variables){
          Relation *RI = new Relation(&I);
          // Save relation with instruction
          (*mapRel)[&I] = RI;
          DEBUG(RI->dump(dbgs()));
          DEBUG(dbgs() << " Composition…" << '\n');
          RB = RI->composition(RB);
          DEBUG(RB->dump(dbgs()));
        } else {
          DEBUG(dbgs() << " ↑ does not contain variables in CMP" << '\n');
        }
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
      } else {
        DEBUG(dbgs() << " ↑ not a PHI inst" << '\n');
      }
    }//End of For II in BB
    if(RB->getInstructions().empty())
      return nullptr;
    else
      return RB;
}

// Return the good relation from phi regarding to the BasicBlocks From and To
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


// Return the good relation from phi going from the body to the header
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

    Function &F = *L->getHeader()->getParent();
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

namespace llvm {

class StringRef;
class DominatorTree;
class Loop;
class LoopInfo;
class Pass;
class ScalarEvolution;

bool mypeelLoop(Loop *L, unsigned PeelCount, MapLoopDeg *mapLoopDeg, LoopInfo
                *LI, ScalarEvolution *SE, DominatorTree *DT, PostDominatorTree
                *PDT, bool PreserveLCSSA);
}

/// Little predicate that returns true if the specified basic block is in
/// a subloop of the current one, not the current one itself.
///
static bool inSubLoop(BasicBlock *BB, Loop *CurLoop, LoopInfo *LI) {/*{-{*/
  assert(CurLoop->contains(BB) && "Only valid if BB is IN the loop");
  return LI->getLoopFor(BB) != CurLoop;
}/*}-}*/


#endif

