//===-                                                          -*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
//===----------------------------------------------------------------------===//
//
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_UTILS_LQICM_H
#define LLVM_TRANSFORMS_UTILS_LQICM_H

/* // Needed because we can't forward-declare the nested struct */
/* // TargetTransformInfo::UnrollingPreferences */
/* #include "llvm/Analysis/TargetTransformInfo.h" */
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AliasSetTracker.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopPass.h"
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
#include "llvm/Transforms/Scalar/LoopPassManager.h"

#include "llvm/Analysis/LoopIterator.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include <algorithm>
/* #include <utility> */

using namespace llvm;

#define DEBUG_TYPE "lqicm"

STATISTIC(NumQuasiInvariants, "Number of instructions with deg != -1");
STATISTIC(NumLoops, "Number of time runOnLoop is performed…");
STATISTIC(NumLoopsManyExitB, "Number Loop with severals ExitBlock → LQICM Aborted…");
STATISTIC(NumLoopsManyLatch, "Number Loop with severals Latch → LQICM Aborted…");
STATISTIC(NumQuasiInvariantsBlocks, "Number of innerBlocks with deg != -1");
STATISTIC(SumDegQIBlocks, "Sum of all degrees for chunks != -1");
STATISTIC(SumDegs, "Sum of all degrees != -1");
STATISTIC(NumError, "Number of loops not analyzed…");

// Relation object TODO should be somewhere else…
namespace llvm {/*{-{*/

  typedef DenseMap<Value*,SmallPtrSet<Value*,8>> DepMap;
  typedef SmallPtrSet<Value*,8> VSet;
  typedef SmallPtrSet<Instruction*,8> ISet;
  typedef SmallPtrSet<BasicBlock*,8> BSet;
  typedef DenseMap<Value*, int> MapDeg;

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
      if(V)
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
    void setInit(VSet v) { init = v; }
    void setDep(DepMap d) { dep = d; }

  public:
    Relation(){
      peeled = false;
      branch = false;
      anchor = false;
    }
    ~Relation(){
      instructions.clear();
      assert(instructions.empty() &&
             "Didn't free instructions in relation");
      variables.clear();
      assert(variables.empty() &&
             "Didn't free instructions in relation");
      in.clear();
      assert(in.empty() &&
             "Didn't free instructions in relation");
      out.clear();
      assert(out.empty() &&
             "Didn't free instructions in relation");
      propag.clear();
      assert(propag.empty() &&
             "Didn't free instructions in relation");
      dep.shrink_and_clear();
      assert(dep.empty() &&
             "Didn't free instructions in relation");
      init.clear();
      assert(init.empty() &&
             "Didn't free instructions in relation");
      Start = nullptr;
      End = nullptr;
    }

    // We may have to do something different…
    Relation(PHINode *PHI, BasicBlock *From){ 
      DEBUG(dbgs() << "\tPhi Relations from " << From->getName() <<"\n");
      DEBUG(dbgs() << "\tNew Instruction\t" << " = \t" << PHI << '\n');
      unsigned i=0;
      for(auto OP = PHI->op_begin(), E = PHI->op_end(); OP!=E;){
        Value *v = OP->get();
        DEBUG(dbgs() << "\t\toperand \t" << v->getName());
        DEBUG(dbgs() << "\t → \t" << v << '\n');
        DEBUG(dbgs() << "\t Block → \t" << PHI->getIncomingBlock(i)->getName()
              << '\n');
        bool isIn = (PHI->getIncomingBlock(i) == From);
        // Take initialisation into account !
        if(isIn){
          DEBUG(dbgs() << "\tInstruction is from: \n" << *From << '\n');
          instructions.insert(PHI);
          addPropag(PHI);
          if(!isa<Constant>(v)){
            addPropag(v);
            addDependence(v,PHI);
          } else{
            addInit(PHI);
          }
          break;
        }
        OP++;
        i++;
      }// End for
      peeled = false;
      branch = false;
      anchor = false;
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
      peeled = false;
      branch = false;
      anchor = false;
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
      peeled = false;
      branch = false;
      anchor = false;
    }

    Relation(Value* v) {
      instructions.insert(v);
      peeled = false;
      branch = false;
      anchor = false;
    }

    Relation(VSet variables) {
      for (auto VV = variables.begin(), E = variables.end(); VV != E; ++VV) {
        Value* V = *VV;
        instructions.insert(V);
        addPropag(V);
      }
      peeled = false;
      branch = false;
      anchor = false;
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
      /* OS << "Instructions:" << '\n'<< '\t'; */
      /* if(!instructions.empty()){ */
      /*   for (auto VV = instructions.begin(), E = instructions.end(); VV != E; ++VV) { */
      /*     Value* V = *VV; */
      /*     if(Instruction *I = dyn_cast<Instruction>(V)){ */
      /*       OS << "(instruction:"<< I << ':' << *I << ")\n"; */
      /*     } */
      /*     else if(BasicBlock* B = dyn_cast<BasicBlock>(V)){ */
      /*       OS << "(BasicBlock:"<< B << ":\n" << *B << ")\n"; */
      /*     } */
      /*     else { */ 
      /*     OS << '(' << V << ':' << V->getName() << "),"; */
      /*     } */
      /*   } */
      /* } */
      OS << "\nVariables:" << '\n'<< '\t';
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
      comp->setInit(mergeVSet(init,r2->init));
      if(isAnchor() || r2->isAnchor())
        comp->setAnchor(true);
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
              comp->addDependence(X1,Y1);
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
      sum->setInit(mergeVSet(init,r2->init));

      if(isAnchor() || r2->isAnchor())
        sum->setAnchor(true);

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

    // TODO We can optimize that by feeding in and out set when adding depends
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

    /* std::pair<VSet,VSet> getInOut(){ */
    /*   return std::make_pair(in, out); */
    /* } */

    VSet getInstructions(){
      return instructions;
    }

    DepMap getDep(){
      return dep;
    }

    /* VSet getOut(){ */
    /*   return out; */
    /* } */

    /* VSet getIn(){ */
    /*   return in; */
    /* } */

    bool isPeeled(){
      return peeled;
    }

    void setPeeled(bool p){
      peeled = p;
    }

    bool isAnchor(){
      return anchor;
    }

    void setAnchor(bool p){
      anchor = p;
    }

    bool isBranch(){
      return branch;
    }

    void setBranch(bool b){
      branch = b;
    }

    BasicBlock* getStart(){
      return Start;
    }

    BasicBlock* getEnd(){
      return End;
    }

    void setStart(BasicBlock* s){
      Start = s;
    }

    void setEnd(BasicBlock* e){
      End = e;
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
    bool peeled;
    bool anchor;
    BasicBlock* Start;
    BasicBlock* End;
    bool branch;

  }; // End Relation

  typedef DenseMap<Value*, Relation*> MapRel;
  typedef SmallPtrSet<Relation*,8> RSet;

  class Chunk {
  protected:
    Chunk(Chunk &&) = default;
    Chunk &operator=(Chunk &&) = default;

  public:
    Chunk(){
      mapDeg = new MapDeg();
      mapRel = new MapRel();
      peeled = false;
      anchor = false;
      type = NORMAL;
    }

    Chunk(StringRef str){
      mapDeg = new MapDeg();
      mapRel = new MapRel();
      peeled = false;
      anchor = false;
      type = NORMAL;
      name = str;
    }
    ~Chunk(){
      delete myRelation;
      delete mapDeg;
      delete mapRel;
      Start = nullptr;
      End = nullptr;
    }

    enum ChunkType { 
      BRANCH,
      FORK,
      LOOP,
      NORMAL,
      ERROR,
    };

    bool isPeeled(){
      return peeled;
    }

    void setPeeled(bool p){
      peeled = p;
    }

    bool isAnchor(){
      return anchor;
    }

    void setAnchor(bool p){
      anchor = p;
    }

    ChunkType getType(){
      return type;
    }

    void setType(ChunkType ty){
      type = ty;
    }

    BasicBlock* getStart(){
      return Start;
    }

    BasicBlock* getEnd(){
      return End;
    }

    void setStart(BasicBlock* s){
      Start = s;
    }

    void setEnd(BasicBlock* e){
      End = e;
    }

    MapDeg* getMapDeg(){
      return mapDeg;
    }

    MapRel* getMapRel(){
      return mapRel;
    }

    Relation* getRel(){
      return myRelation;
    }

    void setRel(Relation* relation){
      myRelation = relation;
    }

    int getDegree(){
      return degree;
    }

    void setDegree(int deg){
      degree = deg;
    }

    StringRef getName(){
      return name;
    }

    void setName(StringRef str){
      name = str;
    }

    void shrink_and_clear(){
      mapDeg->shrink_and_clear();
      mapRel->shrink_and_clear();//should do more TODO
      //Delete myRelation too
      Start = nullptr;
      End = nullptr;
    }

  private:
    StringRef name;
    Relation* myRelation;
    int degree;
    MapDeg* mapDeg;
    MapRel* mapRel;
    BasicBlock* Start;
    BasicBlock* End;
    bool peeled;
    bool anchor;
    ChunkType type;

  }; // End Chunk

  typedef SmallDenseMap<Value*, Chunk*> MapChunk;

  struct LoopInvariantCodeMotion {
    bool runOnLoop(Loop *L, AliasAnalysis *AA, LoopInfo *LI, DominatorTree *DT,
                   DependenceInfo *DI, PostDominatorTree *PDT, ScalarEvolution
                   *SE, bool DeleteAST);

    DenseMap<Loop *, AliasSetTracker *> &getLoopToAliasSetMap() {
      return LoopToAliasSetMap;
    }
    MapChunk &getMapChunk() {
      return mapChunk;
    }

  private:
    MapChunk mapChunk;

    DenseMap<Loop *, AliasSetTracker *> LoopToAliasSetMap;

    AliasSetTracker *collectAliasInfoForLoop(Loop *L, LoopInfo *LI,
                                             AliasAnalysis *AA);
  };

  VSet searchForRelationsWithVAsOutput(Value* V, MapRel* mapRel){
    VSet relations;
    for(auto R = mapRel->begin(), RE = mapRel->end(); R != RE; ++R){
      // Does that save some time?
      if(R->first == V)
        relations.insert(R->first);
      else
        if(R->second->getOut().count(V))
          relations.insert(R->first);
    }
    return relations;
  }

  static void dumpMapDegOfOC(MapChunk *mapChunk, MapDeg* mapDeg,
                             std::vector<Value*> *OC, raw_ostream &OS){
    DEBUG(dbgs() << "\n---- MapDegOfOC ----\n ");
    for(Value* I : *OC){
      DEBUG(dbgs() << "Compute Deg for : " << *I << " = ");
      DEBUG(dbgs() << (*mapDeg)[I]);
      if((*mapDeg)[I] != -1){
        NumQuasiInvariants++;
        SumDegs+=(*mapDeg)[I];
      }
      if((*mapChunk)[I]){
        DEBUG(dbgs() << "\n\t↑ It's the beginning of an inner Chunk with end "
              << ((*mapChunk)[I])->getEnd()->getName() << " ↑ ");
        // If deg is not infinty and it doesn't contains a anchor
        if((*mapDeg)[I] != -1 && !(*mapChunk)[I]->isAnchor()){
          SumDegQIBlocks+=(*mapDeg)[I];
          NumQuasiInvariantsBlocks++;
        }
      }
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

  static Relation* getBURelationOfValueInBB(Instruction* V, BasicBlock* BB, MapRel*
                                            mapRel){
    Relation *RB = new Relation(V);
    DEBUG(dbgs() << "getting Relation of a value Bottom Up strategy : " << '\n');
    for(auto OP = V->op_begin(), E = V->op_end(); OP!=E;){
      Value *v = OP->get();
      DEBUG(dbgs() << "Treating uses: " << *v << " … " << '\n');
      if(Instruction* I = dyn_cast<Instruction>(v)){
        if(!isa<PHINode>(*I) && I->getParent() == BB){
          Relation* RCMP = new Relation(I);
          (*mapRel)[I] = RCMP;
          DEBUG(RCMP->dump(dbgs()));
          RB = RCMP->composition(RB);
          // Rec call
          RB = getBURelationOfValueInBB(I,BB,mapRel)->composition(RB);
        }
        else
          DEBUG(dbgs() << "WARN: use " << *I << " not in BB? " << '\n');
      }
      else{
        if(isa<Constant>(v))
          DEBUG(dbgs() << "INFO: use is a constant… " << '\n');
        else
          DEBUG(dbgs() << "INFO: use not an Instruction? " << '\n');
      }
      OP++;
    }
    return RB;
  }

  // Return Relation composed for the loop condition
  static Relation* getCondRelationsFromBB(BasicBlock* BB, MapRel* mapRel){
    DEBUG(dbgs() << "In getCondRelationsFromBB : " << '\n');
    TerminatorInst *TInst = BB->getTerminator();
    DEBUG(dbgs() << "TerminatorInst: " << *TInst << " … " << '\n');
    /* Relation *RB = new Relation(BB); */
    Relation *RB = new Relation();
    if(Instruction* Idif = dyn_cast<Instruction>(TInst->getOperand(0))){
      DEBUG(dbgs() << "First Inst: " << *Idif << " … " << '\n');
      RB = getBURelationOfValueInBB(Idif,BB,mapRel);
    } else{
      DEBUG(dbgs() << "ERROR: first value " << *TInst->getOperand(0) 
            << " … " << '\n');
    }
    DEBUG(dbgs() << " Final condition Relation: " << '\n');
    DEBUG(RB->dump(dbgs()));

    /* if(RB->getInstructions().empty()){ */
    /*   DEBUG(dbgs() << "WARN: Didn't find any conditions… " << '\n'); */
    /*   return nullptr; */
    /* } */
    /* else */
      return RB;
  }


  // Return Relation composed for the given BasicBlock
  static Relation* getPHIRelations(Loop* L, Chunk* chunk, std::vector<Value*> *OC,
                                   bool WantIn){
    MapDeg* mapDeg = chunk->getMapDeg();
    MapRel* mapRel = chunk->getMapRel();
    BasicBlock* BB = L->getHeader();
    DEBUG(dbgs() << "In getPHIRelations : " << '\n');
    Relation *RB = new Relation();
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
    /* if(RB->getInstructions().empty()) */
    /*   return nullptr; */
    /* else */
    return RB;
  }

  // Return the good relation from phi regarding to the BasicBlocks From and To
  static Relation* getPHIRelations(BasicBlock* From, BasicBlock* To, MapRel*
                                   mapRel){
    DEBUG(dbgs() << "In getPHIRelations : " << '\n');
    /* Relation *RB = new Relation(To); */
    Relation *RB = new Relation();
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
      else 
        DEBUG(dbgs() << "↑ not a Phi." << '\n');
    }//End of For II in BB
    /* if(RB->getInstructions().empty()) */
    /*   return nullptr; */
    /* else */
      return RB;
  }


  // Return the good relation from phi going from the body to the header
  static Relation* getPHIRelations(Loop* L, MapRel* mapRel, bool WantIn){
    BasicBlock* BB = L->getHeader();
    DEBUG(dbgs() << "In getPHIRelations : " << '\n');
    /* Relation *RB = new Relation(BB); */
    Relation *RB = new Relation();
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
    /* if(RB->getInstructions().empty()) */
    /*   return nullptr; */
    /* else */
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
    LegacyLQICMPass() : LoopPass(ID) {
      initializeLegacyLQICMPassPass(*PassRegistry::getPassRegistry());
    }

    bool runOnLoop(Loop *L, LPPassManager &LPM) override {
      NumLoops++;
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
                             /* &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(), */
                             &getAnalysis<DependenceAnalysisWrapperPass>().getDI(),
                             &getAnalysis<PostDominatorTreeWrapperPass>().getPostDomTree(),
                             SE ? &SE->getSE() : nullptr, false); }

      /// This transformation requires natural loop information & requires that
      /// loop preheaders be inserted into the CFG...
      ///
      void getAnalysisUsage(AnalysisUsage &AU) const override {
        /* AU.setPreservesCFG(); */
        /* AU.addRequired<TargetLibraryInfoWrapperPass>(); */
        AU.addRequired<DependenceAnalysisWrapperPass>();
        AU.addRequired<PostDominatorTreeWrapperPass>();
        getLoopAnalysisUsage(AU);
        /* AU.getPreservesAll(); */
      }

      using llvm::Pass::doFinalization;

      bool doFinalization() override {
        LQICM.getMapChunk().shrink_and_clear();
        assert(LQICM.getMapChunk().empty() &&
               "Didn't free loop chunks");
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

  /// Little predicate that returns true if the specified basic block is in
  /// a subloop of the current one, not the current one itself.
  ///
  static bool inSubLoop(BasicBlock *BB, Loop *CurLoop, LoopInfo *LI) {/*{-{*/
    assert(CurLoop->contains(BB) && "Only valid if BB is IN the loop");
    return LI->getLoopFor(BB) != CurLoop;
  }/*}-}*/

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


  // TODO
  BSet removeChunkWithHead(BasicBlock *Head, Loop *L, ValueToValueMapTy &VMap, LoopInfo *LI){
    BSet BBToRemove;
    BBToRemove.insert(Head);
  }

  // Remove chuncks with deg <= curDeg (except if < 0)/*{-{*/
  VSet updateLoopBody(Loop* L, unsigned curDeg, MapChunk* mapChunk,
                      ValueToValueMapTy &VMap, ScalarEvolution *SE,
                      DominatorTree *DT, PostDominatorTree *PDT, LoopInfo *LI,
                      std::vector<Value*> *OC){
    DEBUG(dbgs() <<"CurDeg = " << curDeg << " :\n");

    // If we are here, it works
    Value* head = dyn_cast<Value>(L->getHeader());

    Chunk* currentChunk = (*mapChunk)[head];
    MapDeg *mapDeg = currentChunk->getMapDeg();

    std::vector<Loop*> LoopToRemove;
    ISet toRemove;
    VSet toClean;
    BSet BBToRemove;

    //TODO it's faster to reuse the ordered chunks/commands which has a degree
    //computed
    /* for(Value* VI : *OC){ */
    /*   DEBUG(dbgs() << "Treating: " << VI << " … " ); */

    /*   // If it's not the degree we are looking for continue… */
    /*   if((*mapDeg)[VI] != curDeg){ */
    /*     continue; */
    /*   } */

    /*   if((*mapChunk)[I]){ */
    /*     DEBUG(dbgs() << "\n↑ It's the beginning of an inner Chunk with end: " */
    /*           << ((*mapChunk)[I])->getEnd()->getName()); */
    /*     DEBUG(dbgs() << "to remove… \n"); */
    /*     //TODO recursivly remove chunk */
    /*     // removeChunk(…)… */
    /*   } */

    /*   //If it's a simple instruction */
    /*   if(Instruction* I = dyn_cast<Instruction>(VI)){ */

    /*     //If it's a Terminator then it's the key of a fork if-then-else like */
    /*     if(isa<TerminatorInst>(&I)){ */
    /*       DEBUG(dbgs() <<"Start of a registered branch we need to hoist"<< */
    /*             " with deg = " << (*mapDeg)[VI] << "\n"); */
    /*       TerminatorInst *TInst = dyn_cast<TerminatorInst>(&I); */
    /*       // Put the branches to the garbage */
    /*       BasicBlock *Then = TInst->getSuccessor(0); */
    /*       BasicBlock *Else = TInst->getSuccessor(1); */
    /*       BBToRemove.insert(Then); */
    /*       BBToRemove.insert(Else); */
    /*       // Modify the TInst to go directly to the if.end… */
    /*       BasicBlock *IfEnd = PDT->findNearestCommonDominator(Then,Else); */
    /*       BranchInst* br = llvm::BranchInst::Create(IfEnd); */
    /*       ReplaceInstWithInst(TInst->getParent()->getInstList(),LII,br); */

    /*       // Now adjust the phi nodes in the ifEnd */
    /*       for (BasicBlock::iterator PII = IfEnd->begin(); isa<PHINode>(PII); */
    /*            ++PII) { */
    /*         Instruction &PI = *PII; */
    /*         toRemove.insert(&PI); */
    /*       } */

    /*       // Another cleaner thing is to merge IfEnd and BB */
    /*       /1* MergeBlockIntoPredecessor(IfEnd); //Does not work… why? *1/ */
    /*       // Don't care, other passes like simplifycfg will do it ;) */
    /*     } */
    /*     else{ */
    /*       // If it's just a basic Instruction just remove it */
    /*       toRemove.insert(&I); */
    /*       DEBUG(dbgs() << "to remove… \n"); */
    /*     } */
    /*     continue; */
    /*   } */
    /*   else{ */
    /*     DEBUG(dbgs() <<" WARN: A command in OC is not an Instruction nor a */
    /*           chunk… " << "\n"); */
    /*   } */
    /* } */

    // DEPRECATED ↓
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
        Value* innerHead = dyn_cast<Value>(BB);
        if((*mapChunk)[innerHead]){
          DEBUG(dbgs() << " BB " << innerHead << " is the innerHead of the innerloop " << 
                "with deg = " << (*mapDeg)[innerHead] << "\n");
          if((*mapDeg)[innerHead] == curDeg){
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
          // FIXME Not sure whe should to this here ↓
          NewInst = cast<Instruction>(VMap[&*v]);
          v->replaceAllUsesWith(NewInst); // With the last cloned value for I…
          // ↑
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
    DEBUG(dbgs() <<" Feeding VMap with Phis entries " << *Latch << "\n");
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
    DEBUG(dbgs() <<" Feeding VMap for the outgoing values " << *Latch << "\n");
    for (BasicBlock::iterator I = Exit->begin(); isa<PHINode>(I); ++I) {
      PHINode *PHI = cast<PHINode>(I);
      DEBUG(dbgs() <<" On PHI " << *PHI << "\n");
      // Here we made a correction… maybe the loop's form is not appropriate…
      DEBUG(dbgs() <<"WARN: Index of Latch = " << PHI->getBasicBlockIndex(Latch)
            << "\n");
      if(PHI->getBasicBlockIndex(Latch) != -1){
        Value *LatchVal = PHI->getIncomingValueForBlock(Latch);
        Instruction *LatchInst = dyn_cast<Instruction>(LatchVal);
        if (LatchInst && L->contains(LatchInst))
          LatchVal = VMap[LatchVal];
        PHI->addIncoming(LatchVal, cast<BasicBlock>(VMap[Latch]));
      }
    }
    DEBUG(dbgs() <<" ok !\n");

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
  /// optimizations./*{-{*/
  bool mypeelLoop(Loop *L, unsigned PeelCount, MapChunk*
                  mapChunk,std::vector<Value*> *OC, LoopInfo *LI,
                  ScalarEvolution *SE, DominatorTree *DT, PostDominatorTree
                  *PDT, bool PreserveLCSSA) {

    DEBUG(dbgs() <<"**************in mypeelLoop !****************\n");
    L->print(dbgs());
    DEBUG(dbgs() <<"Loop Before peeling ↑ \n");
    if (!canPeel(L))
      return false;

    // If we are here, it works
    Value* head = dyn_cast<Value>(L->getHeader());

    Chunk* currentChunk = (*mapChunk)[head];
    MapDeg *mapDeg = currentChunk->getMapDeg();

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
    Value* insertTop = dyn_cast<Value>(InsertTop);


    //TODO put relation of the entire loop to InsertTop in mapRelLoop
    //In that way it will not recompute the entire Relation of the inner peeled
    //loop but we also need to say which is the end block
    currentChunk->setStart(InsertTop);
    currentChunk->setPeeled(true);
    (*mapChunk)[insertTop] = currentChunk;

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
      toClean = mergeVSet(toClean, updateLoopBody(L, Iter+1, mapChunk, VMap, SE,
                                                  DT, PDT, LI, OC));

      LoopBlocks.clear();
      LoopBlocks.perform(LI);

      L->print(dbgs());
    }

    DEBUG(dbgs() <<"Cleaning Phi!…\n");
    for (auto VV = toClean.begin(), E = toClean.end(); VV != E; ++VV) {
      Value* V = *VV;
      if(Instruction* I = dyn_cast<Instruction>(V)){
        DEBUG(dbgs() <<"Removing " << *V <<"…\n");
        I->eraseFromParent();
        DEBUG(dbgs() <<"Removed!\n");
      }
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
      // FIXME If there is only one value, then just replace all use of the
      // value and remove this PHI!
    }

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
  }

}/*}-}*/

#endif

