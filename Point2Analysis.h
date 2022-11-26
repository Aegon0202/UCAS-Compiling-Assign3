
#include <llvm/IR/Function.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/IntrinsicInst.h>

#include "Dataflow.h"
using namespace llvm;


struct Point2SetInfo {
    std::map<Instruction*, std::set<Instruction *>> IntraPts;
    Point2SetInfo() : IntraPts() {}
    Point2SetInfo(const Point2SetInfo & info) : IntraPts(info.IntraPts) {}
    bool operator == (const Point2SetInfo & info){
        return IntraPts == info.IntraPts; 
    }
    
};

inline raw_ostream &operator<<(raw_ostream &out, const Point2SetInfo &info) {
    for (std::set<Instruction *>::iterator ii=info.LiveVars.begin(), ie=info.LiveVars.end();
         ii != ie; ++ ii) {
       const Instruction * inst = *ii;
       out << inst->getName();
       out << " ";
    }
    return out;
}

	
class Point2AnalysisVisitor : public DataflowVisitor<struct Point2SetInfo> {
public:
   Point2AnalysisVisitor() {}

   void merge(Point2SetInfo* dest, const Point2SetInfo & src) override{
   }

   void compDFVal(Instruction* inst, Point2SetInfo * dfval) override{
       if(isa<DbgInfoIntrinsic>(inst)) return;

   }
};


class PointAnalysis : public FunctionPass {
public:

   static char ID;
   PointAnalysis() : FunctionPass(ID) {} 

   bool runOnFunction(Function &F) override {

       return false;
   }
};



