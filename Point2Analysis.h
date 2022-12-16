
#include <llvm/IR/Function.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/IntrinsicInst.h>

#include "Dataflow.h"
using namespace llvm;

std::map<BasicBlock*,std::set<BasicBlock*>* > callee2callerMap;
std::map<BasicBlock*,std::set<BasicBlock*>* > caller2calleeMap;
extern std::set<BasicBlock*> worklist;

struct Point2SetInfo {
    std::map<Value*, std::set<Value *> *> IntraPts;
    std::set<Value* > registedValues;
    std::map<Value*, std::set<Function*>*> call2Funcs;

    Point2SetInfo() : IntraPts() {}
    Point2SetInfo(const Point2SetInfo & info) : IntraPts(info.IntraPts) {}
    bool operator == (const Point2SetInfo & info){
        return IntraPts == info.IntraPts; 
    }
    
    void add_node(Value* v){
        registedValues.insert(v) ;
        IntraPts.insert({v,new std::set<Value*>()});
    }

    void set_union(std::set<Value*>* dest,std::set<Value*>* src){
    
        dest->insert(src->begin(),src->end());
    } 

    void addPoint2Edge(Value* pre, Value* suc){
        assert(pre);

        if(IntraPts.find(pre) == IntraPts.end())
            add_node(pre);

        IntraPts[pre]->insert(suc);         
    }
    
    void addPts(Value* pre,std::set<Value*>* sucs){
        if(IntraPts.find(pre)==IntraPts.end()){
            IntraPts.insert({pre, new std::set<Value*>()});
        }
        
        set_union(IntraPts[pre],sucs);
    } 
    

    void rmPts(Value* pre){
        assert(pre);
        if(IntraPts.find(pre)==IntraPts.end()){
            add_node(pre);
        }
        IntraPts[pre]->clear();
    }

    std::set<Value*>* getPts(Value* pre){
        return IntraPts[pre]; 
    }

    bool isPoint2SetEmpty(Value* pre){

        return !(IntraPts[pre] && IntraPts[pre]->empty());
    }
    
};

inline raw_ostream &operator<<(raw_ostream &out, const Point2SetInfo &pts) {
  for (const auto v : pts.IntraPts) {
    if (v.first->hasName()) {
      out << v.first->getName();
    } else {
      out << "%*"; 
    }
    out << ": {";

    const auto s = v.second;
    for (auto iter = s->begin(); iter != s->end(); iter++) {
      if (iter != s->begin()) {
        out << ", ";
      }
      out << (*iter)->getName();
    }
    out << "}\n";
  }
  return out;
}
	
class Point2AnalysisVisitor : public DataflowVisitor<struct Point2SetInfo> {
public:
    Point2AnalysisVisitor() {}

    std::map<unsigned, std::set<std::string>*> mOutput;

    void showResult(){
        for(std::map<unsigned, std::set<std::string>*>::iterator i=mOutput.begin(), j=mOutput.end(); i!=j; i++){
            unsigned line =i->first;
            std::set<std::string> funcs = *(i->second);
            errs()<<line<<":";
            int flag = 1; 
            for(std::string ii:funcs){
                if(flag){
                    errs()<<ii;
                    flag = 0;
                }
                else
                    errs()<<","<<ii;
            }
            errs()<<"\n";
        }
    }
    
    void handleAllocaInst(AllocaInst* allocainst, Point2SetInfo* dfval){
        return ;   
    }

    void handleLoadInst(LoadInst* loadinst, Point2SetInfo * dfval){
        /*
        Value* address = loadinst->getPointerOperand();
        std::set<Value*>* s = dfval->getPoint2Set(address);
        Value* pre = dyn_cast<Value>(loadinst);
        dfval->removePoint2Set(pre);

        for(std::set<Value*>::iterator i=s->begin();i!=s->end();i++){
            std::set<Value*> sucs = dfval->getPoint2Set(i);
            dfval->addPts(pre, sucs); 
        }
        */
        Value* suc = loadinst->getPointerOperand();
        Value* pre = dyn_cast<Value>(loadinst);
        dfval->rmPts(pre);
        dfval->addPts(pre, dfval->getPts(suc));
    }
    
    void handleStoreInst(StoreInst* storeinst,Point2SetInfo* dfval){
        Value* y = storeinst->getValueOperand();
        Value* x = storeinst->getPointerOperand(); 

        dfval->rmPts(x);
        dfval->addPoint2Edge(x,y);
    } 

    void init_new_func(Function* fn,BasicBlock* callerBB){
                
        BasicBlock* entry = &(fn->getEntryBlock());
        BasicBlock* exit = &(fn->back());
        
        if(caller2calleeMap.find(callerBB)==caller2calleeMap.end()) {
            caller2calleeMap.insert({callerBB, new std::set<BasicBlock*>()});
        }
        if(callee2callerMap.find(exit)==callee2callerMap.end()){
            callee2callerMap.insert({exit, new std::set<BasicBlock*>()});
        }

        caller2calleeMap[callerBB]->insert(entry);
        callee2callerMap[exit]->insert(callerBB->getUniqueSuccessor()->getUniqueSuccessor());
        
        //add all blocks of fn to worklist
        for(Function::iterator bi = fn->begin();bi!=fn->end();++bi){
            BasicBlock * bb = &*bi;
            worklist.insert(bb);
        }
    } 

    void handleCallInst(CallInst* callinst, Point2SetInfo* dfval){
        Value* callop = callinst->getCalledOperand(); 
        unsigned line = callinst->getDebugLoc().getLine(); 
        unsigned argnum = callinst->getNumArgOperands();     

        if(mOutput.find(line)==mOutput.end()){
            mOutput.insert({line, new std::set<std::string>()});
        }
        std::set<std::string>* names = mOutput[line];

        if(callop->getName() == "malloc"){
            names->insert("malloc");            
            return;
        }
        
        std::set<Value*>* callfuncs = dfval->getPts(callop); 
    
        for(Value* func: *callfuncs){
            Function* f = dyn_cast<Function>(func);

            //new function
            if(names->find(f->getName())==names->end()){
                //add to print result 
                names->insert(f->getName());
                init_new_func(f,callinst->getParent()); 
            }

            for(unsigned i=0;i<argnum;i++){
                Value* argi = callinst->getArgOperand(i);
                if(argi->getType()->isPointerTy()){
                    Value* fargi = f->getArg(i);
                    dfval->addPts(fargi,dfval->getPts(argi));
                }
            }
            
        } 

        return ;
    }

    void merge(Point2SetInfo* dest, const Point2SetInfo & src) override{
        const auto &srcPts = src.IntraPts;

        for(const auto &pts:srcPts){
            Value* pre = pts.first;
            std::set<Value*>* sucs = pts.second;

            dest->addPts(pre,sucs);
        }
    }

    void compDFVal(Instruction* inst, Point2SetInfo * dfval) override{
        if(isa<DbgInfoIntrinsic>(inst)) return ;
        
        if(LoadInst* loadinst = dyn_cast<LoadInst>(inst)){
            handleLoadInst(loadinst,dfval);
        } 
        else if(StoreInst* storeinst = dyn_cast<StoreInst>(inst)){
            handleStoreInst(storeinst,dfval);
        }
        else if(CallInst* callinst = dyn_cast<CallInst>(inst)){
            handleCallInst(callinst, dfval);
        }
        else{
            return ;
        }
    }
};


class PointAnalysis : public ModulePass {
public:

    static char ID;
    PointAnalysis() : ModulePass(ID) {} 
    
    void preProcess(Module &M) {
        for(Function &fn:M){
            for(Function::iterator bi = fn.begin(); bi!=fn.end(); ++bi){
                BasicBlock* block = &*bi;
                for (BasicBlock::iterator ii=block->begin(), ie=block->end(); ii!=ie; ++ii){
                    Instruction* inst = &*ii;
                    if(isa<DbgInfoIntrinsic>(inst)) continue; 
                    if(CallInst* callinst = dyn_cast<CallInst>(inst)){
                         if(callinst->getCalledOperand()->getName()!="malloc"){
                            BasicBlock* newbb = block->splitBasicBlock(inst,"");
                            assert(block->getUniqueSuccessor());
                         } 
                    }
                }
                        
            }
                
        }
    }

    bool runOnModule(Module &M) override {

        // TODO:preProcessCallInst();
        // after this every call instruction(except intrinsic call or malloc call) will be the last 
        // instruction of the basicblock it belong to. The previous block will be divided into 2 blocks
        // the first one is end with the call inst, and the second on begin with the next inst of the 
        // call inst in previous block. A empty block will be created, and its succ is the second block, its
        // pred is the first block.
        preProcess(M); 

        DataflowResult<Point2SetInfo>::Type result;
        Point2AnalysisVisitor visitor;
        Point2SetInfo initval;
        auto f = M.rbegin(), e = M.rend();
        for(;(f->isIntrinsic()|| f->size()==0)&&f!=e;f++){
        }
        
        compForwardDataflow(&*f, &visitor, &result, initval);
        visitor.showResult();
        return false;
    }
};



