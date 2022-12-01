
#include <llvm/IR/Function.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/IntrinsicInst.h>

#include "Dataflow.h"
using namespace llvm;


struct Point2SetInfo {
    std::map<Value*, std::set<Value *> *> IntraPts;
    std::set<Value* > registedValues;

    Point2SetInfo() : IntraPts() {}
    Point2SetInfo(const Point2SetInfo & info) : IntraPts(info.IntraPts) {}
    bool operator == (const Point2SetInfo & info){
        return IntraPts == info.IntraPts; 
    }
    
    void add_node(Value* v){
        registedValues.insert(v) ;
        IntraPts.insert({pre,new std::set<Value*>()});
    }

    void set_union(std::set<Value*>* dest,std::set<Value*>* src){
    
        dest->insert(src->begin(),src->end());
    } 

    void addPoint2Edge(Value* pre, Value* suc){
        assert(pre);

        if(IntraPts.find(pre) == IntraPts.end()){
            add_node(pre);

        IntraPts[pre]->insert(suc);         
    }
    
    void addPoint2Set(Value* pre,std::set<Value*>* sucs){
        if(IntraPts.find(pre)==IntraPts.end()){
            IntraPts.insert({pre, new std::set<Value*>()})
        }
        
        set_union(IntraPts[pre],sucs);
    } 

    void RemovePoint2Set(Value* pre){
        assert(pre && IntraPts.find(pre)!=IntraPts_end());
        IntraPts[pre]->clear();
    }

    std::set<Value*>* GetPoint2Set(Value* pre){
        return IntraPts[pre]; 
    }

    bool isPoint2SetEmpty(Value* pre){

        return !(IntraPts[pre] && IntraPts[pre]->empty());
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

    unsigned mcurrent_line;

    std::map<unsigned, std::set<Funciton*>> mOutput;

    void push2Output(){
        int size = mOutput.size();
        if(size&&mOutput[size-1].first==mcurrent_line){
            mOutput[size-1].second->insert(mcurrent_func->begin(),mcurrent_func->end());
            delete mcurrent_func;
        }
        else
        mOutput.push_back({mcurrent_line, mcurrent_func});
    }

    void showResult(){
        for(int i=0;i<mOutput.size();i++){
            unsigned line = mOutput[i].first;
            std::set<Function*> funcs = *(mOutput[i].second);
            errs()<<line<<":";
            int flag = 1; 
            for(Function* i :funcs){
                if(flag){
                    errs()<<i->getName();
                    flag = 0;
                }
                else
                    errs()<<","<<i->getName();
            }
            errs()<<"\n";
        }
    }
    
    void handleFunction(Function* func){
        
    } 

    void handleLoadInst(LoadInst* loadinst, Point2SetInfo * dfval){
        Value* address = loadinst->getPointerOperand();
        std::set<Value*>* s = dfval->getPoint2Set(address);
        Value* pre = dyn_cast<Value>(loadinst);
        dfval->removePoint2Set(pre);

        for(std::set<Value*>::iterator i=s->begin();i!=s->end();i++){
            std::set<Value*> sucs = dfval->getPoint2Set(i);
            dfval->addPoint2Set(pre, sucs); 
        }

    }
    
    void handleStoreInst(StoreInst* storeinst,Point2SetInfo* dfval){
        Value* y = storeinst->getValueOperand();
        Value* x = storeinst->getPointerOperand(); 

        dfval->removePoint2Set(x);
        dfval->addPoint2Edge(x,y);
    } 


    void handleCallInst(CallInst* callinst, Point2SetInfo* dfval){
         

        
        // contex-insensitive
        return ;
    }

    void merge(Point2SetInfo* dest, const Point2SetInfo & src) override{
        return ;
    }

    void compDFVal(Instruction* inst, Point2SetInfo * dfval) override{
        if(isa<DbgInfoIntrinsic>(inst)) return ;

        if(LoadInst* loadinst = dyn_cast<LoadInst>(inst)){
            handleLoadInst(loadinst,dfval);
        } 
        else if(StoreInst* storeinst = dyn_cast<StoreInst>(inst)){
            handleStoreInst(storeinst,dfval);
        }
        else if(CallInst* callinst = dyn_cast<CallInst>(callinst)){
            handleCallInst(callinst, dfval);
        }
        else{
            assert(0);
        }
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



