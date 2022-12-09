
#include <llvm/IR/Function.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/IntrinsicInst.h>

#include "Dataflow.h"
using namespace llvm;


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

    std::set<Value*>* getPoint2Set(Value* pre){
        return IntraPts[pre]; 
    }

    bool isPoint2SetEmpty(Value* pre){

        return !(IntraPts[pre] && IntraPts[pre]->empty());
    }
    
};

inline raw_ostream &operator<<(raw_ostream &out, const Point2SetInfo &info) {
    for (std::map<Value*,std::set<Value*> >::iterator ii=info.IntraPts.begin(), ie=info.IntraPts.end();
         ii != ie; ++ ii) {
        out << " ";
    }
    return out;
}

	
class Point2AnalysisVisitor : public DataflowVisitor<struct Point2SetInfo> {
public:
    Point2AnalysisVisitor() {}

    std::map<unsigned, std::set<std::string>*> mOutput;

    void showResult(){
        for(int i=0;i<mOutput.size();i++){
            unsigned line = mOutput[i].first;
            std::set<std::string> funcs = *(mOutput[i].second);
            errs()<<line<<":";
            int flag = 1; 
            for(std::string i:funcs){
                if(flag){
                    errs()<<i;
                    flag = 0;
                }
                else
                    errs()<<","<<i->getName();
            }
            errs()<<"\n";
        }
    }
    
    void handleFunction(Function* func){
        return ; 
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
            dfval->addPoint2Set(pre, sucs); 
        }
        */
        Value* suc = loadinst->getPointerOperand();
        Value* pre = dyn_cast<Value>(loadinst);
        dfval->remvoePoint2Set(pre);
        dfval->addPoint2Set(pre, dfval->getPoint2Set(suc));
    }
    
    void handleStoreInst(StoreInst* storeinst,Point2SetInfo* dfval){
        Value* y = storeinst->getValueOperand();
        Value* x = storeinst->getPointerOperand(); 

        dfval->removePoint2Set(x);
        dfval->addPoint2Edge(x,y);
    } 


    void handleCallInst(CallInst* callinst, Point2SetInfo* dfval){
        Value* callop = callinst->getCalledOperand(); 
        unsigned line = callinst->getDebugLoc().getLine(); 
        unsigned argnum = callinst->getNumArgOperands();     

        if(mOutput.find(line)==mOutput.end()){
            mOutput.insert(line, new std::set<std::string>());
        }
        std::set<std::string>* names = mOutput.find(line);

        if(callop->getName() == "malloc"){
            names->insert("malloc");            
            return;
        }
        
        std::set<Value*>* callfuncs = dfval->getPoint2Set(callop); 
    
        for(Value* func: *callvals){
            Function* f = dyn_cast<Function> func;
            names->insert(f->getName());
             

            for(unsigned i=0;i<argnum;i++){
                Value* argi = callinst->getArgOperand(i);
                if(argi->getType()->isPointerTy()){
                    Value* fargi = f->getArg(i);
                    dfval->addPoint2Set(fargi,dfval->getPoint2Set(argi));
                }
            }
            
        } 
        


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


class PointAnalysis : public ModulePass {
public:

    static char ID;
    PointAnalysis() : ModulePass(ID) {} 

    bool runOnModule(Module &M) override {
        DataflowResult<Point2SetInfo>::Type result;
        Point2AnalysisVisitor visitor;

        for(Function& f:M){

            Point2SetInfo initval;
            compForwardDataflow(&f, &visitor, &result, initval);
        }
        
        visitor.showResult();
        return false;
    }
};



