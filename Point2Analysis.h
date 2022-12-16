
#include <llvm/IR/Function.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/IntrinsicInst.h>

#include "Dataflow.h"
using namespace llvm;

std::map<Function*, myFunc*> func2myfunc;
extern std::set<myBasicBlock* > worklist;

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

    void init_new_func(Function* fn, CallInst* callinst, myBasicBlock* curBB){
        myFunc* mfn = func2myfunc[fn] ;
        myBasicBlock* entry = mfn->getEntryBlock();
        myBasicBlock* exit = mfn->getExitBlock();
        
        myBasicBlock* nexit;
        auto splitline = callinst->getIterator(); 
        ++splitline;
        for(myBasicBlock* succ:curBB->getSuccs()){
            if(succ->getBeginInst()==splitline){ 
                nexit = succ; 
                break;
            }
        }

        assert(nexit->getBeginInst()==splitline) ;

        curBB->addSucc(entry);
        exit->addSucc(nexit); 
        
        for(myBasicBlock* mbb : mfn->mbSet){
            worklist.insert(mbb);
        } 
    } 

    void handleCallInst(CallInst* callinst, Point2SetInfo* dfval, myBasicBlock* curBB){
        
        Function* fff = callinst->getFunction();
        if(fff->getName()!="moo") return ;

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
                init_new_func(f,callinst,curBB); 
            }

            //compute dataflow infomation of func

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

    void compDFVal(Instruction* inst, Point2SetInfo * dfval, myBasicBlock* mbb) override{
        if(isa<DbgInfoIntrinsic>(inst)) return ;
        
        if(LoadInst* loadinst = dyn_cast<LoadInst>(inst)){
            handleLoadInst(loadinst,dfval);
        } 
        else if(StoreInst* storeinst = dyn_cast<StoreInst>(inst)){
            handleStoreInst(storeinst,dfval);
        }
        else if(CallInst* callinst = dyn_cast<CallInst>(inst)){
            handleCallInst(callinst, dfval, mbb);
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
    
    
    BasicBlock::iterator getFirstInst(BasicBlock* bb){
        return bb->begin();
    } 

    BasicBlock::iterator getLastInst(BasicBlock* bb){
        return bb->end();
    }

    void preProcess(Module &M) {
        for(Function &fn:M){
            if(fn.isIntrinsic()) continue;
            myFunc* mf = new myFunc(&fn);
            func2myfunc.insert({&fn,mf});

            BasicBlock* begin_block =  &(fn.getEntryBlock());
            myBasicBlock* begin_mbb = new myBasicBlock(begin_block,mf);
            begin_mbb->setBeginInst(getFirstInst(begin_block));
            begin_mbb->setEndInst(getLastInst(begin_block));
            
            mf->addmyBasicBlock(begin_mbb);
            mf->setEntryBlock(begin_mbb); 
            
            std::map<BasicBlock*,myBasicBlock*> createdList;
            std::set<BasicBlock*> blist;
            createdList.insert({begin_block,begin_mbb});
            blist.insert(begin_block); 
             

            while(!blist.empty()){
                BasicBlock* block = *blist.begin();
                blist.erase(blist.begin());
                myBasicBlock* pre_mbb = createdList[block];

                for(auto si = succ_begin(block), se = succ_end(block); si!=se; si++){
                    BasicBlock* succb = *si;
                    myBasicBlock* succ_mbb;  

                    if(createdList.find(succb)==createdList.end()){
                        succ_mbb = new myBasicBlock(succb,mf);
                        succ_mbb->setBeginInst(getFirstInst(succb));
                        succ_mbb->setEndInst(getLastInst(succb));
                        
                        mf->addmyBasicBlock(succ_mbb);
                        createdList.insert({succb,succ_mbb});
                        blist.insert(succb);                         
                    }
                    else{
                        succ_mbb = createdList[succb];
                    }
                    
                    pre_mbb->addSucc(succ_mbb); 
                    
                }                
            }

            mf->setExitBlock(createdList[&(fn.back())]);
            mf->getExitBlock()->isExitBlock = 1;
            for(Function::iterator bi = fn.begin(), be = fn.end();bi != be; bi++){
                BasicBlock* bb = &*bi;
                
                for (BasicBlock::iterator ii=bb->begin(), ie=bb->end(); ii!=ie; ++ii){
                    Instruction* inst = &*ii;
                    if(isa<DbgInfoIntrinsic>(inst)) continue; 
                    if(CallInst* callinst = dyn_cast<CallInst>(inst)){
                        if(callinst->getCalledOperand()->getName()!="malloc"){
                            myBasicBlock* mbb = createdList[bb];
                            auto tmpi = ii;
                            tmpi++;
                            createdList[bb] =  mbb->split(tmpi);
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



