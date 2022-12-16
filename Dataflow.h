/************************************************************************
 *
 * @file Dataflow.h
 *
 * General dataflow framework
 *
 ***********************************************************************/

#ifndef _DATAFLOW_H_
#define _DATAFLOW_H_

#include <llvm/Support/raw_ostream.h>
#include <map>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Function.h>

using namespace llvm;

class myBasicBlock;
class myFunc{
public:
    Function* mf;
    std::set<myBasicBlock*> mbSet;
    myBasicBlock* entry_block;
    myBasicBlock* exit_block;

    myFunc(Function* f): mf(f), mbSet(){}
    
    void addmyBasicBlock(myBasicBlock* mb){
        mbSet.insert(mb);
    } 
    
    void setEntryBlock(myBasicBlock* mb){
        entry_block = mb;
    }

    void setExitBlock(myBasicBlock* mb){
        exit_block = mb;
    }

    myBasicBlock* getEntryBlock(){
        return entry_block;
    }

    myBasicBlock* getExitBlock(){
        return exit_block;
    }

};

class myBasicBlock{
public:
    myFunc* parent; 
    BasicBlock* bb;
    BasicBlock::iterator begin_inst;
    BasicBlock::iterator end_inst;
    std::set<myBasicBlock*> mSuccs;
    std::set<myBasicBlock*> mPreds;
    bool isExitBlock = 0; 

    myBasicBlock(BasicBlock* initb, myFunc* mf): bb(initb),parent(mf), mSuccs(), mPreds(){} 

    void addSucc(myBasicBlock* succ){
        this->mSuccs.insert(succ);
        succ->mPreds.insert(this);
    }  
    
    void addPred(myBasicBlock* pred ){
        this->mPreds.insert(pred);
        pred->mSuccs.insert(this);
    }
    
    std::set<myBasicBlock*> getSuccs(){
        return mSuccs;
    }

    std::set<myBasicBlock*> getPreds(){
        return mPreds;
    }

    void setBeginInst(BasicBlock::iterator inst){
        begin_inst = inst;
    }

    void setEndInst(BasicBlock::iterator inst){
        end_inst = inst;
    }
    
    BasicBlock::iterator getBeginInst(){
        return begin_inst;
    }

    BasicBlock::iterator getEndInst(){
        return end_inst;
    }

    myBasicBlock* split(BasicBlock::iterator ii){
        myBasicBlock* newMbb = new myBasicBlock(bb,parent);
        parent->mbSet.insert(newMbb);

	for(myBasicBlock* suci:this->getSuccs()){
	    newMbb->addSucc(suci);
	}
        this->mSuccs.clear();
        this->addSucc(newMbb);

        newMbb->setBeginInst(ii);
        newMbb->setEndInst(end_inst);
        end_inst = ii;

        if(isExitBlock){
            isExitBlock = 0;
            newMbb->isExitBlock = 1;
            parent->setExitBlock(newMbb);
        }
        
        return newMbb;
    }
};


std::set<myBasicBlock*> worklist;
extern std::map<Function*, myFunc*> func2myfunc;

///Base dataflow visitor class, defines the dataflow function
template <class T>
class DataflowVisitor {
public:
    virtual ~DataflowVisitor() { }

    /// Dataflow Function invoked for each basic block 
    /// 
    /// @block the Basic Block
    /// @dfval the input dataflow value
    /// @isforward true to compute dfval forward, otherwise backward
    virtual void compDFVal(myBasicBlock *mblock, T *dfval, bool isforward) {
        BasicBlock* block = mblock->bb;
        if (isforward == true) {
           for (BasicBlock::iterator ii=mblock->getBeginInst(), ie=mblock->getEndInst(); 
                ii!=ie; ++ii) {
                Instruction * inst = &*ii;
                compDFVal(inst, dfval,mblock);
           }
        } else {
           for (BasicBlock::reverse_iterator ii=block->rbegin(), ie=block->rend();
                ii != ie; ++ii) {
                Instruction * inst = &*ii;
                compDFVal(inst, dfval,mblock);
           }
        }
    }
    
    ///
    /// Dataflow Function invoked for each instruction
    ///
    /// @inst the Instruction
    /// @dfval the input dataflow value
    /// @return true if dfval changed
    virtual void compDFVal(Instruction *inst, T *dfval, myBasicBlock* mbb) = 0;
    ///
    /// Merge of two dfvals, dest will be ther merged result
    /// @return true if dest changed
    ///
    virtual void merge( T *dest, const T &src ) = 0;
};

///
/// Dummy class to provide a typedef for the detailed result set
/// For each basicblock, we compute its input dataflow val and its output dataflow val
///
template<class T>
struct DataflowResult {
    typedef typename std::map<myBasicBlock *, std::pair<T, T> > Type;
};

/// 
/// Compute a forward iterated fixedpoint dataflow function, using a user-supplied
/// visitor function. Note that the caller must ensure that the function is
/// in fact a monotone function, as otherwise the fixedpoint may not terminate.
/// 
/// @param fn The function
/// @param visitor A function to compute dataflow vals
/// @param result The results of the dataflow 
/// @initval the Initial dataflow value
template<class T>
void compForwardDataflow(Function *fn,
    DataflowVisitor<T> *visitor,
    typename DataflowResult<T>::Type *result,
    const T & initval) {

    myFunc* mfn = func2myfunc[fn];     
    
    for(myBasicBlock* mbb: mfn->mbSet){
        result->insert(std::make_pair(mbb,std::make_pair(initval, initval)));
        worklist.insert(mbb);
    }

    while(!worklist.empty()) {
        myBasicBlock * mbb = *worklist.begin();
        worklist.erase(worklist.begin());

        if(result->find(mbb) == result->end()){
            result->insert(std::make_pair(mbb,std::make_pair(initval, initval)));
        }

        T bbentryval = (*result)[mbb].first;


        for(myBasicBlock* pred : mbb->getPreds()){
            visitor->merge(&bbentryval, (*result)[pred].second);
        }
        
        (*result)[mbb].first = bbentryval;
        visitor->compDFVal(mbb, &bbentryval, true);

        // If outgoing value changed, propagate it along the CFG
        if (bbentryval == (*result)[mbb].second) continue;
        (*result)[mbb].second = bbentryval;

        for (myBasicBlock* si : mbb->getSuccs()) {
            worklist.insert(si);
        }

    }

    return;
}
/// 
/// Compute a backward iterated fixedpoint dataflow function, using a user-supplied
/// visitor function. Note that the caller must ensure that the function is
/// in fact a monotone function, as otherwise the fixedpoint may not terminate.
/// 
/// @param fn The function
/// @param visitor A function to compute dataflow vals
/// @param result The results of the dataflow 
/// @initval The initial dataflow value
template<class T>
void compBackwardDataflow(Function *fn,
    DataflowVisitor<T> *visitor,
    typename DataflowResult<T>::Type *result,
    const T &initval) {
    return ;
}

template<class T>
void printDataflowResult(raw_ostream &out,
                         const typename DataflowResult<T>::Type &dfresult) {
    for ( typename DataflowResult<T>::Type::const_iterator it = dfresult.begin();
            it != dfresult.end(); ++it ) {
        if (it->first == NULL) out << "*";
        else it->first->dump();
        out << "\n\tin : "
            << it->second.first 
            << "\n\tout :  "
            << it->second.second
            << "\n";
    }
}







#endif /* !_DATAFLOW_H_ */
