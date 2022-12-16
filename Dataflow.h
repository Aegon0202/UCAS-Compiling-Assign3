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
                compDFVal(inst, dfval);
           }
        } else {
           for (BasicBlock::reverse_iterator ii=block->rbegin(), ie=block->rend();
                ii != ie; ++ii) {
                Instruction * inst = &*ii;
                compDFVal(inst, dfval);
           }
        }
    }
    
    virtual void compDFVal(BasicBlock *block, T *dfval, typename DataflowResult<T>::Type *result, bool isforward){

        if (isforward == true) {
           for (BasicBlock::iterator ii=block->begin(), ie=block->end(); 
                ii!=ie; ++ii) {
                Instruction * inst = &*ii;
                compDFVal(inst, dfval,result);
           }
        } else {
           for (BasicBlock::reverse_iterator ii=block->rbegin(), ie=block->rend();
                ii != ie; ++ii) {
                Instruction * inst = &*ii;
                compDFVal(inst, dfval,result);
           }
        }
    }
    ///
    /// Dataflow Function invoked for each instruction
    ///
    /// @inst the Instruction
    /// @dfval the input dataflow value
    /// @return true if dfval changed
    virtual void compDFVal(Instruction *inst, T *dfval ) = 0;

    virtual void compDFVal(Instruction *inst, T *dfval, typename DataflowResult<T>::Type *result) = 0;
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
        mBasicBlock * mbb = *worklist.begin();
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
