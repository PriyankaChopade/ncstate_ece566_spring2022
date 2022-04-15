#include <fstream>
#include <memory>
#include <algorithm>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <iostream>

#include "llvm-c/Core.h"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Analysis/InstructionSimplify.h"

using namespace llvm;

bool dce;
bool simplified;
bool inc_flag;

static void CommonSubexpressionElimination(Module *);
static void sameBBScan(BasicBlock::iterator);
static void domBBScan(BasicBlock::iterator);
static bool isValidForCSE(Instruction &);
static void eliminateLoad(BasicBlock::iterator);
static void eliminateStore(BasicBlock::iterator &);

static void summarize(Module *M);
static void print_csv_file(std::string outputfile);

static cl::opt<std::string>
        InputFilename(cl::Positional, cl::desc("<input bitcode>"), cl::Required, cl::init("-"));

static cl::opt<std::string>
        OutputFilename(cl::Positional, cl::desc("<output bitcode>"), cl::Required, cl::init("out.bc"));

static cl::opt<bool>
        Mem2Reg("mem2reg",
                cl::desc("Perform memory to register promotion before CSE."),
                cl::init(false));

static cl::opt<bool>
        NoCSE("no-cse",
              cl::desc("Do not perform CSE Optimization."),
              cl::init(false));

static cl::opt<bool>
        Verbose("verbose",
                    cl::desc("Verbose stats."),
                    cl::init(false));

static cl::opt<bool>
        NoCheck("no",
                cl::desc("Do not check for valid IR."),
                cl::init(false));

static llvm::Statistic CSEDead = {"", "CSEDead", "CSE found dead instructions"};
static llvm::Statistic CSEElim = {"", "CSEElim", "CSE redundant instructions"};
static llvm::Statistic CSESimplify = {"", "CSESimplify", "CSE simplified instructions"};
static llvm::Statistic CSELdElim = {"", "CSELdElim", "CSE redundant loads"};
static llvm::Statistic CSEStore2Load = {"", "CSEStore2Load", "CSE forwarded store to load"};
static llvm::Statistic CSEStElim = {"", "CSEStElim", "CSE redundant stores"};

int main(int argc, char **argv) {
    // Parse command line arguments
    cl::ParseCommandLineOptions(argc, argv, "llvm system compiler\n");

    // Handle creating output files and shutting down properly
    llvm_shutdown_obj Y;  // Call llvm_shutdown() on exit.
    LLVMContext Context;

    // LLVM idiom for constructing output file.
    std::unique_ptr<ToolOutputFile> Out;
    std::string ErrorInfo;
    std::error_code EC;
    Out.reset(new ToolOutputFile(OutputFilename.c_str(), EC,
                                 sys::fs::OF_None));

    EnableStatistics();

    // Read in module
    SMDiagnostic Err;
    std::unique_ptr<Module> M;
    M = parseIRFile(InputFilename, Err, Context);

    // If errors, fail
    if (M.get() == 0)
    {
        Err.print(argv[0], errs());
        return 1;
    }

    // If requested, do some early optimizations
    if (Mem2Reg)
    {
        legacy::PassManager Passes;
        Passes.add(createPromoteMemoryToRegisterPass());
        Passes.run(*M.get());
    }

    if (!NoCSE) {
        CommonSubexpressionElimination(M.get());
    }

    // Collect statistics on Module
    summarize(M.get());
    print_csv_file(OutputFilename);

    if (Verbose)
        PrintStatistics(errs());

    // Verify integrity of Module, do this by default
    if (!NoCheck)
    {
        legacy::PassManager Passes;
        Passes.add(createVerifierPass());
        Passes.run(*M.get());
    }

    // Write final bitcode
    WriteBitcodeToFile(*M.get(), Out->os());
    Out->keep();

    return 0;
}

static llvm::Statistic nFunctions = {"", "Functions", "number of functions"};
static llvm::Statistic nInstructions = {"", "Instructions", "number of instructions"};
static llvm::Statistic nLoads = {"", "Loads", "number of loads"};
static llvm::Statistic nStores = {"", "Stores", "number of stores"};

static void summarize(Module *M) {
    for (auto i = M->begin(); i != M->end(); i++) {
        if (i->begin() != i->end()) {
            nFunctions++;
        }

        for (auto j = i->begin(); j != i->end(); j++) {
            for (auto k = j->begin(); k != j->end(); k++) {
                Instruction &I = *k;
                nInstructions++;
                if (isa<LoadInst>(&I)) {
                    nLoads++;
                } else if (isa<StoreInst>(&I)) {
                    nStores++;
                }
            }
        }
    }
}

static void print_csv_file(std::string outputfile)
{
    std::ofstream stats(outputfile + ".stats");
    auto a = GetStatistics();
    
    for (auto p : a) {
        stats << p.first.str() << "," << p.second << std::endl;
    }
    stats.close();
}



bool isDead(Instruction &I)
{
    /*
        Check necessary requirements, otherwise return false
     */
    if ( I.use_begin() == I.use_end() )
    {
        int opcode = I.getOpcode();
        switch(opcode){
            case Instruction::Add:
            case Instruction::FNeg:
            case Instruction::FAdd:
            case Instruction::Sub:
            case Instruction::FSub:
            case Instruction::Mul:
            case Instruction::FMul:
            case Instruction::UDiv:
            case Instruction::SDiv:
            case Instruction::FDiv:
            case Instruction::URem:
            case Instruction::SRem:
            case Instruction::FRem:
            case Instruction::Shl:
            case Instruction::LShr:
            case Instruction::AShr:
            case Instruction::And:
            case Instruction::Or:
            case Instruction::Xor:
            //case Instruction::Alloca:
            case Instruction::GetElementPtr:
            case Instruction::Trunc:
            case Instruction::ZExt:
            case Instruction::SExt:
            case Instruction::FPToUI:
            case Instruction::FPToSI:
            case Instruction::UIToFP:
            case Instruction::SIToFP:
            case Instruction::FPTrunc:
            case Instruction::FPExt:
            case Instruction::PtrToInt:
            case Instruction::IntToPtr:
            case Instruction::BitCast:
            case Instruction::AddrSpaceCast:
            case Instruction::ICmp:
            case Instruction::FCmp:
            case Instruction::PHI:
            case Instruction::Select:
            case Instruction::ExtractElement:
            case Instruction::InsertElement:
            case Instruction::ShuffleVector:
            case Instruction::ExtractValue:
            case Instruction::InsertValue:
                return true; // dead, but this is not enough

            // case Instruction::Load:
            // {
            //     LoadInst *li = dyn_cast<LoadInst>(&I);
            //     if (li && li->isVolatile())
            //         return false;
            //     return true;
            // }
            default:
                // any other opcode fails
                return false;
        }
    }

    return false;
}

static void CommonSubexpressionElimination(Module *M) {
    // Implement this function
    for(auto f = M->begin(); f!=M->end(); f++)
    {
        // loop over functions
        for(auto bb= f->begin(); bb!=f->end(); bb++)
        {
            // loop over basic blocks
            for(auto i = bb->begin(); i != bb->end(); )
            {

                Instruction *ExtractedI = &*i; // extract a pointer to an instr using the iterator i(deref it anf then take its address)
                if( isDead(*ExtractedI) ) 
                {
                    i++;
                    //ExtractedI->print(errs(), true);
                    ExtractedI->eraseFromParent();
                    CSEDead++;
                    continue;
                }      

                auto simplyInstr = SimplifyInstruction(ExtractedI, M->getDataLayout());
                if(simplyInstr)
                {
                    i++;
                    //ExtractedI->print(errs(), true);
                    ExtractedI->replaceAllUsesWith(simplyInstr);
                    ExtractedI->eraseFromParent();
                    CSESimplify++;
                    continue;
                    
                }

                if(isValidForCSE(*ExtractedI))
                {
                    sameBBScan(i);
                    
                    domBBScan(i);
                }

                if(ExtractedI->getOpcode() == Instruction::Load){
                    eliminateLoad(i);
                }

                if(ExtractedI->getOpcode() == Instruction::Store){
                    eliminateStore(i);
                    if(inc_flag) continue;
                }

                i++;
            }
        }
    }
}

//***********************Fucntion isValidForCSE**************************//
// checks for  Loads, Stores, Terminators, VAArg, Calls, Allocas, and FCmps
// if the instr is of any of the above types it returns false
// else returns true
// similar to isDead function above
//***********************************************************************//

static bool isValidForCSE(Instruction &I)
{
    int opcode = I.getOpcode();
    bool terminator = I.isTerminator();
    if(opcode == Instruction::Load || opcode == Instruction::Store ||
       opcode == Instruction::FCmp || opcode == Instruction::Alloca ||
       opcode == Instruction::VAArg || opcode == Instruction::Call ||
       terminator)
       {
           return false;
       }
       return true;
}

//**********************Function sameBBScan**************************************//
// scans for identical instr in the same basic block
// get the iteartor of the current instr
// make a copy of it and increment it and start the for loop till the end of the basic bloc
// if the current instr is identical to next iterator intr then increment the counter,
// erase the instr
// increment the CSElim counter
//*******************************************************************************//

static void sameBBScan(BasicBlock::iterator it)
{
    Instruction *currentI = &*it;
    BasicBlock *bb = currentI->getParent();
    it++;
    for(auto i = it; i!= bb->end();)
    {
        Instruction *nextI = &*i;
        i++;
        if(nextI->isIdenticalTo(currentI))
        {
            

            //nextI->print(errs(),true);
            nextI->replaceAllUsesWith(currentI);
            nextI->eraseFromParent();
            CSEElim++;
        }
    }
    return;
}
//***************************Function domBBScan*************************************//
//scans the child basic blocks for identical instr
// get the instr pointer
// find its parent
// find its block
// find the blocks it dominates
//**********************************************************************************//

static void domBBScan(BasicBlock::iterator iter)
{
    Instruction *I = &*iter;
    BasicBlock *BB = I->getParent();
    Function *F = I->getFunction();

    DominatorTreeBase<BasicBlock, false> *DT = nullptr;
    DT = new DominatorTreeBase<BasicBlock, false>();
    DT->recalculate(*F);                                 // F is Function. Use one DominatorTreeBase and
                                                        // recalculate tree for each function you visit
    DomTreeNodeBase<BasicBlock> *Node = DT->getNode(BB); // get Node from some basic block
    DomTreeNodeBase<BasicBlock>::iterator it, end;

    for (it = Node->begin(), end = Node->end(); it != end; it++) 
    {
        BasicBlock *bb_next = (*it)->getBlock(); // get each bb it immediately dominates
        for(auto p = bb_next->begin(); p!=bb_next->end();)
        {
            Instruction *nextI = &*p;
            p++;
            if(nextI->isIdenticalTo(I))
            {
                //nextI->print(errs(),true);
                nextI->replaceAllUsesWith(I);
                nextI->eraseFromParent();
                CSEElim++;
            }            
        }                 
    }
    return;
}

//**************************function eliminateLoad*****************************************//
// takes the copy of iterator(pass by value) after basic cse pass
// extracts instr from it and increment it
// get the basic block to which the instruction belongs
// iterate over the same basic block and one by one check if the instr is load, volatile, same addr, same type
// if yes eliminate the later load
// also check if there is any store to any addr, if yes then break
// ***************************************************************************************//

static void eliminateLoad(BasicBlock::iterator loadIt)
{
    Instruction *currentLoad = &*loadIt;
    BasicBlock *bb = currentLoad->getParent();
    loadIt++;
    for(auto k = loadIt; k!= bb->end();)
    {
        Instruction *nextInst = &*k;
        k++;
        if(nextInst->getOpcode() == Instruction::Load)
        {
            LoadInst *li = dyn_cast<LoadInst>(nextInst);
            if(!(li->isVolatile()))
            {
                if((nextInst->getOperand(0) == currentLoad->getOperand(0)) && (nextInst->getType() == currentLoad->getType()))
                {
                    nextInst->replaceAllUsesWith(currentLoad);
                    nextInst->eraseFromParent();
                    CSELdElim++;
                }
                
            }
            
        }

        if(nextInst->getOpcode() == Instruction::Store)
        {
            break;
        }
    } 
    return;
}
//**************************function eliminateStore*****************************************//
// takes the iterator(pass by reference) after basic cse pass
// make a copy of this iterator
// extracts instr from the copy and increment it
// get the basic block to which the instruction belongs
// iterate over the same basic block 
// firstly, check if the instr is load, volatile, same addr, same type .. 
// .. as the store value operand
// if yes eliminate the load
// Secondly, check if its a store with same address, same type, the current store is non volatile..
// .. if yes increment the passed iterator and then delete the current store
// also check if there is any store, load or call or any instruction with side effects to any addr, if yes then break
// ***************************************************************************************//
static void eliminateStore(BasicBlock::iterator &it)
{
    inc_flag = false;
    auto storeIt = it;
    Instruction *currentStore = &*storeIt;
    auto castedStore = dyn_cast<StoreInst>(currentStore);
    BasicBlock *bb = currentStore->getParent();
    storeIt++;
    for(auto m = storeIt; m!= bb->end();)
    {
        Instruction *nextInstruction = &*m;
        
        if(nextInstruction->getOpcode() == Instruction::Load)
        {
            LoadInst *li = dyn_cast<LoadInst>(nextInstruction);
            if(!(li->isVolatile()))
            {
                if((nextInstruction->getOperand(0) == currentStore->getOperand(1)) && (nextInstruction->getType() == (currentStore->getOperand(0))->getType()))
                {
                    m++;
                    nextInstruction->replaceAllUsesWith(castedStore->getValueOperand());
                    nextInstruction->eraseFromParent();
                    CSEStore2Load++;
                    continue;
                }
                
            }
            
        }

        if((nextInstruction->getOpcode() == Instruction::Store) && (nextInstruction->getOperand(1) == currentStore->getOperand(1)))
        {
            StoreInst *Si = dyn_cast<StoreInst>(currentStore);
            if(!(Si->isVolatile())){
                if((nextInstruction->getOperand(0)->getType()) == (currentStore->getOperand(0)->getType()))
                {
                    m++;
                    it++;
                    inc_flag = true;
                    currentStore->eraseFromParent();
                    CSEStElim++;
                    break;
                }
            }
        }

        if((nextInstruction->getOpcode() == Instruction::Load)  || 
           (nextInstruction->getOpcode() == Instruction::Store) || 
           (nextInstruction->getOpcode() == Instruction::Call)  ||
           (nextInstruction->mayHaveSideEffects()))
                 {
                    break;
                 }
        m++;
    }
    return;
}