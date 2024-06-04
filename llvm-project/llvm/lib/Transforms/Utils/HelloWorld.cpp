//===-- HelloWorld.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/HelloWorld.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Attributes.h"

#define PASS_MODE 1
/*
1 == disable whole pass
2 == stack/alloca usage analysis
3 == only tagging ptrs
0 == naive ptr+mem tagging
*/

#define MTE_GRANULE 16
#define MT_TAG_SHIFT 56
#define TAGGY 7

#define __INLINE_MTE_CALL 1
//  asm volatile ( \
        "mov x2, %0\n" \
        "mov x3, %1\n" \
        "mov x17, %0\n" \
        "cbz %1, 2f\n" \
   "1:\n" \
        "mov x16, %0\n" \
        "lsr x16, x16, #56\n" \
        "and x16, x16, #0xFUL\n" \
        "strb w16, [x17, #0x0]\n" \
        "add %0, %0, #16\n" \
        "sub %1, %1, #16\n" \
        "add x17, x17, 1\n" \
        "cbnz    %1, 1b\n" \
   "2:\n" \
       "mov %0, x2\n" \
       "mov %1, x3\n" \
    ::"r"(ptr), "r"(size):"x16","x17","x2","x3","memory")

using namespace llvm;

FunctionCallee mte_set_tag_address_range;

#if PASS_MODE == 2
FunctionCallee output_alloca_size;
#endif

namespace {
/// Represents an Alloca with redzone instrumentation afterwards.
class InstrumentedAlloca {
    Function *F = nullptr;
    /// The instrumented alloca that has space for the redzone.
    AllocaInst *Alloca = nullptr;
    // The new aligned size of the alloca
    Value *newSize = nullptr;
    // Store the tagged pointer upon tagging
    Value *storedTaggedPtr = nullptr;
    /// Instructions where untag instrumentation was added before.
    std::vector<Instruction *> untagPoints;
public:
    bool taggedByStart = false;
    InstrumentedAlloca(Function &F, AllocaInst *A, Value* S) : F(&F), Alloca(A), newSize(S) {
        assert(A);
    }

    AllocaInst* getAlloca(){
        return Alloca;
    }

    /// Return true if the given Value is the respective alloca.
    [[nodiscard]]
    bool isAlloca(Value *A) const {
        return Alloca == A->stripPointerCastsAndAliases();
    }

    void applyTag(Instruction *When){
        // We can only touch the alloca when it dominates our use. Otherwise this violates SSA.
        DominatorTree DT(*F);
        if (!DT.dominates(Alloca, When))
            return;

        assert(When);
        LLVMContext &C = F->getContext();

        IRBuilder<> builder(When);

        // set the tag in pointer: ptr | (tag << shift)
        builder.SetInsertPoint(Alloca->getNextNode());
        Value* tag = builder.CreateShl(builder.getInt64(TAGGY), MT_TAG_SHIFT);
        Value* allocaInt = builder.CreatePtrToInt(Alloca, tag->getType());
        Value* taggedPtrInt = builder.CreateOr(allocaInt, tag);
        Value* taggedPtr = builder.CreateIntToPtr(taggedPtrInt, Alloca->getType());
        Alloca->replaceUsesWithIf(taggedPtr, [&](const Use &u){
            return u.getUser() != allocaInt;
        });
        storedTaggedPtr = taggedPtr;

#if __INLINE_MTE_CALL == 1
        InlineAsm *IA = InlineAsm::get(
	      				   FunctionType::get(llvm::Type::getVoidTy(C), {taggedPtr->getType(), newSize->getType()}, false),
	      				   StringRef("mov x2, $0\n mov x3, $1\n mov x17, $0\n cbz $1, 2f\n 1:\n mov x16, $0\n lsr x16, x16, #56\n and x16, x16, #0xFUL\n strb w16, [x17, #0x0]\n add $0, $0, #16\n sub $1, $1, #16\n add x17, x17, 1\n cbnz    $1, 1b\n 2:\n mov $0, x2\n mov $1, x3\n "),
	      				   StringRef("r,r,~{x16},~{x17},~{x2},~{x3},~{memory}"),
	      				   /*hasSideEffects=*/ true,
	      				   /*isAlignStack*/ false,
	      				   InlineAsm::AD_ATT,
	      				   /*canThrow*/ false);
        std::vector<llvm::Value*> args = { taggedPtr, newSize };
        builder.CreateCall(IA, args);
#else
        // call the MTE analogues (i.e., set the tag in memory)
        builder.SetInsertPoint(cast<Instruction>(taggedPtr)->getNextNode());
        builder.CreateCall(mte_set_tag_address_range, {taggedPtr, newSize});
#endif
    }

    void removeTag(Instruction *When){
        // We can only touch the alloca when it dominates our use. Otherwise this violates SSA.
        DominatorTree DT(*F);
        if (!DT.dominates(Alloca, When))
            return;

        assert(When);
        LLVMContext &C = F->getContext();

        if(storedTaggedPtr == nullptr) return;

        IRBuilder<> builder(When);

        // For overhead simulation, we simply apply the tag again for removeTag
#if __INLINE_MTE_CALL == 1
        InlineAsm *IA = InlineAsm::get(
	      				   FunctionType::get(llvm::Type::getVoidTy(C), {storedTaggedPtr->getType(), newSize->getType()}, false),
	      				   StringRef("mov x2, $0\n mov x3, $1\n mov x17, $0\n cbz $1, 2f\n 1:\n mov x16, $0\n lsr x16, x16, #56\n and x16, x16, #0xFUL\n strb w16, [x17, #0x0]\n add $0, $0, #16\n sub $1, $1, #16\n add x17, x17, 1\n cbnz    $1, 1b\n 2:\n mov $0, x2\n mov $1, x3\n "),
	      				   StringRef("r,r,~{x16},~{x17},~{x2},~{x3},~{memory}"),
	      				   /*hasSideEffects=*/ true,
	      				   /*isAlignStack*/ false,
	      				   InlineAsm::AD_ATT,
	      				   /*canThrow*/ false);
        std::vector<llvm::Value*> args = { storedTaggedPtr, newSize };
        builder.CreateCall(IA, args);
#else
        // call the MTE analogues (i.e., set the tag in memory)
        builder.SetInsertPoint(cast<Instruction>(storedTaggedPtr)->getNextNode());
        builder.CreateCall(mte_set_tag_address_range, {storedTaggedPtr, newSize});
#endif
    }

    /// Returns true if the alloca was already untagged at Instruction 'When'.
    [[nodiscard]]
    bool alreadyUntagged(Instruction *When, const DominatorTree &F) const {
    for (Instruction *I : untagPoints)
        if (F.dominates(I, When))
            return true;
    return false;
    }
};
}


void make_stack_obj_size_16(Function &F){
    const DataLayout &DL = F.getParent()->getDataLayout();
    LLVMContext &C = F.getContext();

    std::vector<AllocaInst*> allocas;
    for(BasicBlock &BB : F){
        for(Instruction &I : BB){
            if(AllocaInst *A = dyn_cast<AllocaInst>(&I)){
                allocas.push_back(A);
            }
        }
    }

    std::vector<InstrumentedAlloca> mte_allocas;

    for (AllocaInst *A : allocas) {
        IRBuilder<> builder(A);
        Value *numElem = A->getArraySize(); // number of elements allocated
        Type *Ty = A->getAllocatedType(); // type of element allocated
        if(Ty->isEmptyTy()) continue; // [0 x i8]

        /*** step 1: allocations of size class 16 ***/

        // oldsize = numelem * sizeof(elem)
        Value *oldSize = builder.CreateMul(numElem, builder.getInt32(5)); // DL.getTypeAllocSize(Ty)
        // spill = oldsize % 16
        Value *spill = builder.CreateSRem(oldSize, builder.getInt32(MTE_GRANULE));
        // if( spill != 0 ) { // (N bytes spilled over multiple-of-16)
        // errs() << "Alloca " << *A << " -- oldSize " << *oldSize << " -- spill " << *spill << "\n";
        BasicBlock* basedblock = A->getParent();

        Value* cmp = builder.CreateICmp(CmpInst::Predicate::ICMP_NE, spill, ConstantInt::getNullValue(Type::getInt32Ty(C)));

        Instruction *endOfThen = SplitBlockAndInsertIfThen(cmp, A, /*unreachable*/false);
        builder.SetInsertPoint(endOfThen);
        // remainder = 16 - spill
        Value *remainder = builder.CreateSub(builder.getInt32(MTE_GRANULE), spill);
        // newSize = oldSize + remainder
        Value *newSize = builder.CreateAdd(oldSize, remainder);

        builder.SetInsertPoint(A);
        PHINode* phi = builder.CreatePHI(oldSize->getType(), 2);
        phi->addIncoming(newSize, endOfThen->getParent());
        phi->addIncoming(oldSize, basedblock);

        // update alloca state
        AllocaInst *paddedAlloca = builder.CreateAlloca(builder.getInt8Ty(), phi);
        paddedAlloca->setAlignment(Align(MTE_GRANULE));
        A->replaceAllUsesWith(paddedAlloca);
        A->eraseFromParent();

        mte_allocas.emplace_back(F, paddedAlloca, phi);

    }

    // now that the allocas are the correct size, lets apply and remove tags
    std::vector<IntrinsicInst *> starts;
    std::vector<IntrinsicInst *> ends;
    std::vector<ReturnInst *> rets;

    auto getInstrumentedOrNull = [&mte_allocas](Value *I) {
        InstrumentedAlloca* Error = nullptr;
        if (!I)
            return Error;
        I = I->stripPointerCastsAndAliases();
        I = getUnderlyingObject(I);
        
        for (InstrumentedAlloca &A : mte_allocas)
            if (A.isAlloca(I))
                return &A;
        return Error;
    };

    for (BasicBlock &BB : F) {
        for (Instruction &I : BB) {
            if (auto *II = dyn_cast<IntrinsicInst>(&I)) {
                if (II->getIntrinsicID() == Intrinsic::lifetime_end)
                    ends.push_back(II);
                if (II->getIntrinsicID() == Intrinsic::lifetime_start)
                    starts.push_back(II);
            }
            if (auto *R = dyn_cast<ReturnInst>(&I))
                rets.push_back(R);
        }
    }

    // Tag the respective alloca after each lifetime start.
    for (Instruction *I : starts) {
        if (InstrumentedAlloca *A = getInstrumentedOrNull(I->getOperand(1))){
            A->applyTag(/*When=*/I);
            A->taggedByStart = true;
        }
    }
#if 0
    // Untag the respective alloca after each lifetime end.
    for (Instruction *I : ends) {
        if (InstrumentedAlloca *A = getInstrumentedOrNull(I->getOperand(1)))
            A->removeTag(/*When=*/I);
    }

    // Some allocas will not have life time markers. Tag them right after the alloca
    for(InstrumentedAlloca &A : mte_allocas){
        if(!A.taggedByStart){
            bool dominatesAllRets = true;
            DominatorTree DT(F);
            for(ReturnInst *ret : rets) {
                if (!DT.dominates(A.getAlloca(), ret)) {
                    // We have found an Alloca that does not dominates all rets, annoying, skip
                    dominatesAllRets = false;
                    break;
                }
            }
            if(dominatesAllRets) {
                A.applyTag(A.getAlloca());
            }
        }
    }

    DominatorTree domTree(F);
    // Check every return if there is an alloca that hasn't been untagged yet from a previous lifetime.end.
    for (Instruction *Ret : rets) {
        for (InstrumentedAlloca &A : mte_allocas) {
            // Check if a previous untag already happened.
            // E.g.:
            //   lifetime.end(alloca) <- tag removed here
            //   ret <- no need to untag again here
            if (A.alreadyUntagged(Ret, domTree))
                continue;
            A.removeTag(/*When=*/Ret);
        }
    }
#endif
    // TODO: edge cases like setjmp and exceptions need to clear tags too.

}

void dumpy(Function &F){
    errs() << "~~ DUMPY: " << F.getName() << "\n";
    for(BasicBlock &BB : F){
        for(Instruction &I : BB){
            errs() << I << "\n";
        }
    }
}

PreservedAnalyses HelloWorldPass::run(Function &F, FunctionAnalysisManager &AM) {
    if(F.getName().compare("main") != 0){
        return PreservedAnalyses::all();
    }
    errs() << "[TagPool] running on " << F.getName() << "\n";
    /* TODO:
    - 0. align the entire stack to 16 bytes
    - 1. make all stack allocation sizes multiples of 16 (cast to char* and make size round up to next 16)
    - 2. each alloca result needs to receive a tag: %1 = alloca(...) -> do an OR operation on %1 with tag and ReplaceAllUses to tagged ptr
    - 3. call mte_set_tag_address_range(tagged_ptr, obj_size) for every alloca
    - 4. clean up the stack state on lifetime end

    // NOTE for myself: since we are simulating, maybe not all the alignment properties need to hold.
    */

    make_stack_obj_size_16(F);

    // dumpy(F);
 
    // Run some optimization passes to simplify instrumentation: only if not -O0
    if(!F.hasOptNone())
    {
        AM.clear();
        InstCombinePass().run(F, AM);
        AM.clear();
        SimplifyCFGPass().run(F, AM);
    }

    return PreservedAnalyses::all();
}

#if PASS_MODE == 2
void do_stack_analysis(Function &F, FunctionAnalysisManager &AM) {
    errs() << "[TagPool] Stack Analysis running on " << F.getName() << "\n";
    std::vector<AllocaInst*> allocas;
    for(BasicBlock &BB : F){
        for(Instruction &I : BB){
            if(AllocaInst *A = dyn_cast<AllocaInst>(&I)){
                allocas.push_back(A);
            }
        }
    }

    const DataLayout &DL = F.getParent()->getDataLayout();
    for (AllocaInst *A : allocas) {
        IRBuilder<> builder(A);
        Value *numElem = A->getArraySize(); // number of elements allocated
        Type *Ty = A->getAllocatedType(); // type of element allocated
        if(Ty->isEmptyTy()) continue; // [0 x i8]
        // oldsize = numelem * sizeof(elem)
        Value *oldSize = builder.CreateMul(numElem, builder.getInt64(DL.getTypeAllocSize(Ty)));
        builder.CreateCall(output_alloca_size, {oldSize});
    }
}
#endif

#if PASS_MODE == 3
void apply_tag(AllocaInst *Alloca, int t){
    IRBuilder<> builder(Alloca);
    // set the tag in pointer: ptr | (tag << shift)
    builder.SetInsertPoint(Alloca->getNextNode());
    Value* tag = builder.CreateShl(builder.getInt64(t), MT_TAG_SHIFT);
    Value* allocaInt = builder.CreatePtrToInt(Alloca, tag->getType());
    Value* taggedPtrInt = builder.CreateOr(allocaInt, tag);
    Value* taggedPtr = builder.CreateIntToPtr(taggedPtrInt, Alloca->getType());
    Alloca->replaceUsesWithIf(taggedPtr, [&](const Use &u){
        return u.getUser() != allocaInt;
    });
}

void do_tag_pointers(Function &F, FunctionAnalysisManager &AM) {
    errs() << "[TagPool] Tagging Pointers on " << F.getName() << "\n";
    std::vector<AllocaInst*> allocas;
    for(BasicBlock &BB : F){
        for(Instruction &I : BB){
            if(AllocaInst *A = dyn_cast<AllocaInst>(&I)){
                allocas.push_back(A);
            }
        }
    }

    std::vector<IntrinsicInst *> starts;

    for (BasicBlock &BB : F) {
        for (Instruction &I : BB) {
            if (auto *II = dyn_cast<IntrinsicInst>(&I)) {
                if (II->getIntrinsicID() == Intrinsic::lifetime_start)
                    starts.push_back(II);
            }
        }
    }

    int NextTag = 0;
    // Tag the respective alloca after each lifetime start.
    for (Instruction *I : starts) {
        Value *V = I->getOperand(1);
        V = V->stripPointerCastsAndAliases();
        V = getUnderlyingObject(V);
        for(AllocaInst* Alloca : allocas){
            if(Alloca == V->stripPointerCastsAndAliases()){
                NextTag = (NextTag + 1) % 16;
                apply_tag(Alloca, NextTag);
            }
        }
    }

    // Run some optimization passes to simplify instrumentation: only if not -O0
    if(!F.hasOptNone()){
        AM.clear();
        InstCombinePass().run(F, AM);
        AM.clear();
        SimplifyCFGPass().run(F, AM);
    }
}

#define NOINSTRUMENT_PREFIX "__noinstrument_"
bool isSkip(Value *V) {
    if (V && V->hasName()) {
        StringRef Name = V->getName();
        if (Name.startswith(NOINSTRUMENT_PREFIX))
            return true;
        // Support for mangled C++ names (should maybe do something smarter here)
        if (Name.startswith("_Z"))
            return Name.find(NOINSTRUMENT_PREFIX, 2) != StringRef::npos;
    }
    return false;
}
#endif

PreservedAnalyses HelloWorldPass::run(Module &M, ModuleAnalysisManager &AM) {
#ifdef DEFAULTCLANG
    return PreservedAnalyses::none();
#endif

    auto &FAM = AM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();
    LLVMContext &C = M.getContext();

#if PASS_MODE == 1
    return PreservedAnalyses::none();
#elif PASS_MODE == 2 // stack analysis
    // void output_alloca_size(uint64_t sz){
    FunctionType* OutputAllocaSizeTy = FunctionType::get(Type::getVoidTy(C), {Type::getInt64Ty(C)}, false);
    output_alloca_size = M.getOrInsertFunction("output_alloca_size", OutputAllocaSizeTy);
    auto *a = dyn_cast_or_null<Function>(output_alloca_size.getCallee());
    a->setLinkage(GlobalValue::ExternalWeakLinkage);
    a->setUnnamedAddr(GlobalValue::UnnamedAddr::None);

    for (Function &F : M){
        if (!F.isDeclaration()){
            do_stack_analysis(F, FAM);
        }
    }
    return PreservedAnalyses::none();
#elif PASS_MODE == 3 // only tag pointers
    for (Function &F : M){
        if (!F.isDeclaration() && F.hasFnAttribute(Attribute::SafeStack) && !isSkip(&F)){
            do_tag_pointers(F, FAM);
        }
    }
    return PreservedAnalyses::none();
#endif

    // void mte_set_tag_address_range(void *ptr, int range); //stg
    FunctionType* MTESetTagTy = FunctionType::get(Type::getVoidTy(C), {Type::getInt8PtrTy(C), Type::getInt64Ty(C)}, false);
    mte_set_tag_address_range = M.getOrInsertFunction("mte_set_tag_address_range", MTESetTagTy);
    auto *f = dyn_cast_or_null<Function>(mte_set_tag_address_range.getCallee());
    f->setLinkage(GlobalValue::ExternalWeakLinkage);
    f->setUnnamedAddr(GlobalValue::UnnamedAddr::None);

    for (Function &F : M){
        if (!F.isDeclaration()){
            run(F, FAM);
        }
    }
    return PreservedAnalyses::none();
}
