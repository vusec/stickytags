//===- SafeStack.cpp - Safe Stack Insertion -------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This pass splits the stack into the safe stack (kept as-is for LLVM backend)
// and the unsafe stack (explicitly allocated and managed through the runtime
// support library).
//
// http://clang.llvm.org/docs/SafeStack.html
//
//===----------------------------------------------------------------------===//

#include "SafeStackLayout.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/Analysis/DomTreeUpdater.h"
#include "llvm/Analysis/InlineCost.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/StackLifetime.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/CodeGen/TargetLowering.h"
#include "llvm/CodeGen/TargetPassConfig.h"
#include "llvm/CodeGen/TargetSubtargetInfo.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/ConstantRange.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DIBuilder.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/Value.h"
#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <optional>
#include <string>
#include <utility>

// redpool
#include <llvm/Analysis/DominanceFrontier.h>
#include <llvm/IR/Attributes.h>
#include <llvm/IR/DebugInfo.h>

using namespace llvm;
using namespace llvm::safestack;

#define ALLOCA_TAGGING
#define ALLOCA_REPLACE_ALL_USES

#define TAG_OFFSET_ONE (0x100000000000000)
#define TAG_AND_15 (0xf00000000000000)
// stack span start is 16MB aligned
#define STACK_SPAN_START_MASK (~((1 << 24)-1))

#if 0
// snippet to call printf() with Value* 
Type *intType = Type::getInt32Ty(F.getContext());
// Declare C standard library printf 
std::vector<Type *> printfArgsTypes({Type::getInt8PtrTy(F.getContext())});
FunctionType *printfType = FunctionType::get(intType, printfArgsTypes, true);
FunctionCallee printfFunc = F.getParent()->getOrInsertFunction("printf", printfType);

// The format string for the printf function, declared as a global literal
Value *str = IRBUser.CreateGlobalStringPtr("Delta %d SizeClass %d SizeClassInBits %d Jumps %d Tag %d\n", "str");

std::vector<Value *> argsV({str, Delta, IRBUser.getInt64(SizeClass), SizeClassInBits, Jumps, Tag});
IRBUser.CreateCall(printfFunc, argsV, "calltmp");
#endif

Type* cursedType;

#define DEBUG_TYPE "safe-stack"

#define FAIL(msg) do {                                     \
    llvm::errs() << "[SizedStack] error: " << msg << "\n"; \
    exit(1);                                               \
  } while (0);


#define NOINSTRUMENT_PREFIX "__noinstrument_"
bool isNoInstrument(Value *V) {
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

void setNoInstrument(Value *V) {
    V->setName(std::string(NOINSTRUMENT_PREFIX) + V->getName().str());
}

bool shouldInstrument(Function &F) {
    if (F.isDeclaration())
        return false;

    if (isNoInstrument(&F))
        return false;

    return true;
}

static bool stripDebugInfoRecursive(Function &F, SmallPtrSetImpl<Function*> &Visited) {
    if (Visited.count(&F))
        return false;
    Visited.insert(&F);
    bool Changed = stripDebugInfo(F);
    if (Changed) {
        for (Instruction &I : instructions(F)) {
            auto *CB = dyn_cast<CallBase>(&I);
            if (CB && CB->getCalledFunction())
                stripDebugInfoRecursive(*CB->getCalledFunction(), Visited);
        }
    }
    return Changed;
}

static bool stripDebugInfoRecursive(Function &F) {
    SmallPtrSet<Function*, 4> Visited;
    return stripDebugInfoRecursive(F, Visited);
}

Function *getOrInsertNoInstrumentFunction(Module &M, StringRef Name, FunctionType *Ty) {
    std::string FullName(NOINSTRUMENT_PREFIX);
    FullName += Name;
    if (Function *F = M.getFunction(FullName)) {
        if (F->getFunctionType() != Ty) {
            errs() << "unexpected type for helper function " << FullName << "\n";
            errs() << "  expected: " << *Ty << "\n";
            errs() << "  found:    " << *F->getFunctionType() << "\n";
            exit(1);
        }
        stripDebugInfoRecursive(*F);
        return F;
    }
    return Function::Create(Ty, GlobalValue::ExternalLinkage, FullName, &M);
}

namespace llvm {

STATISTIC(NumFunctions, "Total number of functions");
STATISTIC(NumUnsafeStackFunctions, "Number of functions with unsafe stack");
STATISTIC(NumUnsafeStackRestorePointsFunctions,
          "Number of functions that use setjmp or exceptions");

STATISTIC(NumAllocas, "Total number of allocas");
STATISTIC(NumUnsafeStaticAllocas, "Number of unsafe static allocas");
STATISTIC(NumUnsafeDynamicAllocas, "Number of unsafe dynamic allocas");
STATISTIC(NumUnsafeByValArguments, "Number of unsafe byval arguments");
STATISTIC(NumUnsafeStackRestorePoints, "Number of setjmps and landingpads");

STATISTIC(NumUnsafeStacks, "Total number of unsafe stacks");
STATISTIC(NumUnsafeStacksPerFunction, "Maximum number of unsafe stacks per function");
STATISTIC(NumDynAllocasMovedToHeap, "Number of dynamic allocas moved to the heap");
static const std::string kUnsafeStackPtrCountVar         = "__sizedstack_count";
static const std::string kUnsafeStackPtrVar              = "__sizedstack_ptrs";
static const std::string kUnsafeStackPtrVarFinal         = "__sizedstack_ptrs_final";
static const std::string kUnsafeStackPtrVarTemp          = "__sizedstack_ptrs_temp";
static const std::string kUnsafeStackSizeClassesVar      = "__sizedstack_sizeclasses";
static const std::string kUnsafeStackSizeClassesVarFinal = "__sizedstack_sizeclasses_final";

static const unsigned kDefaultUnsafeStackSize = 0x2800000;
// Size classes from TCMalloc
// static const std::vector<uint64_t> kSizeClasses = {
//   16, 32, 48, 64, 80, 96, 112, 128, 144, 160, 176, 192, 208, 224, 240, 256,
//   288, 320, 352, 384, 416, 448, 480, 512, 576, 640, 704, 768, 832, 960, 1152,
//   1280, 1408, 1536, 1664, 1920, 2304, 2560, 2816, 3072, 3328, 3584, 4608, 5120,
//   5632, 6656, 7168, 9216, 10240, 11264, 13312, 14336, 18432, 22528, 26624,
//   28672, 36864, 45056, 53248, 61440, 73728, 81920, 90112, 98304, 106496, 114688,
//   122880, 131072, 139264, 147456, 155648, 163840, 172032, 180224, 188416,
//   196608, 204800, 212992, 221184, 229376, 237568, 245760, 253952, 262144
// };

// Multiples of 2 size classes
static const std::vector<uint64_t> kSizeClasses = {
  16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144
};

// Defined in RedzoneChecks.cpp
cl::opt<unsigned long long> OptRedzoneSize("redzone-size",
    cl::desc("Redzone size"),
    cl::init(0));

cl::opt<int> OptRedzoneValue("redzone-value",
    cl::desc("Guard value for redzone initalization"),
    cl::init(0x42));

#ifndef USE_GOLD_PASSES
static cl::opt<bool> ClSizedStack(
    "sized-stack",
    cl::desc("If set will be enabled"),
    cl::init(true));
#endif
static cl::opt<bool> OptInitRedzones("stack-init-redzones",
    cl::desc("Initialize stack redzones upon allocation"),
    cl::init(false));
static cl::opt<bool> OptStackShadowMem("stack-shadowmem",
    cl::desc("Maintain shadow memory on stack allocation"),
    cl::init(false));
static cl::opt<bool> OptOnlyNoDynAllocas("only-no-dyn-allocas",
    cl::desc("Only move dynamic allocas to the heap, don't do anything with static allocas"),
    cl::init(false));

} // namespace llvm

/// Use __safestack_pointer_address even if the platform has a faster way of
/// access safe stack pointer.
static cl::opt<bool>
    SafeStackUsePointerAddress("safestack-use-pointer-address",
                                  cl::init(false), cl::Hidden);

static cl::opt<bool> ClColoring("safe-stack-coloring",
                                cl::desc("enable safe stack coloring"),
                                cl::Hidden, cl::init(true));

namespace {

/// Rewrite an SCEV expression for a memory access address to an expression that
/// represents offset from the given alloca.
///
/// The implementation simply replaces all mentions of the alloca with zero.
class AllocaOffsetRewriter : public SCEVRewriteVisitor<AllocaOffsetRewriter> {
  const Value *AllocaPtr;

public:
  AllocaOffsetRewriter(ScalarEvolution &SE, const Value *AllocaPtr)
      : SCEVRewriteVisitor(SE), AllocaPtr(AllocaPtr) {}

  const SCEV *visitUnknown(const SCEVUnknown *Expr) {
    if (Expr->getValue() == AllocaPtr)
      return SE.getZero(Expr->getType());
    return Expr;
  }
};

class SizedStackRuntime {
  GlobalVariable *stackPointerArray;
  
  StringMap<size_t> typeIndexByTypeId;
  size_t typeIndexNext;
  SmallVector<uint64_t, 16> AssignedSizeClasses;

  Module &M;
  const DataLayout &DL;

  PointerType *StackPtrTy;
  IntegerType *IntPtrTy;
  IntegerType *Int64Ty;

  static std::string getStaticStackID(uint64_t Size, const Value &V);
  size_t getTypeIndex(StringRef StackID);
  static uint64_t roundUpToSizeClass(uint64_t Size);

  GlobalVariable *createStackPtrArray(StringRef varName, size_t count);
  GlobalVariable *createStackSpansArray(StringRef varName, size_t count);
  GlobalVariable *createStackPtrCount(StringRef varName, size_t count);
  GlobalVariable *createSizeClassArray(StringRef varName);

public:
  /// Unsafe stack alignment. Each stack frame must ensure that the stack is
  /// aligned to this value. We need to re-align the unsafe stack if the
  /// alignment of any object on the stack exceeds this value.
  ///
  /// 16 seems like a reasonable upper bound on the alignment of objects that we
  /// might expect to appear on the stack on most common targets.
  enum { StackAlignment = 16 };

  Function *DynAllocFunc, *DynFreeFunc, *DynFreeOptFunc, *ShadowMemPoisonFunc;

  SizedStackRuntime(Module &M)
      : M(M), DL(M.getDataLayout()),
        StackPtrTy(Type::getInt8PtrTy(M.getContext())),
        IntPtrTy(DL.getIntPtrType(M.getContext())),
        Int64Ty(Type::getInt64Ty(M.getContext())) {}

  /// \brief Calculate the allocation size of a given alloca. Returns 0 if the
  /// size can not be statically determined.
  uint64_t getStaticAllocaAllocationSize(const AllocaInst* AI);

  bool initialize();
  bool finalize();

  std::string getStackID(const AllocaInst &AI);
  std::string getStackID(const Argument &Arg);

  Value *getOrCreateUnsafeStackPtr(IRBuilder<> &IRB, Function &F, StringRef typeId);
  
}; // class SizedStackRuntime


/// The SafeStack pass splits the stack of each function into the safe
/// stack, which is only accessed through memory safe dereferences (as
/// determined statically), and the unsafe stack, which contains all
/// local variables that are accessed in ways that we can't prove to
/// be safe.
class SafeStack {
  Function &F;
  const TargetLoweringBase &TL;
  const DataLayout &DL;
  DomTreeUpdater *DTU;
  ScalarEvolution &SE;
  DominatorTree &DT;
  DominanceFrontier &DF;
  SizedStackRuntime &RT;

  Type *StackPtrTy;
  Type *IntPtrTy;
  Type *Int32Ty;
  Type *Int8Ty;

  Value *UnsafeStackPtr = nullptr;

  /// Unsafe stack alignment. Each stack frame must ensure that the stack is
  /// aligned to this value. We need to re-align the unsafe stack if the
  /// alignment of any object on the stack exceeds this value.
  ///
  /// 16 seems like a reasonable upper bound on the alignment of objects that we
  /// might expect to appear on the stack on most common targets.
  static constexpr Align StackAlignment = Align::Constant<16>();

  /// Return the value of the stack canary.
  Value *getStackGuard(IRBuilder<> &IRB, Function &F);

  /// Load stack guard from the frame and check if it has changed.
  void checkStackGuard(IRBuilder<> &IRB, Function &F, Instruction &RI,
                       AllocaInst *StackGuardSlot, Value *StackGuard);

  /// Find all static allocas, dynamic allocas, return instructions and
  /// stack restore points (exception unwind blocks and setjmp calls) in the
  /// given function and append them to the respective vectors.
  void findInsts(Function &F, SmallVectorImpl<AllocaInst *> &StaticAllocas,
                 SmallVectorImpl<AllocaInst *> &DynamicAllocas,
                 SmallVectorImpl<Argument *> &ByValArguments,
                 SmallVectorImpl<Instruction *> &Returns,
                 SmallVectorImpl<Instruction *> &StackRestorePoints);

  /// Calculate the allocation size of a given alloca. Returns 0 if the
  /// size can not be statically determined.
  uint64_t getStaticAllocaAllocationSize(const AllocaInst* AI);

  /// Allocate space for all static allocas in \p StaticAllocas,
  /// replace allocas with pointers into the unsafe stack.
  ///
  /// \returns A pointer to the top of the unsafe stack after all unsafe static
  /// allocas are allocated.
  Value *moveStaticAllocasToUnsafeStack(IRBuilder<> &IRB, Function &F,
                                        ArrayRef<AllocaInst *> StaticAllocas,
                                        ArrayRef<Argument *> ByValArguments,
                                        Instruction *BasePointer,
                                        AllocaInst *StackGuardSlot,
                                        Value *UnsafeStackPtr,
                                        StringRef StackID);

  /// Generate code to restore the stack after all stack restore points
  /// in \p StackRestorePoints.
  ///
  /// \returns A local variable in which to maintain the dynamic top of the
  /// unsafe stack if needed.
  AllocaInst *
  createStackRestorePoints(IRBuilder<> &IRB, Function &F,
                           ArrayRef<Instruction *> StackRestorePoints,
                           Value *StaticTop, bool NeedDynamicTop,
                           Value *UnsafeStackPtr, StringRef StackID);


  /// Replace all allocas in \p DynamicAllocas with code to allocate
  /// space dynamically on the unsafe stack and store the dynamic unsafe stack
  /// top to \p DynamicTop if non-null.
  void moveDynamicAllocasToHeap(Function &F, ArrayRef<AllocaInst *> DynamicAllocas);

  void moveDynamicAllocasToUnsafeStack(Function &F, Value *UnsafeStackPtr,
                                       AllocaInst *DynamicTop,
                                       ArrayRef<AllocaInst *> DynamicAllocas);

  bool IsSafeStackAlloca(const Value *AllocaPtr, uint64_t AllocaSize);

  bool IsMemIntrinsicSafe(const MemIntrinsic *MI, const Use &U,
                          const Value *AllocaPtr, uint64_t AllocaSize);
  bool IsAccessSafe(Value *Addr, uint64_t Size, const Value *AllocaPtr,
                    uint64_t AllocaSize);

  bool ShouldInlinePointerAddress(CallInst &CI);
  void TryInlinePointerAddress();

public:
  SafeStack(Function &F, const TargetLoweringBase &TL, const DataLayout &DL,
            DomTreeUpdater *DTU, ScalarEvolution &SE, DominatorTree &DT, DominanceFrontier &DF,
            SizedStackRuntime &RT)
      : F(F), TL(TL), DL(DL), DTU(DTU), SE(SE), DT(DT), DF(DF), RT(RT), 
        StackPtrTy(Type::getInt8PtrTy(F.getContext())),
        IntPtrTy(DL.getIntPtrType(F.getContext())),
        Int32Ty(Type::getInt32Ty(F.getContext())),
        Int8Ty(Type::getInt8Ty(F.getContext())) {}

  // Run the transformation on the associated function.
  // Returns whether the function was changed.
  bool run();
};

constexpr Align SafeStack::StackAlignment;

uint64_t SafeStack::getStaticAllocaAllocationSize(const AllocaInst* AI) {
  uint64_t Size = DL.getTypeAllocSize(AI->getAllocatedType());
  if (AI->isArrayAllocation()) {
    auto C = dyn_cast<ConstantInt>(AI->getArraySize());
    if (!C)
      return 0;
    Size *= C->getZExtValue();
  }
  return Size;
}

bool SafeStack::IsAccessSafe(Value *Addr, uint64_t AccessSize,
                             const Value *AllocaPtr, uint64_t AllocaSize) {
  const SCEV *AddrExpr = SE.getSCEV(Addr);
  const auto *Base = dyn_cast<SCEVUnknown>(SE.getPointerBase(AddrExpr));
  if (!Base || Base->getValue() != AllocaPtr) {
    LLVM_DEBUG(
        dbgs() << "[SafeStack] "
               << (isa<AllocaInst>(AllocaPtr) ? "Alloca " : "ByValArgument ")
               << *AllocaPtr << "\n"
               << "SCEV " << *AddrExpr << " not directly based on alloca\n");
    return false;
  }

  const SCEV *Expr = SE.removePointerBase(AddrExpr);
  uint64_t BitWidth = SE.getTypeSizeInBits(Expr->getType());
  ConstantRange AccessStartRange = SE.getUnsignedRange(Expr);
  ConstantRange SizeRange =
      ConstantRange(APInt(BitWidth, 0), APInt(BitWidth, AccessSize));
  ConstantRange AccessRange = AccessStartRange.add(SizeRange);
  ConstantRange AllocaRange =
      ConstantRange(APInt(BitWidth, 0), APInt(BitWidth, AllocaSize));
  bool Safe = AllocaRange.contains(AccessRange);

  LLVM_DEBUG(
      dbgs() << "[SafeStack] "
             << (isa<AllocaInst>(AllocaPtr) ? "Alloca " : "ByValArgument ")
             << *AllocaPtr << "\n"
             << "            Access " << *Addr << "\n"
             << "            SCEV " << *Expr
             << " U: " << SE.getUnsignedRange(Expr)
             << ", S: " << SE.getSignedRange(Expr) << "\n"
             << "            Range " << AccessRange << "\n"
             << "            AllocaRange " << AllocaRange << "\n"
             << "            " << (Safe ? "safe" : "unsafe") << "\n");

  return Safe;
}

bool SafeStack::IsMemIntrinsicSafe(const MemIntrinsic *MI, const Use &U,
                                   const Value *AllocaPtr,
                                   uint64_t AllocaSize) {
  if (auto MTI = dyn_cast<MemTransferInst>(MI)) {
    if (MTI->getRawSource() != U && MTI->getRawDest() != U)
      return true;
  } else {
    if (MI->getRawDest() != U)
      return true;
  }

  const auto *Len = dyn_cast<ConstantInt>(MI->getLength());
  // Non-constant size => unsafe. FIXME: try SCEV getRange.
  if (!Len) return false;
  return IsAccessSafe(U, Len->getZExtValue(), AllocaPtr, AllocaSize);
}

/// Check whether a given allocation must be put on the safe
/// stack or not. The function analyzes all uses of AI and checks whether it is
/// only accessed in a memory safe way (as decided statically).
bool SafeStack::IsSafeStackAlloca(const Value *AllocaPtr, uint64_t AllocaSize) {
  // Go through all uses of this alloca and check whether all accesses to the
  // allocated object are statically known to be memory safe and, hence, the
  // object can be placed on the safe stack.
  SmallPtrSet<const Value *, 16> Visited;
  SmallVector<const Value *, 8> WorkList;
  WorkList.push_back(AllocaPtr);

  // A DFS search through all uses of the alloca in bitcasts/PHI/GEPs/etc.
  while (!WorkList.empty()) {
    const Value *V = WorkList.pop_back_val();
    for (const Use &UI : V->uses()) {
      auto I = cast<const Instruction>(UI.getUser());
      assert(V == UI.get());

      switch (I->getOpcode()) {
      case Instruction::Load:
        if (!IsAccessSafe(UI, DL.getTypeStoreSize(I->getType()), AllocaPtr,
                          AllocaSize))
          return false;
        break;

      case Instruction::VAArg:
        // "va-arg" from a pointer is safe.
        break;
      case Instruction::Store:
        if (V == I->getOperand(0)) {
          // Stored the pointer - conservatively assume it may be unsafe.
          LLVM_DEBUG(dbgs()
                     << "[SafeStack] Unsafe alloca: " << *AllocaPtr
                     << "\n            store of address: " << *I << "\n");
          return false;
        }

        if (!IsAccessSafe(UI, DL.getTypeStoreSize(I->getOperand(0)->getType()),
                          AllocaPtr, AllocaSize))
          return false;
        break;

      case Instruction::Ret:
        // Information leak.
        return false;

      case Instruction::Call:
      case Instruction::Invoke: {
        const CallBase &CS = *cast<CallBase>(I);

        if (I->isLifetimeStartOrEnd())
          continue;

        if (const MemIntrinsic *MI = dyn_cast<MemIntrinsic>(I)) {
          if (!IsMemIntrinsicSafe(MI, UI, AllocaPtr, AllocaSize)) {
            LLVM_DEBUG(dbgs()
                       << "[SafeStack] Unsafe alloca: " << *AllocaPtr
                       << "\n            unsafe memintrinsic: " << *I << "\n");
            return false;
          }
          continue;
        }

        // LLVM 'nocapture' attribute is only set for arguments whose address
        // is not stored, passed around, or used in any other non-trivial way.
        // We assume that passing a pointer to an object as a 'nocapture
        // readnone' argument is safe.
        // FIXME: a more precise solution would require an interprocedural
        // analysis here, which would look at all uses of an argument inside
        // the function being called.
        auto B = CS.arg_begin(), E = CS.arg_end();
        for (const auto *A = B; A != E; ++A)
          if (A->get() == V)
            if (!(CS.doesNotCapture(A - B) && (CS.doesNotAccessMemory(A - B) ||
                                               CS.doesNotAccessMemory()))) {
              LLVM_DEBUG(dbgs() << "[SafeStack] Unsafe alloca: " << *AllocaPtr
                                << "\n            unsafe call: " << *I << "\n");
              return false;
            }
        continue;
      }

      default:
        if (Visited.insert(I).second)
          WorkList.push_back(cast<const Instruction>(I));
      }
    }
  }

  // All uses of the alloca are safe, we can place it on the safe stack.
  return true;
}

Value *SafeStack::getStackGuard(IRBuilder<> &IRB, Function &F) {
  Value *StackGuardVar = TL.getIRStackGuard(IRB);
  Module *M = F.getParent();

  if (!StackGuardVar) {
    TL.insertSSPDeclarations(*M);
    return IRB.CreateCall(Intrinsic::getDeclaration(M, Intrinsic::stackguard));
  }

  return IRB.CreateLoad(StackPtrTy, StackGuardVar, "StackGuard");
}

void SafeStack::findInsts(Function &F,
                          SmallVectorImpl<AllocaInst *> &StaticAllocas,
                          SmallVectorImpl<AllocaInst *> &DynamicAllocas,
                          SmallVectorImpl<Argument *> &ByValArguments,
                          SmallVectorImpl<Instruction *> &Returns,
                          SmallVectorImpl<Instruction *> &StackRestorePoints) {
  for (Instruction &I : instructions(&F)) {
    if (auto AI = dyn_cast<AllocaInst>(&I)) {
      ++NumAllocas;

      uint64_t Size = getStaticAllocaAllocationSize(AI);
      if (IsSafeStackAlloca(AI, Size))
        continue;

      if (AI->isStaticAlloca()) {
        ++NumUnsafeStaticAllocas;
        StaticAllocas.push_back(AI);
      } else {
        ++NumUnsafeDynamicAllocas;
        DynamicAllocas.push_back(AI);
      }
    } else if (auto RI = dyn_cast<ReturnInst>(&I)) {
      if (CallInst *CI = I.getParent()->getTerminatingMustTailCall())
        Returns.push_back(CI);
      else
        Returns.push_back(RI);
    } else if (auto CI = dyn_cast<CallInst>(&I)) {
      // setjmps require stack restore.
      if (CI->getCalledFunction() && CI->canReturnTwice())
        StackRestorePoints.push_back(CI);
    } else if (auto LP = dyn_cast<LandingPadInst>(&I)) {
      // Exception landing pads require stack restore.
      StackRestorePoints.push_back(LP);
    } else if (auto II = dyn_cast<IntrinsicInst>(&I)) {
      if (II->getIntrinsicID() == Intrinsic::gcroot)
        report_fatal_error(
            "gcroot intrinsic not compatible with safestack attribute");
    }
  }
  for (Argument &Arg : F.args()) {
    if (!Arg.hasByValAttr())
      continue;
    uint64_t Size = DL.getTypeStoreSize(Arg.getParamByValType());
    if (IsSafeStackAlloca(&Arg, Size))
      continue;
    ++NumUnsafeByValArguments;
    ByValArguments.push_back(&Arg);
  }
}

AllocaInst *
SafeStack::createStackRestorePoints(IRBuilder<> &IRB, Function &F,
                                    ArrayRef<Instruction *> StackRestorePoints,
                                    Value *StaticTop, bool NeedDynamicTop,
                                    Value *UnsafeStackPtr, StringRef StackID) {
  assert(StaticTop && "The stack top isn't set.");

  if (StackRestorePoints.empty())
    return nullptr;

  // We need the current value of the shadow stack pointer to restore
  // after longjmp or exception catching.

  // FIXME: On some platforms this could be handled by the longjmp/exception
  // runtime itself.

  AllocaInst *DynamicTop = nullptr;
  if (NeedDynamicTop) {
    // If we also have dynamic alloca's, the stack pointer value changes
    // throughout the function. For now we store it in an alloca.
    DynamicTop = IRB.CreateAlloca(StackPtrTy, /*ArraySize=*/nullptr,
                                  "unsafe_stack_dynamic_ptr_" + StackID);
    IRB.CreateStore(StaticTop, DynamicTop);
  }

  // Restore current stack pointer after longjmp/exception catch.
  for (Instruction *I : StackRestorePoints) {
    ++NumUnsafeStackRestorePoints;

    IRB.SetInsertPoint(I->getNextNode());
    Value *CurrentTop =
        DynamicTop ? IRB.CreateLoad(StackPtrTy, DynamicTop) : StaticTop;
    IRB.CreateStore(CurrentTop, UnsafeStackPtr);
  }

  return DynamicTop;
}

void SafeStack::checkStackGuard(IRBuilder<> &IRB, Function &F, Instruction &RI,
                                AllocaInst *StackGuardSlot, Value *StackGuard) {
  Value *V = IRB.CreateLoad(StackPtrTy, StackGuardSlot);
  Value *Cmp = IRB.CreateICmpNE(StackGuard, V);

  auto SuccessProb = BranchProbabilityInfo::getBranchProbStackProtector(true);
  auto FailureProb = BranchProbabilityInfo::getBranchProbStackProtector(false);
  MDNode *Weights = MDBuilder(F.getContext())
                        .createBranchWeights(SuccessProb.getNumerator(),
                                             FailureProb.getNumerator());
  Instruction *CheckTerm =
      SplitBlockAndInsertIfThen(Cmp, &RI, /* Unreachable */ true, Weights, DTU);
  IRBuilder<> IRBFail(CheckTerm);
  // FIXME: respect -fsanitize-trap / -ftrap-function here?
  FunctionCallee StackChkFail =
      F.getParent()->getOrInsertFunction("__stack_chk_fail", IRB.getVoidTy());
  IRBFail.CreateCall(StackChkFail, {});
}

/// We explicitly compute and set the unsafe stack layout for all unsafe
/// static alloca instructions. We save the unsafe "base pointer" in the
/// prologue into a local variable and restore it in the epilogue.
Value *SafeStack::moveStaticAllocasToUnsafeStack(
    IRBuilder<> &IRB, Function &F, ArrayRef<AllocaInst *> StaticAllocas,
    ArrayRef<Argument *> ByValArguments, Instruction *BasePointer,
    AllocaInst *StackGuardSlot, Value *UnsafeStackPtr, StringRef StackID) {
  if (StaticAllocas.empty() && ByValArguments.empty())
    return BasePointer;

  DIBuilder DIB(*F.getParent());

  StackLifetime SSC(F, StaticAllocas, StackLifetime::LivenessType::May);
  static const StackLifetime::LiveRange NoColoringRange(1, true);
  if (ClColoring)
    SSC.run();

  for (const auto *I : SSC.getMarkers()) {
    auto *Op = dyn_cast<Instruction>(I->getOperand(1));
    const_cast<IntrinsicInst *>(I)->eraseFromParent();
    // Remove the operand bitcast, too, if it has no more uses left.
    if (Op && Op->use_empty())
      Op->eraseFromParent();
  }

  // Unsafe stack always grows down.
  StackLayout SSL(StackAlignment);
  if (StackGuardSlot) {
    Type *Ty = StackGuardSlot->getAllocatedType();
    Align Align = std::max(DL.getPrefTypeAlign(Ty), StackGuardSlot->getAlign());
    SSL.addObject(StackGuardSlot, getStaticAllocaAllocationSize(StackGuardSlot),
                  Align, SSC.getFullLiveRange());
  }

  // All entries have the same size on the stack.
  // FIXME: getting this from the string is dirty
  uint64_t SizeClass = std::stoll(StackID.substr(StackID.rfind('_') + 1).str());

  for (Argument *Arg : ByValArguments) {
    Type *Ty = Arg->getParamByValType();
    uint64_t Size = DL.getTypeStoreSize(Ty);
    if (Size == 0)
      Size = 1; // Don't create zero-sized stack objects.

    // Ensure the object is properly aligned.
    Align Align = DL.getPrefTypeAlign(Ty);
    if (auto A = Arg->getParamAlign())
      Align = std::max(Align, *A);

      // Alignment must be compatible with size class.
    if (SizeClass % Align.value()) {
      FAIL("alignment " << Align.value() << " does not divide size class " << SizeClass << ":\n" << *Arg);
    }

    SSL.addObject(Arg, SizeClass, Align, SSC.getFullLiveRange());
  }

  for (AllocaInst *AI : StaticAllocas) {
    Type *Ty = AI->getAllocatedType();
    uint64_t Size = getStaticAllocaAllocationSize(AI);
    if (Size == 0)
      Size = 1; // Don't create zero-sized stack objects.

    // Ensure the object is properly aligned.
    Align Align = std::max(DL.getPrefTypeAlign(Ty), AI->getAlign());
    
    // Alignment must be compatible with size class.
    if (SizeClass % Align.value()) {
      FAIL("alignment " << Align.value() << " does not divide size class " << SizeClass << ":\n" << *AI);
    }

    SSL.addObject(AI, SizeClass, Align, ClColoring ? SSC.getLiveRange(AI) : NoColoringRange);
  }

  SSL.computeLayout();
  Align FrameAlignment = SSL.getFrameAlignment();

  // FIXME: tell SSL that we start at a less-then-MaxAlignment aligned location
  // (AlignmentSkew).
  if (FrameAlignment > StackAlignment) {
      FAIL("frame alignment " << FrameAlignment.value() << " bigger than stack alignment " <<
               RT.StackAlignment << ", need to realign but this would mess with sizeclass offsets");
    // Re-align the base pointer according to the max requested alignment.
    // IRB.SetInsertPoint(BasePointer->getNextNode());
    // BasePointer = cast<Instruction>(IRB.CreateIntToPtr(
    //     IRB.CreateAnd(
    //         IRB.CreatePtrToInt(BasePointer, IntPtrTy),
    //         ConstantInt::get(IntPtrTy, ~(FrameAlignment.value() - 1))),
    //     StackPtrTy));
  }

  if (SizeClass % FrameAlignment.value())
    FAIL("size class " << SizeClass << " is not a multiple of frame alignment " << FrameAlignment.value());

  IRB.SetInsertPoint(BasePointer->getNextNode());

  if (StackGuardSlot) {
    unsigned Offset = SSL.getObjectOffset(StackGuardSlot);
    Value *Off = IRB.CreateGEP(Int8Ty, BasePointer, // BasePointer is i8*
                               ConstantInt::get(Int32Ty, -Offset));
    Value *NewAI =
        IRB.CreateBitCast(Off, StackGuardSlot->getType(), "StackGuardSlot");

    // Replace alloc with the new location.
    StackGuardSlot->replaceAllUsesWith(NewAI);
    StackGuardSlot->eraseFromParent();
  }

#ifdef ALLOCA_TAGGING
  // should be able to share SpanStart with allocas but this is easier
  // byval args are probably are rare anyway
  Instruction *SpanStartByVal = nullptr;
#endif

  SetVector<uint64_t> ObjectOffsets;

  for (Argument *Arg : ByValArguments) {
    unsigned Offset = SSL.getObjectOffset(Arg);
    if (Offset % SizeClass)
      FAIL("object offset " << Offset << " is not a multiple of sizeclass " << SizeClass);

    ObjectOffsets.insert(Offset);
    MaybeAlign Align(SSL.getObjectAlignment(Arg));
    Type *Ty = Arg->getParamByValType();

    uint64_t Size = DL.getTypeStoreSize(Ty);
    if (Size == 0)
      Size = 1; // Don't create zero-sized stack objects.

    Value *Off = IRB.CreateGEP(Int8Ty, BasePointer, // BasePointer is i8*
                               ConstantInt::get(Int32Ty, -Offset));
    Value *NewArg = IRB.CreateBitCast(Off, Arg->getType(),
                                     Arg->getName() + ".unsafe-byval");

    // Replace alloc with the new location.
    replaceDbgDeclare(Arg, BasePointer, DIB, DIExpression::ApplyOffset,
                      -Offset);
#ifdef ALLOCA_TAGGING
    // We can optimize this by calculating the tags less frequently
    // but ByVal arguments are probably rare?
    Value *AllocaPtr = IRB.CreatePtrToInt(NewArg, IntPtrTy);
   if(SpanStartByVal == nullptr){
        SpanStartByVal = dyn_cast<Instruction>(IRB.CreateAnd(AllocaPtr, STACK_SPAN_START_MASK));
    }

    Value *Delta = IRB.CreateSub(AllocaPtr, SpanStartByVal);
    Value *Jumps = IRB.CreateLShr(Delta, IRB.getInt64((int)log2(SizeClass)));
    Value *TagVal = IRB.CreateAnd(Jumps, IRB.getInt64(15));

    Value *TagShifted = IRB.CreateShl(TagVal, 56);
    Value *AllocaInt = IRB.CreatePtrToInt(NewArg, IntPtrTy);
    Value *TaggedAlloca = IRB.CreateOr(AllocaInt, TagShifted);
    Value *TaggedPtr = IRB.CreateIntToPtr(TaggedAlloca, Arg->getType());
    NewArg = TaggedPtr;
#endif

    Arg->replaceAllUsesWith(NewArg);
    IRB.SetInsertPoint(cast<Instruction>(NewArg)->getNextNode());
    IRB.CreateMemCpy(Off, Align, Arg, Arg->getParamAlign(), Size);
  }

#ifdef ALLOCA_TAGGING
  Instruction *Tag = nullptr;
  Instruction *SpanStart = nullptr;
  bool first = true;
#endif

  // Allocate space for every unsafe static AllocaInst on the unsafe stack.
  for (AllocaInst *AI : StaticAllocas) {
    IRB.SetInsertPoint(AI);
    unsigned Offset = SSL.getObjectOffset(AI);
    if (Offset % SizeClass)
      FAIL("object offset " << Offset << " is not a multiple of sizeclass " << SizeClass);
    ObjectOffsets.insert(Offset);

    replaceDbgDeclare(AI, BasePointer, DIB, DIExpression::ApplyOffset, -Offset);
    replaceDbgValueForAlloca(AI, BasePointer, DIB, -Offset);

    // Replace uses of the alloca with the new location.
    // Insert address calculation close to each use to work around PR27844.
    std::string Name = std::string(AI->getName()) + ".unsafe";
#ifdef ALLOCA_REPLACE_ALL_USES
    // SafeStack places calculation of new alloca address close to the use to avoid
    // using registers for a long time.
    // however if we also need to perform ptr tag arithmetic it may make more sense to not
    // recalculate at every use site.
#ifndef ALLOCA_TAGGING
    IRB.SetInsertPoint(BasePointer->getNextNode());
#endif
    Value *Off = IRB.CreateGEP(Int8Ty, BasePointer, // BasePointer is i8*
                                     ConstantInt::get(Int32Ty, -Offset));
    Value *Replacement = IRB.CreateBitCast(Off, AI->getType(), Name);
#ifdef ALLOCA_TAGGING
    if(1){ // TEST: always take the calculation branch
        // first alloca iteration: can we assume its the first obj?
        // assert(Offset == SizeClass);

        // determine the span start by masking the alloca address down to 16MB alignment
        Value *AllocaPtr = IRB.CreatePtrToInt(Replacement, IntPtrTy);
#if 1
        if(SpanStart == nullptr)
#endif
        {
            SpanStart = dyn_cast<Instruction>(IRB.CreateAnd(AllocaPtr, STACK_SPAN_START_MASK));
        }

        // calculate the tag for this size class first alloca
        Value *Delta = IRB.CreateSub(AllocaPtr, SpanStart);
        Value *SizeClassInBits = IRB.getInt64((int)log2(SizeClass));
        Value *Jumps = IRB.CreateLShr(Delta, SizeClassInBits);
        Value *TagUnshifted = IRB.CreateAnd(Jumps, IRB.getInt64(15));
        Tag = dyn_cast<Instruction>(IRB.CreateShl(TagUnshifted, 56));
        first = false;
    }

#if 0
    else{
        // calculate the tag based on previous tag
        // since the stack is growing down, the tags also cycle down (tag--)
        Value *TagMinusOne = IRB.CreateSub(Tag, IRB.getInt64(TAG_OFFSET_ONE));
        Tag = dyn_cast<Instruction>(IRB.CreateAnd(TagMinusOne, IRB.getInt64(TAG_AND_15)));
    }
#endif

    //ConstantInt* Tag = ConstantInt::get(IRB.getInt64Ty(), 0x7);
    Value *AllocaInt = IRB.CreatePtrToInt(Replacement, IntPtrTy);
    Value *TaggedAlloca = IRB.CreateOr(AllocaInt, Tag);
    Value *TaggedPtr = IRB.CreateIntToPtr(TaggedAlloca, AI->getType());
    Replacement = TaggedPtr;

    // Type *intType = Type::getInt32Ty(F.getContext());
    // // Declare C standard library printf 
    // std::vector<Type *> printfArgsTypes({Type::getInt8PtrTy(F.getContext())});
    // FunctionType *printfType = FunctionType::get(intType, printfArgsTypes, true);
    // FunctionCallee printfFunc = F.getParent()->getOrInsertFunction("printf", printfType);

    // // The format string for the printf function, declared as a global literal
    // Value *str = IRB.CreateGlobalStringPtr("Addr %p Tag %d\n", "str");

    // std::vector<Value *> argsV({str, AllocaInt, Tag});
    // IRB.CreateCall(printfFunc, argsV, "calltmp");
 #endif

    AI->replaceAllUsesWith(Replacement);
#else
    while (!AI->use_empty()) {
      Use &U = *AI->use_begin();
      Instruction *User = cast<Instruction>(U.getUser());

      Instruction *InsertBefore;
      if (auto *PHI = dyn_cast<PHINode>(User))
        InsertBefore = PHI->getIncomingBlock(U)->getTerminator();
      else
        InsertBefore = User;

      IRBuilder<> IRBUser(InsertBefore);
      Value *Off = IRBUser.CreateGEP(Int8Ty, BasePointer, // BasePointer is i8*
                                     ConstantInt::get(Int32Ty, -Offset));
      Value *Replacement = IRBUser.CreateBitCast(Off, AI->getType(), Name);

      //errs() << "BasePointer " << *BasePointer << " Off " << *Off << "\n";

      // errs() << "Alloca " << *AI << " has Off: " << *Off << "\n";
      // errs() << "Alloca " << *AI << " has user: " << *User << "\n";

#ifdef ALLOCA_TAGGING
      // get span_start    
      // delta = alloca - span_start
      // jumps = delta >> num_bits_size_class
      // tag = jumps & 15
      // tag_shifted = tag << 56
      // tagged_alloca = alloca | tag_shifted

      // TODO: should avoid calculating the tag at every use, do it once, OR it, and then all uses use it
      // TODO: only calculate the tag for the first allocation, then cycle up
      // why does this code loop through the uses?
      // check https://github.com/llvm/llvm-project/issues/28218
      // and https://bugs.llvm.org/show_bug.cgi?id=27846

      // its to avoid many registers being used.
      // we can probably transform it to ReplaceAllUsesWith, and pay a penalty
      // we can benchmark both techniques, I suppose

      Value *AllocaPtr = IRBUser.CreatePtrToInt(Replacement, IntPtrTy);
      Value *Delta = IRBUser.CreateSub(AllocaPtr, SpanStart);
      Value *SizeClassInBits = IRBUser.getInt64((int)log2(SizeClass));
      Value *Jumps = IRBUser.CreateLShr(Delta, SizeClassInBits);
      Tag = IRBUser.CreateAnd(Jumps, IRBUser.getInt64(15));

      Value *TagShifted = IRBUser.CreateShl(Tag, 56);
      Value *AllocaInt = IRBUser.CreatePtrToInt(Replacement, IntPtrTy);
      Value *TaggedAlloca = IRBUser.CreateOr(AllocaInt, TagShifted);
      Value *TaggedPtr = IRBUser.CreateIntToPtr(TaggedAlloca, AI->getType());
      Replacement = TaggedPtr;
      // errs() << "Replacement is " << *Replacement << "\n";

      Type *intType = Type::getInt32Ty(F.getContext());
      // Declare C standard library printf 
      std::vector<Type *> printfArgsTypes({Type::getInt8PtrTy(F.getContext())});
      FunctionType *printfType = FunctionType::get(intType, printfArgsTypes, true);
      FunctionCallee printfFunc = F.getParent()->getOrInsertFunction("printf", printfType);

      // The format string for the printf function, declared as a global literal
      Value *str = IRBUser.CreateGlobalStringPtr("Addr %p Tag %d\n", "str");

      std::vector<Value *> argsV({str, AllocaInt, Tag});
      IRBUser.CreateCall(printfFunc, argsV, "calltmp");
 #endif

      if (auto *PHI = dyn_cast<PHINode>(User))
        // PHI nodes may have multiple incoming edges from the same BB (why??),
        // all must be updated at once with the same incoming value.
        PHI->setIncomingValueForBlock(PHI->getIncomingBlock(U), Replacement);
      else
        U.set(Replacement);
    }
#endif

    AI->eraseFromParent();
  }



  // Re-align BasePointer so that our callees would see it aligned as
  // expected.
  // FIXME: no need to update BasePointer in leaf functions.
  unsigned FrameSize = alignTo(SSL.getFrameSize(), StackAlignment);

  // The frame size must be a multiple of the size class to make the redzone
  // positions predictible, which is required for the slow path and for redzone
  // initialization on page fault.
  assert(SSL.getFrameSize() % SizeClass == 0);

  MDBuilder MDB(F.getContext());
  SmallVector<Metadata *, 2> Data;
  Data.push_back(MDB.createString("unsafe-stack-size"));
  Data.push_back(MDB.createConstant(ConstantInt::get(Int32Ty, FrameSize)));
  MDNode *MD = MDTuple::get(F.getContext(), Data);
  F.setMetadata(LLVMContext::MD_annotation, MD);

  // Update shadow stack pointer in the function epilogue.
  IRB.SetInsertPoint(BasePointer->getNextNode());

  Value *StaticTop =
      IRB.CreateGEP(Int8Ty, BasePointer, ConstantInt::get(Int32Ty, -FrameSize),
                    "unsafe_stack_static_top_" + StackID);
  IRB.CreateStore(StaticTop, UnsafeStackPtr);

  return StaticTop;
}


static void findReachableExits(BasicBlock *BB,
    SmallVectorImpl<Instruction*> &Exits,
    SmallPtrSetImpl<BasicBlock*> &Visited) {
  if (Visited.count(BB))
    return;
  Visited.insert(BB);

  if (ReturnInst *RI  = dyn_cast<ReturnInst>(BB->getTerminator())) {
    Exits.push_back(RI);
  } else {
    for (succ_iterator SI = succ_begin(BB), E = succ_end(BB); SI != E; ++SI)
      findReachableExits(*SI, Exits, Visited);
  }
}

template<unsigned N = 4>
static SmallVector<Instruction*, N> findReachableExits(Instruction *I) {
  SmallVector<Instruction*, N> Exits;
  SmallPtrSet<BasicBlock*, 8> Visited;
  findReachableExits(I->getParent(), Exits, Visited);
  return Exits;
}

static bool findDominancePathBetween(BasicBlock *A, BasicBlock *B,
                                     SmallVectorImpl<BasicBlock*> &Path,
                                     DominatorTree &DT, DominanceFrontier &DF) {
  if (DT.dominates(A, B))
    return true;

  for (BasicBlock *FB : DF.calculate(DT, DT.getNode(A))) {
    if (FB != A) {
      Path.push_back(FB);
      if (findDominancePathBetween(FB, B, Path, DT, DF))
        return true;
#if LLVM_VERSION_MAJOR > 7
      Path.pop_back();
#else
      Path.pop_back_val();
#endif
    }
  }

  return false;
}

template<unsigned N = 2>
static SmallVector<BasicBlock*, N> findDominancePathBetween(
                                      BasicBlock *A, BasicBlock *B,
                                      DominatorTree &DT, DominanceFrontier &DF) {
  SmallVector<BasicBlock*, N> Path;
  bool Success = findDominancePathBetween(A, B, Path, DT, DF);
  assert(Success);
  return Path;
}

static Instruction *makeDominating(Instruction *Alloc, Instruction *RI,
                                   DominatorTree &DT, DominanceFrontier &DF) {
  PointerType *Ty = cast<PointerType>(Alloc->getType());
  Instruction *Prev = Alloc;

  for (BasicBlock *BB : findDominancePathBetween(Alloc->getParent(), RI->getParent(), DT, DF)) {
    PHINode *PN = PHINode::Create(Ty, 2, Alloc->getName() + ".prop", BB->getFirstNonPHI());
    for (pred_iterator PI = pred_begin(BB), E = pred_end(BB); PI != E; ++PI) {
      BasicBlock *Pred = *PI;
      if (DT.dominates(Prev->getParent(), Pred))
        PN->addIncoming(Prev, Pred);
      else
        PN->addIncoming(ConstantPointerNull::get(Ty), Pred);
    }
    Prev = PN;
  }

  assert(DT.dominates(Prev, RI));
  return Prev;
}


void SafeStack::moveDynamicAllocasToHeap(Function &F, ArrayRef<AllocaInst*> DynamicAllocas) {
  DIBuilder DIB(*F.getParent());
  IRBuilder<> IRB(F.getContext());

  for (AllocaInst *AI : DynamicAllocas) {
    LLVM_DEBUG(dbgs() << "[SizedStack] Move dynamic alloca to heap:" << *AI << "\n");
    IRB.SetInsertPoint(AI);

    // Compute allocation size in bytes
    Value *Size = AI->getArraySize();
    if (Size->getType() != IntPtrTy)
      Size = IRB.CreateIntCast(Size, IntPtrTy, false);
    uint64_t TySize = DL.getTypeAllocSize(AI->getAllocatedType());
    if (TySize != 1)
      Size = IRB.CreateMul(Size, ConstantInt::get(IntPtrTy, TySize));

    // Replace alloca with call to heap allocation helper in runtime
    Value *Align = ConstantInt::get(IntPtrTy, AI->getAlign().value());
    Instruction *HeapAlloc = IRB.CreateCall(RT.DynAllocFunc, {Size, Align});
    Value *Replacement = HeapAlloc;
    if (Replacement->getType() != AI->getType())
      Replacement = IRB.CreatePointerCast(Replacement, AI->getType());
    Replacement->takeName(AI);
    replaceDbgDeclare(AI, Replacement, DIB, DIExpression::ApplyOffset, 0);

    AI->replaceAllUsesWith(Replacement);
    AI->eraseFromParent();

    // We always want to free the allocation if the return is dominated by the
    // allocation. If the return is not dominated, but is reachable, we insert a
    // PHI(alloc, NULL) node at the dominance frontier leading to the return,
    // and pass that to the free function (which must do a NULL check that
    // should be optimized away for non-phi pointers).
    for (Instruction *RI : findReachableExits(HeapAlloc)) {
      Instruction *FreedPointer = makeDominating(HeapAlloc, RI, DT, DF);
      Function *Helper = FreedPointer == HeapAlloc ? RT.DynFreeFunc : RT.DynFreeOptFunc;
      IRB.SetInsertPoint(RI);
      IRB.CreateCall(Helper, {FreedPointer});
    }

    ++NumDynAllocasMovedToHeap;
  }
}

void SafeStack::moveDynamicAllocasToUnsafeStack(
    Function &F, Value *UnsafeStackPtr, AllocaInst *DynamicTop,
    ArrayRef<AllocaInst *> DynamicAllocas) {
  DIBuilder DIB(*F.getParent());

  for (AllocaInst *AI : DynamicAllocas) {
    IRBuilder<> IRB(AI);

    // Compute the new SP value (after AI).
    Value *ArraySize = AI->getArraySize();
    if (ArraySize->getType() != IntPtrTy)
      ArraySize = IRB.CreateIntCast(ArraySize, IntPtrTy, false);

    Type *Ty = AI->getAllocatedType();
    uint64_t TySize = DL.getTypeAllocSize(Ty);
    Value *Size = IRB.CreateMul(ArraySize, ConstantInt::get(IntPtrTy, TySize));

    Value *SP = IRB.CreatePtrToInt(IRB.CreateLoad(StackPtrTy, UnsafeStackPtr),
                                   IntPtrTy);
    SP = IRB.CreateSub(SP, Size);

    // Align the SP value to satisfy the AllocaInst, type and stack alignments.
    auto Align = std::max(std::max(DL.getPrefTypeAlign(Ty), AI->getAlign()),
                          StackAlignment);

    Value *NewTop = IRB.CreateIntToPtr(
        IRB.CreateAnd(SP,
                      ConstantInt::get(IntPtrTy, ~uint64_t(Align.value() - 1))),
        StackPtrTy);

    // Save the stack pointer.
    IRB.CreateStore(NewTop, UnsafeStackPtr);
    if (DynamicTop)
      IRB.CreateStore(NewTop, DynamicTop);

    Value *NewAI = IRB.CreatePointerCast(NewTop, AI->getType());
    if (AI->hasName() && isa<Instruction>(NewAI))
      NewAI->takeName(AI);

    replaceDbgDeclare(AI, NewAI, DIB, DIExpression::ApplyOffset, 0);
    AI->replaceAllUsesWith(NewAI);
    AI->eraseFromParent();
  }

  if (!DynamicAllocas.empty()) {
    // Now go through the instructions again, replacing stacksave/stackrestore.
    for (Instruction &I : llvm::make_early_inc_range(instructions(&F))) {
      auto *II = dyn_cast<IntrinsicInst>(&I);
      if (!II)
        continue;

      if (II->getIntrinsicID() == Intrinsic::stacksave) {
        IRBuilder<> IRB(II);
        Instruction *LI = IRB.CreateLoad(StackPtrTy, UnsafeStackPtr);
        LI->takeName(II);
        II->replaceAllUsesWith(LI);
        II->eraseFromParent();
      } else if (II->getIntrinsicID() == Intrinsic::stackrestore) {
        IRBuilder<> IRB(II);
        Instruction *SI = IRB.CreateStore(II->getArgOperand(0), UnsafeStackPtr);
        SI->takeName(II);
        assert(II->use_empty());
        II->eraseFromParent();
      }
    }
  }
}

bool SafeStack::ShouldInlinePointerAddress(CallInst &CI) {
  Function *Callee = CI.getCalledFunction();
  if (CI.hasFnAttr(Attribute::AlwaysInline) &&
      isInlineViable(*Callee).isSuccess())
    return true;
  if (Callee->isInterposable() || Callee->hasFnAttribute(Attribute::NoInline) ||
      CI.isNoInline())
    return false;
  return true;
}

void SafeStack::TryInlinePointerAddress() {
  auto *CI = dyn_cast<CallInst>(UnsafeStackPtr);
  if (!CI)
    return;

  if(F.hasOptNone())
    return;

  Function *Callee = CI->getCalledFunction();
  if (!Callee || Callee->isDeclaration())
    return;

  if (!ShouldInlinePointerAddress(*CI))
    return;

  InlineFunctionInfo IFI;
  InlineFunction(*CI, IFI);
}

bool SafeStack::run() {
  assert(F.hasFnAttribute(Attribute::SafeStack) &&
         "Can't run SafeStack on a function without the attribute");
  assert(!F.isDeclaration() && "Can't run SafeStack on a function declaration");

  // AttrBuilder AB(F.getParent()->getContext());
  // AB.addAttribute(Attribute::StackProtect);
  // AB.addAttribute(Attribute::StackProtectReq);
  // AB.addAttribute(Attribute::StackProtectStrong);
  // F.removeAttributes(AttributeList::FunctionIndex, AB);

  ++NumFunctions;

  SmallVector<AllocaInst *, 16> StaticAllocas;
  SmallVector<AllocaInst *, 4> DynamicAllocas;
  SmallVector<Argument *, 4> ByValArguments;
  SmallVector<Instruction *, 4> Returns;

  // Collect all points where stack gets unwound and needs to be restored
  // This is only necessary because the runtime (setjmp and unwind code) is
  // not aware of the unsafe stack and won't unwind/restore it properly.
  // To work around this problem without changing the runtime, we insert
  // instrumentation to restore the unsafe stack pointer when necessary.
  SmallVector<Instruction *, 4> StackRestorePoints;

  // Find all static and dynamic alloca instructions that must be moved to the
  // unsafe stack, all return instructions and stack restore points.
  // F.dump();
  findInsts(F, StaticAllocas, DynamicAllocas, ByValArguments, Returns,
            StackRestorePoints);

  if (StaticAllocas.empty() && DynamicAllocas.empty() &&
      ByValArguments.empty() && StackRestorePoints.empty())
    return false; // Nothing to do in this function.

  if (!StaticAllocas.empty() || !DynamicAllocas.empty() ||
      !ByValArguments.empty())
    ++NumUnsafeStackFunctions; // This function has the unsafe stack.

  if (!StackRestorePoints.empty())
    ++NumUnsafeStackRestorePointsFunctions;

  IRBuilder<> IRB(&F.front(), F.begin()->getFirstInsertionPt());
  // Calls must always have a debug location, or else inlining breaks. So
  // we explicitly set a artificial debug location here.
  if (DISubprogram *SP = F.getSubprogram())
    IRB.SetCurrentDebugLocation(
        DILocation::get(SP->getContext(), SP->getScopeLine(), 0, SP));
  if (SafeStackUsePointerAddress) {
    FunctionCallee Fn = F.getParent()->getOrInsertFunction(
        "__safestack_pointer_address", StackPtrTy->getPointerTo(0));
    UnsafeStackPtr = IRB.CreateCall(Fn);
  } else {
    UnsafeStackPtr = TL.getSafeStackPointerLocation(IRB);
  }

  AllocaInst *StackGuardSlot = nullptr;
  // // FIXME: implement weaker forms of stack protector.
  // if (F.hasFnAttribute(Attribute::StackProtect) ||
  //     F.hasFnAttribute(Attribute::StackProtectStrong) ||
  //     F.hasFnAttribute(Attribute::StackProtectReq)) {
  //   Value *StackGuard = getStackGuard(IRB, F);
  //   StackGuardSlot = IRB.CreateAlloca(StackPtrTy, nullptr);
  //   IRB.CreateStore(StackGuard, StackGuardSlot);

  //   for (Instruction *RI : Returns) {
  //     IRBuilder<> IRBRet(RI);
  //     checkStackGuard(IRBRet, F, *RI, StackGuardSlot, StackGuard);
  //   }
  // }

  // Handle dynamic allocas.
  // moveDynamicAllocasToUnsafeStack(F, UnsafeStackPtr, DynamicTop,
  //                                 DynamicAllocas);
  moveDynamicAllocasToHeap(F, DynamicAllocas);
  if (OptOnlyNoDynAllocas)
    return !DynamicAllocas.empty();

  // Don't treat dynamic allocas again below since they are now removed
  DynamicAllocas.clear();

  // Divide allocas into sized stacks.
  struct StackInfo {
    SmallVector<AllocaInst *, 8> StaticAllocas;
    SmallVector<Argument *, 2> ByValArguments;
  };
  StringMap<StackInfo> UnsafeStacks;
  for (AllocaInst *AI : StaticAllocas){
    // errs() << "Unsafe Alloca: " << *AI << "\n";
    UnsafeStacks[RT.getStackID(*AI)].StaticAllocas.push_back(AI);
  }
  for (Argument *Arg : ByValArguments){
    // errs() << "Testing: ByValArgument: " << *Arg << "\n";
    UnsafeStacks[RT.getStackID(*Arg)].ByValArguments.push_back(Arg);
  }

  // Create a base pointer for each sized stack and transform allocas.
  // IRBuilder<> IRB(F.getContext());
  for (auto &it : UnsafeStacks) {
    StringRef StackID = it.getKey();
    const struct StackInfo &Stack = it.getValue();

    // Reset IRBuilder to function entry point.
    IRB.SetInsertPoint(&F.front(), F.begin()->getFirstInsertionPt());


    // Get the pointer to the unsafe stack.
    Value *UnsafeStackPtr = RT.getOrCreateUnsafeStackPtr(IRB, F, StackID);

    // Load the current stack pointer (we'll also use it as a base pointer).
    // FIXME: use a dedicated register for it?
    Instruction *BasePointer =
        IRB.CreateLoad(StackPtrTy, UnsafeStackPtr, false, "unsafe_stack_ptr_" + StackID);

    assert(BasePointer->getType() == StackPtrTy);

    // The top of the unsafe stack after all unsafe static allocas are
    // allocated.
    Value *StaticTop =
        moveStaticAllocasToUnsafeStack(IRB, F, Stack.StaticAllocas, Stack.ByValArguments,
                                       BasePointer, StackGuardSlot,
                                       UnsafeStackPtr, StackID);

    // Safe stack object that stores the current unsafe stack top. It is updated
    // as unsafe dynamic (non-constant-sized) allocas are allocated and freed.
    // This is only needed if we need to restore stack pointer after longjmp
    // or exceptions, and we have dynamic allocations.
    // FIXME: a better alternative might be to store the unsafe stack pointer
    // before setjmp / invoke instructions.
    createStackRestorePoints(
        IRB, F, StackRestorePoints, StaticTop, false,
        UnsafeStackPtr, StackID);

    // Restore the unsafe stack pointer before each return.
    for (Instruction *RI : Returns) {

      IRB.SetInsertPoint(RI);
      IRB.CreateStore(BasePointer, UnsafeStackPtr);
    }
  }

  if (UnsafeStacks.size() > NumUnsafeStacksPerFunction)
    NumUnsafeStacksPerFunction = UnsafeStacks.size();

  // TryInlinePointerAddress();

  //errs() << "[SizedStack] sizedstack applied to " << F.getName()
  //                  << " with " << UnsafeStacks.size() << " unsafe stacks\n";

  LLVM_DEBUG(dbgs() << "[SafeStack]     safestack applied\n");
  return true;
}

static void replaceUsesWithCast(Value *What, Value *With) {
  if (isa<Constant>(What)) {
    Constant *WithC = cast<Constant>(With);
    if (With->getType() != What->getType())
      With = ConstantExpr::getBitCast(WithC, What->getType());
  }
  What->replaceAllUsesWith(With);
}


bool SizedStackRuntime::initialize() {
  Type *VoidTy = Type::getVoidTy(M.getContext());
  FunctionType *FnTy;

  if (OptStackShadowMem) {
    Type *BoolTy = Type::getInt1Ty(M.getContext());
    FnTy = FunctionType::get(VoidTy, {IntPtrTy, Int64Ty, BoolTy}, false);
    ShadowMemPoisonFunc = getOrInsertNoInstrumentFunction(M, "shadowmem_poison", FnTy);
  }

  FnTy = FunctionType::get(StackPtrTy, {IntPtrTy, IntPtrTy}, false);
  DynAllocFunc = getOrInsertNoInstrumentFunction(M, "dyn_alloc", FnTy);

  FnTy = FunctionType::get(VoidTy, {StackPtrTy}, false);
  DynFreeFunc = getOrInsertNoInstrumentFunction(M, "dyn_free", FnTy);
  DynFreeOptFunc = getOrInsertNoInstrumentFunction(M, "dyn_free_optional", FnTy);

  if (OptOnlyNoDynAllocas)
    return true;

  // Create a temporary stack pointer array as we do not know the size yet.
  stackPointerArray = createStackPtrArray(kUnsafeStackPtrVarTemp, 0);
  typeIndexNext = 0;

  return true;
}

bool SizedStackRuntime::finalize() {
  if (OptOnlyNoDynAllocas)
    return false;

  // Replace temporary stack pointer array with a properly sized one.
  GlobalVariable *stackPointerArrayFinal = createStackPtrArray(kUnsafeStackPtrVarFinal, typeIndexNext);
  replaceUsesWithCast(stackPointerArray, stackPointerArrayFinal);
  stackPointerArray->eraseFromParent();
  stackPointerArray = nullptr;
  // Replace static library stack pointer array with the newly allocated one.

  GlobalVariable *stackPointerArrayStatic = dyn_cast_or_null<GlobalVariable>(M.getNamedValue(kUnsafeStackPtrVar));

  assert(stackPointerArrayStatic);
  replaceUsesWithCast(stackPointerArrayStatic, stackPointerArrayFinal);
  stackPointerArrayStatic->eraseFromParent();

  // Replace static library size class array with a properly sized and initialized one.
  // The array might not exist; it gets optimized out when DISABLE_SLOWPATH is
  // set in the static library
  GlobalVariable *sizeClassArrayStatic = dyn_cast_or_null<GlobalVariable>(M.getNamedValue(kUnsafeStackSizeClassesVar));
  if (sizeClassArrayStatic) {
    GlobalVariable *sizeClassArrayFinal = createSizeClassArray(kUnsafeStackSizeClassesVarFinal);
    replaceUsesWithCast(sizeClassArrayStatic, sizeClassArrayFinal);
    sizeClassArrayStatic->eraseFromParent();
  }

  // Provide stack pointer count and assigned size classes to static library.
  createStackPtrCount(kUnsafeStackPtrCountVar, typeIndexNext);

  return true;
}

size_t SizedStackRuntime::getTypeIndex(StringRef typeId) {
  auto typeIndexIt = typeIndexByTypeId.find(typeId);
  size_t typeIndex;

  // Find size class in type id.
  uint64_t SizeClass = 0;
  int idx = typeId.rfind('_');
  if (idx >= 0)
    SizeClass = std::stoll(typeId.substr(idx + 1).str());

  if (typeIndexIt == typeIndexByTypeId.end()) {
    typeIndex = typeIndexNext++;
    LLVM_DEBUG(dbgs() << "[SizedStack] getTypeIndex typeId=" << typeId <<
               " sizeclass=" << SizeClass << " typeIndex=" << typeIndex << "\n");
    typeIndexByTypeId[typeId] = typeIndex;
    assert(AssignedSizeClasses.size() == typeIndex);
    AssignedSizeClasses.push_back(SizeClass);
    ++NumUnsafeStacks;
  } else {
    typeIndex = typeIndexIt->second;
    assert(AssignedSizeClasses[typeIndex] == SizeClass);
  }

  return typeIndex;
}

Value *SizedStackRuntime::getOrCreateUnsafeStackPtr(IRBuilder<> &IRB, Function &F, StringRef typeId) {
  size_t typeIndex = getTypeIndex(typeId);
  return IRB.CreateInBoundsGEP(cursedType, stackPointerArray, {IRB.getInt32(0), IRB.getInt32(typeIndex)});
}

GlobalVariable *SizedStackRuntime::createStackPtrArray(StringRef varName, size_t count) {
  // We need an array of count stack pointers.
  ArrayType *type = ArrayType::get(StackPtrTy, count);
  cursedType = type;
  LLVM_DEBUG(dbgs() << "[SizedStack] create stack pointer array " << varName << " count=" << count << "\n");

  // Initialize every stack pointer to NULL.
  Constant *initElement = ConstantPointerNull::get(StackPtrTy);
  SmallVector<Constant*, 16> initElements;
  for (size_t i = 0; i < count; ++i)
    initElements.push_back(initElement);
  Constant *init = ConstantArray::get(type, initElements);

  // Create the global var.
  return new GlobalVariable(
      /*Module=*/M,
      /*Type=*/type,
      /*isConstant=*/false,
      /*Linkage=*/GlobalValue::PrivateLinkage,
      /*Initializer=*/init,
      /*Name=*/varName,
      /*InsertBefore=*/nullptr,
      /*ThreadLocalMode=*/GlobalValue::InitialExecTLSModel);
      // TODO try this, should work for LTO: /*ThreadLocalMode=*/GlobalValue::LocalExecTLSModel);
}

GlobalVariable *SizedStackRuntime::createStackSpansArray(StringRef varName, size_t count) {
  // We need an array of count stack pointers.
  ArrayType *type = ArrayType::get(StackPtrTy, count);
  cursedType = type;

  // Initialize every stack pointer to NULL.
  Constant *initElement = ConstantPointerNull::get(StackPtrTy);
  SmallVector<Constant*, 16> initElements;
  for (size_t i = 0; i < count; ++i)
    initElements.push_back(initElement);
  Constant *init = ConstantArray::get(type, initElements);

  // Create the global var.
  return new GlobalVariable(
      /*Module=*/M,
      /*Type=*/type,
      /*isConstant=*/false,
      /*Linkage=*/GlobalValue::PrivateLinkage,
      /*Initializer=*/init,
      /*Name=*/varName,
      /*InsertBefore=*/nullptr,
      /*ThreadLocalMode=*/GlobalValue::InitialExecTLSModel);
      // TODO try this, should work for LTO: /*ThreadLocalMode=*/GlobalValue::LocalExecTLSModel);
}

GlobalVariable *SizedStackRuntime::createStackPtrCount(StringRef varName, size_t count) {
  GlobalVariable *gv = cast<GlobalVariable>(M.getNamedValue(varName));
  IntegerType *type = IntegerType::get(M.getContext(), 64);
  Constant *init = ConstantInt::get(type, count);
  gv->setInitializer(init);
  gv->setConstant(true);
  gv->setLinkage(GlobalValue::PrivateLinkage);
  return gv;
}

GlobalVariable *SizedStackRuntime::createSizeClassArray(StringRef varName) {
  ArrayType *type = ArrayType::get(Int64Ty, AssignedSizeClasses.size());

  SmallVector<Constant*, 16> initElements;
  for (uint64_t SC : AssignedSizeClasses)
    initElements.push_back(ConstantInt::get(Int64Ty, SC));
  Constant *init = ConstantArray::get(type, initElements);

  return new GlobalVariable(
      /*Module=*/M,
      /*Type=*/type,
      /*isConstant=*/true,
      /*Linkage=*/GlobalValue::PrivateLinkage,
      /*Initializer=*/init,
      /*Name=*/varName,
      /*InsertBefore=*/nullptr,
      /*ThreadLocalMode=*/GlobalValue::InitialExecTLSModel);
}

uint64_t SizedStackRuntime::roundUpToSizeClass(uint64_t Size) {
  uint64_t Rounded = 0;
  for (const uint64_t SC : kSizeClasses) {
    if (Size <= SC) {
      Rounded = SC;
      break;
    }
  }
  if (Rounded == 0) {
    assert(Size + OptRedzoneSize <= kDefaultUnsafeStackSize);
    for (Rounded = Size; Rounded % StackAlignment; ++Rounded);
    assert(Rounded % StackAlignment == 0);
    LLVM_DEBUG(dbgs() << "[SizedStack] creating new size class " << Rounded
                      << " for " << Size << "-byte allocation\n");
  }
  return Rounded;
}

std::string SizedStackRuntime::getStaticStackID(uint64_t Size, const Value &V) {
  uint64_t PaddedSize = roundUpToSizeClass(Size + OptRedzoneSize);
  assert(PaddedSize > 0);
  std::string id;
  raw_string_ostream ss(id);
  ss << "static_" << PaddedSize;
  return id;
}

uint64_t SizedStackRuntime::getStaticAllocaAllocationSize(const AllocaInst* AI) {
  uint64_t Size = DL.getTypeAllocSize(AI->getAllocatedType());
  if (AI->isArrayAllocation()) {
    auto C = dyn_cast<ConstantInt>(AI->getArraySize());
    if (!C)
      return 0;
    Size *= C->getZExtValue();
  }
  return Size;
}

std::string SizedStackRuntime::getStackID(const AllocaInst &AI) {
  assert(AI.isStaticAlloca());
  return getStaticStackID(getStaticAllocaAllocationSize(&AI), AI);
}

std::string SizedStackRuntime::getStackID(const Argument &Arg) {
  Type *Ty = Arg.getType()->getPointerElementType();
  return getStaticStackID(DL.getTypeStoreSize(Ty), Arg);
}

class SafeStackLegacyPass : public ModulePass {
  const TargetMachine *TM = nullptr;

public:
  static char ID; // Pass identification, replacement for typeid..

  SafeStackLegacyPass() : ModulePass(ID) {
    initializeSafeStackLegacyPassPass(*PassRegistry::getPassRegistry());
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<TargetPassConfig>();
    AU.addRequired<TargetLibraryInfoWrapperPass>();
    AU.addRequired<AssumptionCacheTracker>();
    AU.addPreserved<DominatorTreeWrapperPass>();
  }

  bool runOnFunction(Function &F, SizedStackRuntime &RT) {
    LLVM_DEBUG(dbgs() << "[SafeStack] Function: " << F.getName() << "\n");

    if (!F.hasFnAttribute(Attribute::SafeStack)) {
      LLVM_DEBUG(dbgs() << "[SafeStack]     safestack is not requested"
                           " for this function\n");
      return false;
    }

    if (F.isDeclaration()) {
      LLVM_DEBUG(dbgs() << "[SafeStack]     function definition"
                           " is not available\n");
      return false;
    }

    TM = &getAnalysis<TargetPassConfig>().getTM<TargetMachine>();
    auto *TL = TM->getSubtargetImpl(F)->getTargetLowering();
    if (!TL)
      report_fatal_error("TargetLowering instance is required");

    auto *DL = &F.getParent()->getDataLayout();
    auto &TLI = getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(F);
    auto &ACT = getAnalysis<AssumptionCacheTracker>().getAssumptionCache(F);

    // Compute DT and LI only for functions that have the attribute.
    // This is only useful because the legacy pass manager doesn't let us
    // compute analyzes lazily.

    DominatorTree *DT;
    bool ShouldPreserveDominatorTree;
    std::optional<DominatorTree> LazilyComputedDomTree;

    // Do we already have a DominatorTree avaliable from the previous pass?
    // Note that we should *NOT* require it, to avoid the case where we end up
    // not needing it, but the legacy PM would have computed it for us anyways.
    if (auto *DTWP = getAnalysisIfAvailable<DominatorTreeWrapperPass>()) {
      DT = &DTWP->getDomTree();
      ShouldPreserveDominatorTree = true;
    } else {
      // Otherwise, we need to compute it.
      LazilyComputedDomTree.emplace(F);
      DT = &*LazilyComputedDomTree;
      ShouldPreserveDominatorTree = false;
    }

    // Likewise, lazily compute loop info.
    LoopInfo LI(*DT);

    DomTreeUpdater DTU(DT, DomTreeUpdater::UpdateStrategy::Lazy);

    ScalarEvolution SE(F, TLI, ACT, *DT, LI);

    DominanceFrontier DF;
    DF.analyze(*DT);

    return SafeStack(F, *TL, *DL, ShouldPreserveDominatorTree ? &DTU : nullptr, SE, *DT, DF, RT).run();
  }

  bool runOnModule(Module &M) override {
#ifndef USE_GOLD_PASSES
    if (!ClSizedStack) return false;
#endif

    bool isSafeStack = false;
    for (Function &F : M) {
      if (F.hasFnAttribute(Attribute::SafeStack)) {
          isSafeStack = true;
      }
    }

    if(!isSafeStack){
      return false;
    }

    SizedStackRuntime RT(M);
    bool Changed = RT.initialize();

    for (Function &F : M) {
      if (shouldInstrument(F))
        Changed |= runOnFunction(F, RT);
    }
#if 0
    FILE* fp = fopen("/tmp/safe_stack_sizes.txt", "a");
    std::string CurrWorkPath = std::getenv("PWD");
    std::string FullFilename = CurrWorkPath + "/" + M.getSourceFileName();
    fprintf(fp, "%s %lu %lu\n", FullFilename.c_str(), NumUnsafeStacks.getValue(), NumUnsafeStacksPerFunction.getValue());
    //errs() << "[SizedSafeStack analysis]: " << FullFilename << "\n" << NumUnsafeStacks << " " << NumUnsafeStacksPerFunction << "\n";
    fflush(fp);
    fclose(fp);
#endif

    Changed |= RT.finalize();
    return Changed;
  }
};

} // end anonymous namespace

char SafeStackLegacyPass::ID = 0;

INITIALIZE_PASS_BEGIN(SafeStackLegacyPass, DEBUG_TYPE,
                      "Safe Stack instrumentation pass", false, false)
INITIALIZE_PASS_DEPENDENCY(TargetPassConfig)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_END(SafeStackLegacyPass, DEBUG_TYPE,
                    "Safe Stack instrumentation pass", false, false)

ModulePass *llvm::createSafeStackPass() { return new SafeStackLegacyPass(); }
