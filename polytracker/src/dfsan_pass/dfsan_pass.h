/*
 * dfsan_pass.h
 *
 *  Created on: Jul 24, 2020
 *      Author: carson
 */
//TODO Move to includes

#ifndef POLYTRACKER_SRC_DFSAN_PASS_DFSAN_PASS_H_
#define POLYTRACKER_SRC_DFSAN_PASS_DFSAN_PASS_H_

#include <llvm/Config/llvm-config.h>
#include <llvm/IR/IRBuilder.h>

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/None.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/Triple.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Transforms/Utils/Local.h"
// For out of source registration
#include "llvm/IR/LegacyPassManager.h"

#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/User.h"
#include "llvm/IR/Value.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/SpecialCaseList.h"
// For out of source registration
#include "dfsan/dfsan_types.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Instrumentation.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <algorithm>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <iostream>
#include <iterator>
#include <memory>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "dfsan_pass_util.h"

using namespace llvm;


static StringRef GetGlobalTypeString(const GlobalValue &G) {
  // Types of GlobalVariables are always pointer types.
  Type *GType = G.getValueType();
  // For now we support blacklisting struct types only.
  if (StructType *SGType = dyn_cast<StructType>(GType)) {
    if (!SGType->isLiteral())
      return SGType->getName();
  }
  return "<unknown type>";
}


/*
 * This is a class used to handle the ABI lists which decide which functions to intercept/ignore etc
 */
class DFSanABIList {
  std::unique_ptr<SpecialCaseList> SCL;

public:
  DFSanABIList() = default;

  void set(std::unique_ptr<SpecialCaseList> List) { SCL = std::move(List); }

  /// Returns whether either this function or its source file are listed in the
  /// given category.
  bool isIn(const Function &F, StringRef Category) const {
    return isIn(*F.getParent(), Category) ||
           SCL->inSection("dataflow", "fun", F.getName(), Category);
  }

  /// Returns whether this global alias is listed in the given category.
  ///
  /// If GA aliases a function, the alias's name is matched as a function name
  /// would be.  Similarly, aliases of globals are matched like globals.
  bool isIn(const GlobalAlias &GA, StringRef Category) const {
    if (isIn(*GA.getParent(), Category))
      return true;

    if (isa<FunctionType>(GA.getValueType()))
      return SCL->inSection("dataflow", "fun", GA.getName(), Category);

    return SCL->inSection("dataflow", "global", GA.getName(), Category) ||
           SCL->inSection("dataflow", "type", GetGlobalTypeString(GA),
                          Category);
  }

  /// Returns whether this module is listed in the given category.
  bool isIn(const Module &M, StringRef Category) const {
    return SCL->inSection("dataflow", "src", M.getModuleIdentifier(), Category);
  }
};


/// TransformedFunction is used to express the result of transforming one
/// function type into another.  This struct is immutable.  It holds metadata
/// useful for updating calls of the old function to the new type.
struct TransformedFunction {
  TransformedFunction(FunctionType *OriginalType, FunctionType *TransformedType,
                      std::vector<unsigned> ArgumentIndexMapping)
      : OriginalType(OriginalType), TransformedType(TransformedType),
        ArgumentIndexMapping(ArgumentIndexMapping) {}

  // Disallow copies.
  TransformedFunction(const TransformedFunction &) = delete;
  TransformedFunction &operator=(const TransformedFunction &) = delete;

  // Allow moves.
  TransformedFunction(TransformedFunction &&) = default;
  TransformedFunction &operator=(TransformedFunction &&) = default;

  /// Type of the function before the transformation.
  FunctionType *const OriginalType;

  /// Type of the function after the transformation.
  FunctionType *const TransformedType;

  /// Transforming a function may change the position of arguments.  This
  /// member records the mapping from each argument's old position to its new
  /// position.  Argument positions are zero-indexed.  If the transformation
  /// from F to F' made the first argument of F into the third argument of F',
  /// then ArgumentIndexMapping[0] will equal 2.
  const std::vector<unsigned> ArgumentIndexMapping;
};


/*
 * This is the main module pass for dfsan that triggers everything
 * In this class definition there are a bunch of important variables
 *
 * ShadowWidth: this determines the integer size of shadow values. This is important because
 * the dfsan runtime sets up an mmap'd arena to represent shadow memory. If for whatever reason
 * the ShadowWidth in the pass and the runtime get out of sync everything breaks. This is why we define
 * the length of the label in dfsan/types.h so they can share it. Originally this was not the case,
 * and originally it was a 16bit maximum which we found to be very limiting. So we upped it to 32.
 * if you are going to mess with the size, make sure you update the address calculations in the runtime, see dfsan_platform.h i believe
 *
 * WrapperKind: Our fork of DFSan still uses these "abi lists" which specify if you should replace a function with a custom implementation or ignore it
 * If there are conflicts within or between ABI lists there is a conflict resolution function. Originally the ranking was discard above all else, we found
 * that to be super annoying so we make it so custom > functional > discard > warning is the new ranking. You might thank us later for that
 *
 * All the different functions and variables are there next, this is just standard LLVM stuff.
 */
class DataFlowSanitizer : public ModulePass {
  friend struct DFSanFunction;
  friend class DFSanVisitor;


  enum { ShadowWidth = DFSAN_LABEL_BITS };

  /// Which ABI should be used for instrumented functions?
  enum InstrumentedABI {
    /// Argument and return value labels are passed through additional
    /// arguments and by modifying the return type.
    IA_Args,

    /// Argument and return value labels are passed through TLS variables
    /// __dfsan_arg_tls and __dfsan_retval_tls.
    IA_TLS
  };

  /// How should calls to uninstrumented functions be handled?
  enum WrapperKind {
    /// This function is present in an uninstrumented form but we don't know
    /// how it should be handled.  Print a warning and call the function anyway.
    /// Don't label the return value.
    WK_Warning,

    /// This function does not write to (user-accessible) memory, and its return
    /// value is unlabelled.
    WK_Discard,

    /// This function does not write to (user-accessible) memory, and the label
    /// of its return value is the union of the label of its arguments.
    WK_Functional,

    /// Instead of calling the function, a custom wrapper __dfsw_F is called,
    /// where F is the name of the function.  This function may wrap the
    /// original function or provide its own implementation.  This is similar to
    /// the IA_Args ABI, except that IA_Args uses a struct return type to
    /// pass the return value shadow in a register, while WK_Custom uses an
    /// extra pointer argument to return the shadow.  This allows the wrapped
    /// form of the function type to be expressed in C.
    WK_Custom
  };

  Module *Mod;
  LLVMContext *Ctx;
  IntegerType *ShadowTy;
  PointerType *ShadowPtrTy;
  IntegerType *IntptrTy;
  ConstantInt *ZeroShadow;
  ConstantInt *ShadowPtrMask;
  ConstantInt *ShadowPtrMul;
  Constant *ArgTLS;
  Constant *RetvalTLS;
  void *(*GetArgTLSPtr)();
  void *(*GetRetvalTLSPtr)();
  Constant *GetArgTLS;
  Constant *GetRetvalTLS;
  Constant *ExternalShadowMask;
  FunctionType *DFSanUnionFnTy;
  FunctionType *DFSanUnionLoadFnTy;
  FunctionType *DFSanUnimplementedFnTy;
  FunctionType *DFSanSetLabelFnTy;
  FunctionType *DFSanNonzeroLabelFnTy;
  FunctionType *DFSanVarargWrapperFnTy;

  // General for all taint
  FunctionType *DFSanLogTaintFnTy;
  Constant *DFSanLogTaintFn;

  // Function to log cmps
  FunctionType *DFSanLogCmpFnTy;
  Constant *DFSanLogCmpFn;

  FunctionType *DFSanLogInstFnTy;
  Constant *DFSanLogInstFn;

  FunctionType *DFSanEntryFnTy;
  FunctionType *DFSanExitFnTy;
  FunctionType *DFSanEntryBBFnTy;
  FunctionType *DFSanExitBBFnTy;

  FunctionType *DFSanResetFrameFnTy;
  Constant *DFSanEntryFn;
  Constant *DFSanEntryBBFn;
  Constant *DFSanExitFn;
  Constant *DFSanExitBBFn;
  Constant *DFSanResetFrameFn;

  Constant *DFSanUnionFn;
  Constant *DFSanCheckedUnionFn;
  Constant *DFSanUnionLoadFn;
  Constant *DFSanUnimplementedFn;
  Constant *DFSanSetLabelFn;
  Constant *DFSanNonzeroLabelFn;
  Constant *DFSanVarargWrapperFn;
  MDNode *ColdCallWeights;
  DFSanABIList ABIList;
  DenseMap<Value *, Function *> UnwrappedFnMap;
  AttrBuilder ReadOnlyNoneAttrs;
  bool DFSanRuntimeShadowMask = false;

  Value *getShadowAddress(Value *Addr, Instruction *Pos);
  bool isInstrumented(const Function *F);
  bool isInstrumented(const GlobalAlias *GA);
  FunctionType *getArgsFunctionType(FunctionType *T);
  FunctionType *getTrampolineFunctionType(FunctionType *T);
  TransformedFunction getCustomFunctionType(FunctionType *T);
  InstrumentedABI getInstrumentedABI();
  WrapperKind getWrapperKind(Function *F);
  void addGlobalNamePrefix(GlobalValue *GV);
  Function *buildWrapperFunction(Function *F, StringRef NewFName,
                                 GlobalValue::LinkageTypes NewFLink,
                                 FunctionType *NewFT);
  Constant *getOrBuildTrampolineFunction(FunctionType *FT, StringRef FName);

public:
  static char ID;

  DataFlowSanitizer(
      const std::vector<std::string> &ABIListFiles = std::vector<std::string>(),
      void *(*getArgTLS)() = nullptr, void *(*getRetValTLS)() = nullptr);

  bool doInitialization(Module &M) override;
  bool runOnModule(Module &M) override;
  void insertRuntimeFunctions();
  void collectFunctions(std::vector<Function*>&, Module &M);
  void collectBasicBlocks(std::vector<BasicBlock*>&, Module &M);

  std::unordered_map<BasicBlock*, Value*> basic_block_id_map;
};


/*
 * This class represents a DFSan function.
 * During the runOnModule method when it encounters a function it wants to instrument it creates a
 * DFSan function object and uses it to make a DFSan visitor
 *
 * Mostly this class has some metadata about the current function being analyzed and some methods for
 * creating IR that will load/store shadow values.
 *
 * The ValShadowMap is a cache that is used to look up if an instructions shadow has already been accessed/set
 * in the current function so instead of creating new IR you can just grab its Value* and use it directly. The load
 * function will do this for you so you don't really need to know this.
 */
struct DFSanFunction {
  DataFlowSanitizer &DFS;
  Function *F;
  DominatorTree DT;
  DataFlowSanitizer::InstrumentedABI IA;
  bool IsNativeABI;
  Value *ArgTLSPtr = nullptr;
  Value *RetvalTLSPtr = nullptr;
  AllocaInst *LabelReturnAlloca = nullptr;
  DenseMap<Value *, Value *> ValShadowMap;
  DenseMap<AllocaInst *, AllocaInst *> AllocaShadowMap;
  std::vector<std::pair<PHINode *, PHINode *>> PHIFixups;
  DenseSet<Instruction *> SkipInsts;
  std::vector<Value *> NonZeroChecks;
  bool AvoidNewBlocks;

  struct CachedCombinedShadow {
    BasicBlock *Block;
    Value *Shadow;
  };
  DenseMap<std::pair<Value *, Value *>, CachedCombinedShadow>
      CachedCombinedShadows;
  DenseMap<Value *, std::set<Value *>> ShadowElements;

  DFSanFunction(DataFlowSanitizer &DFS, Function *F, bool IsNativeABI)
      : DFS(DFS), F(F), IA(DFS.getInstrumentedABI()), IsNativeABI(IsNativeABI) {
    DT.recalculate(*F);
    // FIXME: Need to track down the register allocator issue which causes poor
    // performance in pathological cases with large numbers of basic blocks.
    AvoidNewBlocks = F->size() > 1000;
  }

  Value *getArgTLSPtr();
  Value *getArgTLS(unsigned Index, Instruction *Pos);
  Value *getRetvalTLS();
  Value *getShadow(Value *V);
  void setShadow(Instruction *I, Value *Shadow);
  Value *combineShadows(Value *V1, Value *V2, Instruction *Pos);
  Value *combineOperandShadows(Instruction *Inst);
  Value *loadShadow(Value *ShadowAddr, uint64_t Size, uint64_t Align,
                    Instruction *Pos);
  void storeShadow(Value *Addr, uint64_t Size, uint64_t Align, Value *Shadow,
                   Instruction *Pos);
};

/*
 * This class is what does most of the instrumentation and propagation
 * it visits every insruction within a function and adds instrumentation logic for it
 *
 * This is where the functions created during runOnModule are actually inserted, and it's where
 * we insert our calls to Polytrackers runtime.
 */
class DFSanVisitor : public InstVisitor<DFSanVisitor> {
public:
  DFSanFunction &DFSF;

  DFSanVisitor(DFSanFunction &DFSF) : DFSF(DFSF) {}

  const DataLayout &getDataLayout() const {
    return DFSF.F->getParent()->getDataLayout();
  }
  void logTaintedCmp(Instruction *InsertPoint, Value *Shadow);
  void logTaintedOps(Instruction *InsertPoint, Value *Shadow);
  void traceTaintedBinaryOp(Instruction * inst);

  void visitOperandShadowInst(Instruction &I);
  void visitBinaryOperator(BinaryOperator &BO);
  void visitCastInst(CastInst &CI);
  void visitCmpInst(CmpInst &CI);
  void visitGetElementPtrInst(GetElementPtrInst &GEPI);
  void visitLoadInst(LoadInst &LI);
  void visitStoreInst(StoreInst &SI);
  void visitReturnInst(ReturnInst &RI);
  void visitCallSite(CallSite CS);
  void visitPHINode(PHINode &PN);
  void visitExtractElementInst(ExtractElementInst &I);
  void visitInsertElementInst(InsertElementInst &I);
  void visitShuffleVectorInst(ShuffleVectorInst &I);
  void visitExtractValueInst(ExtractValueInst &I);
  void visitInsertValueInst(InsertValueInst &I);
  void visitAllocaInst(AllocaInst &I);
  void visitSelectInst(SelectInst &I);
  void visitMemSetInst(MemSetInst &I);
  void visitMemTransferInst(MemTransferInst &I);
};

#endif /* POLYTRACKER_SRC_DFSAN_PASS_DFSAN_PASS_H_ */
