/*
 * dfsan_visitor.cpp
 *
 *  Created on: Jul 24, 2020
 *      Author: carson
 */

#include "dfsan_pass.h"

//CLI opts from main
extern cl::opt<bool> ClCombinePointerLabelsOnLoad;
extern cl::opt<bool> ClCombinePointerLabelsOnStore;
extern cl::opt<bool> ClPreserveAlignment;

namespace {

/// Given function attributes from a call site for the original function,
/// return function attributes appropriate for a call to the transformed
/// function.
AttributeList
TransformFunctionAttributes(const TransformedFunction &TransformedFunction,
                            LLVMContext &Ctx, AttributeList CallSiteAttrs) {

  // Construct a vector of AttributeSet for each function argument.
  std::vector<llvm::AttributeSet> ArgumentAttributes(
      TransformedFunction.TransformedType->getNumParams());

  // Copy attributes from the parameter of the original function to the
  // transformed version.  'ArgumentIndexMapping' holds the mapping from
  // old argument position to new.
  for (unsigned i = 0, ie = TransformedFunction.ArgumentIndexMapping.size();
       i < ie; ++i) {
    unsigned TransformedIndex = TransformedFunction.ArgumentIndexMapping[i];
    ArgumentAttributes[TransformedIndex] = CallSiteAttrs.getParamAttributes(i);
  }

  // Copy annotations on varargs arguments.
  for (unsigned i = TransformedFunction.OriginalType->getNumParams(),
                ie = CallSiteAttrs.getNumAttrSets();
       i < ie; ++i) {
    ArgumentAttributes.push_back(CallSiteAttrs.getParamAttributes(i));
  }

  return AttributeList::get(Ctx, CallSiteAttrs.getFnAttributes(),
                            CallSiteAttrs.getRetAttributes(),
                            llvm::makeArrayRef(ArgumentAttributes));
}

} // end anonymous namespace

void DFSanVisitor::logTaintedOps(Instruction *InsertPoint, Value *Shadow) {
  IRBuilder<> IRB(InsertPoint);
  int op_code = InsertPoint->getOpcode();
  IntegerType * int_ty = IntegerType::get(*DFSF.DFS.Ctx, 32);
  //FIXME Add
  Value *ExtZeroShadow = ConstantInt::get(int_ty, op_code);
  CallInst *Call = IRB.CreateCall(DFSF.DFS.DFSanLogTaintFn, Shadow);
}


void DFSanVisitor::visitOperandShadowInst(Instruction &I) {
  Value *CombinedShadow = DFSF.combineOperandShadows(&I);
  DFSF.setShadow(&I, CombinedShadow);
  logTaintedOps(&I, CombinedShadow);
}

void DFSanVisitor::visitLoadInst(LoadInst &LI) {
  auto &DL = LI.getModule()->getDataLayout();
  uint64_t Size = DL.getTypeStoreSize(LI.getType());
  if (Size == 0) {
    DFSF.setShadow(&LI, DFSF.DFS.ZeroShadow);
    return;
  }

  uint64_t Align;
  if (ClPreserveAlignment) {
    Align = LI.getAlignment();
    if (Align == 0)
      Align = DL.getABITypeAlignment(LI.getType());
  } else {
    Align = 1;
  }
  IRBuilder<> IRB(&LI);
  Value *Shadow = DFSF.loadShadow(LI.getPointerOperand(), Size, Align, &LI);
  if (ClCombinePointerLabelsOnLoad) {
    Value *PtrShadow = DFSF.getShadow(LI.getPointerOperand());
    Shadow = DFSF.combineShadows(Shadow, PtrShadow, &LI);
  }
  if (Shadow != DFSF.DFS.ZeroShadow)
    DFSF.NonZeroChecks.push_back(Shadow);

  DFSF.setShadow(&LI, Shadow);
}


void DFSanVisitor::visitStoreInst(StoreInst &SI) {
  auto &DL = SI.getModule()->getDataLayout();
  uint64_t Size = DL.getTypeStoreSize(SI.getValueOperand()->getType());
  if (Size == 0)
    return;

  uint64_t Align;
  if (ClPreserveAlignment) {
    Align = SI.getAlignment();
    if (Align == 0)
      Align = DL.getABITypeAlignment(SI.getValueOperand()->getType());
  } else {
    Align = 1;
  }

  Value *Shadow = DFSF.getShadow(SI.getValueOperand());
  if (ClCombinePointerLabelsOnStore) {
    Value *PtrShadow = DFSF.getShadow(SI.getPointerOperand());
    Shadow = DFSF.combineShadows(Shadow, PtrShadow, &SI);
  }
  DFSF.storeShadow(SI.getPointerOperand(), Size, Align, Shadow, &SI);
}

void DFSanVisitor::traceTaintedBinaryOp(Instruction * Inst) {
	IRBuilder<> IRB(Inst);
	Value * opt_1 = Inst->getOperand(0);
	Value * opt_2 = Inst->getOperand(1);
	Value * shad_1 = DFSF.getShadow(opt_1);
	Value * shad_2 = DFSF.getShadow(opt_2);
	IntegerType *ShadowTy = IntegerType::get(*DFSF.DFS.Ctx, DFSF.DFS.ShadowWidth);
	auto val = Inst->getOpcode();
	std::cout << "VAL IS: " << val << std::endl;
	Value *ExtZeroShadow = ConstantInt::get(ShadowTy, val);
	//This instruments the binary operand to call a function with both values and their shadows.
	//This creates 4 allocas and 4 stores, but when generating code the LLVM backend will remove non
	//needed allocas/stores etc.
	Value * opt_zero_val = IRB.CreateAlloca(IntegerType::getInt32Ty(*(DFSF.DFS.Ctx)));
	Value * opt_one_val = IRB.CreateAlloca(IntegerType::getInt32Ty(*(DFSF.DFS.Ctx)));
	Value * opt_zero_shadow = IRB.CreateAlloca(IntegerType::getInt32Ty(*(DFSF.DFS.Ctx)));
	Value * opt_one_shadow  = IRB.CreateAlloca(IntegerType::getInt32Ty(*(DFSF.DFS.Ctx)));
	auto store_val_opt0 = IRB.CreateStore(opt_1, opt_zero_val);
	auto store_val_opt1 = IRB.CreateStore(opt_2, opt_one_val);
	auto store_shad_0 = IRB.CreateStore(shad_1, opt_zero_shadow);
	auto store_shad_1 = IRB.CreateStore(shad_2, opt_one_shadow);

	CallInst *CallTest = IRB.CreateCall(DFSF.DFS.DFSanLogInstFn,
			{		  ExtZeroShadow,
					opt_zero_val,
					opt_one_val,
					opt_zero_shadow,
					opt_one_shadow,
			}
	);
}

void DFSanVisitor::visitBinaryOperator(BinaryOperator &BO) {
	visitOperandShadowInst(BO);
	  traceTaintedBinaryOp(&BO);
}

void DFSanVisitor::visitCastInst(CastInst &CI) { visitOperandShadowInst(CI); }

void DFSanVisitor::visitCmpInst(CmpInst &CI) {
  Value *CombinedShadow = DFSF.combineOperandShadows(&CI);
  DFSF.setShadow(&CI, CombinedShadow);

  IRBuilder<> IRB(&CI);
  CallInst *Call = IRB.CreateCall(DFSF.DFS.DFSanLogCmpFn, CombinedShadow);
  traceTaintedBinaryOp(&CI);
}

void DFSanVisitor::visitGetElementPtrInst(GetElementPtrInst &GEPI) {
  visitOperandShadowInst(GEPI);
}

void DFSanVisitor::visitExtractElementInst(ExtractElementInst &I) {
  visitOperandShadowInst(I);
}

void DFSanVisitor::visitInsertElementInst(InsertElementInst &I) {
  visitOperandShadowInst(I);
}

void DFSanVisitor::visitShuffleVectorInst(ShuffleVectorInst &I) {
  visitOperandShadowInst(I);
}

void DFSanVisitor::visitExtractValueInst(ExtractValueInst &I) {
  visitOperandShadowInst(I);
}

void DFSanVisitor::visitInsertValueInst(InsertValueInst &I) {
  visitOperandShadowInst(I);
}

void DFSanVisitor::visitAllocaInst(AllocaInst &I) {
  bool AllLoadsStores = true;
  for (User *U : I.users()) {
    if (isa<LoadInst>(U))
      continue;

    if (StoreInst *SI = dyn_cast<StoreInst>(U)) {
      if (SI->getPointerOperand() == &I)
        continue;
    }

    AllLoadsStores = false;
    break;
  }
  if (AllLoadsStores) {
    IRBuilder<> IRB(&I);
    DFSF.AllocaShadowMap[&I] = IRB.CreateAlloca(DFSF.DFS.ShadowTy);
  }
  DFSF.setShadow(&I, DFSF.DFS.ZeroShadow);
}

void DFSanVisitor::visitSelectInst(SelectInst &I) {
  Value *CondShadow = DFSF.getShadow(I.getCondition());
  Value *TrueShadow = DFSF.getShadow(I.getTrueValue());
  Value *FalseShadow = DFSF.getShadow(I.getFalseValue());

  if (isa<VectorType>(I.getCondition()->getType())) {
    DFSF.setShadow(
        &I,
        DFSF.combineShadows(
            CondShadow, DFSF.combineShadows(TrueShadow, FalseShadow, &I), &I));
  } else {
    Value *ShadowSel;
    if (TrueShadow == FalseShadow) {
      ShadowSel = TrueShadow;
    } else {
      ShadowSel =
          SelectInst::Create(I.getCondition(), TrueShadow, FalseShadow, "", &I);
    }
    DFSF.setShadow(&I, DFSF.combineShadows(CondShadow, ShadowSel, &I));
  }
}

void DFSanVisitor::visitMemSetInst(MemSetInst &I) {
  IRBuilder<> IRB(&I);
  Value *ValShadow = DFSF.getShadow(I.getValue());
  IRB.CreateCall(
      DFSF.DFS.DFSanSetLabelFn,
      {ValShadow,
       IRB.CreateBitCast(I.getDest(), Type::getInt8PtrTy(*DFSF.DFS.Ctx)),
       IRB.CreateZExtOrTrunc(I.getLength(), DFSF.DFS.IntptrTy)});
}

void DFSanVisitor::visitMemTransferInst(MemTransferInst &I) {
  IRBuilder<> IRB(&I);
  Value *DestShadow = DFSF.DFS.getShadowAddress(I.getDest(), &I);
  Value *SrcShadow = DFSF.DFS.getShadowAddress(I.getSource(), &I);
  Value *LenShadow =
      IRB.CreateMul(I.getLength(), ConstantInt::get(I.getLength()->getType(),
                                                    DFSF.DFS.ShadowWidth / 8));
  Type *Int8Ptr = Type::getInt8PtrTy(*DFSF.DFS.Ctx);
  DestShadow = IRB.CreateBitCast(DestShadow, Int8Ptr);
  SrcShadow = IRB.CreateBitCast(SrcShadow, Int8Ptr);
  auto *MTI = cast<MemTransferInst>(
      IRB.CreateCall(I.getCalledValue(),
                     {DestShadow, SrcShadow, LenShadow, I.getVolatileCst()}));
  if (ClPreserveAlignment) {
    MTI->setDestAlignment(I.getDestAlignment() * (DFSF.DFS.ShadowWidth / 8));
    MTI->setSourceAlignment(I.getSourceAlignment() *
                            (DFSF.DFS.ShadowWidth / 8));
  } else {
    MTI->setDestAlignment(DFSF.DFS.ShadowWidth / 8);
    MTI->setSourceAlignment(DFSF.DFS.ShadowWidth / 8);
  }
}

void DFSanVisitor::visitReturnInst(ReturnInst &RI) {
  if (!DFSF.IsNativeABI && RI.getReturnValue()) {
    switch (DFSF.IA) {
    case DataFlowSanitizer::IA_TLS: {
      Value *S = DFSF.getShadow(RI.getReturnValue());
      IRBuilder<> IRB(&RI);
      IRB.CreateStore(S, DFSF.getRetvalTLS());
      break;
    }
    case DataFlowSanitizer::IA_Args: {
      IRBuilder<> IRB(&RI);
      Type *RT = DFSF.F->getFunctionType()->getReturnType();
      Value *InsVal =
          IRB.CreateInsertValue(UndefValue::get(RT), RI.getReturnValue(), 0);
      Value *InsShadow =
          IRB.CreateInsertValue(InsVal, DFSF.getShadow(RI.getReturnValue()), 1);
      RI.setOperand(0, InsShadow);
      break;
    }
    }
  }
  IRBuilder<> IRB(&RI);
  CallInst *ExitCall = IRB.CreateCall(DFSF.DFS.DFSanExitFn, {});
}

void DFSanVisitor::visitCallSite(CallSite CS) {
  Function *F = CS.getCalledFunction();
  if ((F && F->isIntrinsic()) || isa<InlineAsm>(CS.getCalledValue())) {
    visitOperandShadowInst(*CS.getInstruction());
    return;
  }

  // Calls to this function are synthesized in wrappers, and we shouldn't
  // instrument them.
  if (F == DFSF.DFS.DFSanVarargWrapperFn)
    return;

  IRBuilder<> IRB(CS.getInstruction());

  DenseMap<Value *, Function *>::iterator i =
      DFSF.DFS.UnwrappedFnMap.find(CS.getCalledValue());
  if (i != DFSF.DFS.UnwrappedFnMap.end()) {
    Function *F = i->second;
    switch (DFSF.DFS.getWrapperKind(F)) {
    case DataFlowSanitizer::WK_Warning:
      CS.setCalledFunction(F);
      IRB.CreateCall(DFSF.DFS.DFSanUnimplementedFn,
                     IRB.CreateGlobalStringPtr(F->getName()));
      DFSF.setShadow(CS.getInstruction(), DFSF.DFS.ZeroShadow);
      return;
    case DataFlowSanitizer::WK_Discard:
      CS.setCalledFunction(F);
      DFSF.setShadow(CS.getInstruction(), DFSF.DFS.ZeroShadow);
      return;
    case DataFlowSanitizer::WK_Functional:
      CS.setCalledFunction(F);
      visitOperandShadowInst(*CS.getInstruction());
      return;
    case DataFlowSanitizer::WK_Custom:
      // Don't try to handle invokes of custom functions, it's too complicated.
      // Instead, invoke the dfsw$ wrapper, which will in turn call the __dfsw_
      // wrapper.
      if (CallInst *CI = dyn_cast<CallInst>(CS.getInstruction())) {
        FunctionType *FT = F->getFunctionType();
        TransformedFunction CustomFn = DFSF.DFS.getCustomFunctionType(FT);
        std::string CustomFName = "__dfsw_";
        CustomFName += F->getName();
        Constant *CustomF = DFSF.DFS.Mod->getOrInsertFunction(
            CustomFName, CustomFn.TransformedType);
        if (Function *CustomFn = dyn_cast<Function>(CustomF)) {
          CustomFn->copyAttributesFrom(F);

          // Custom functions returning non-void will write to the return label.
          if (!FT->getReturnType()->isVoidTy()) {
            CustomFn->removeAttributes(AttributeList::FunctionIndex,
                                       DFSF.DFS.ReadOnlyNoneAttrs);
          }
        }

        std::vector<Value *> Args;

        CallSite::arg_iterator i = CS.arg_begin();
        for (unsigned n = FT->getNumParams(); n != 0; ++i, --n) {
          Type *T = (*i)->getType();
          FunctionType *ParamFT;
          if (isa<PointerType>(T) &&
              (ParamFT = dyn_cast<FunctionType>(
                   cast<PointerType>(T)->getElementType()))) {
            std::string TName = "dfst";
            TName += utostr(FT->getNumParams() - n);
            TName += "$";
            TName += F->getName();
            Constant *T = DFSF.DFS.getOrBuildTrampolineFunction(ParamFT, TName);
            Args.push_back(T);
            Args.push_back(
                IRB.CreateBitCast(*i, Type::getInt8PtrTy(*DFSF.DFS.Ctx)));
          } else {
            Args.push_back(*i);
          }
        }

        i = CS.arg_begin();
        const unsigned ShadowArgStart = Args.size();
        for (unsigned n = FT->getNumParams(); n != 0; ++i, --n)
          Args.push_back(DFSF.getShadow(*i));

        if (FT->isVarArg()) {
          auto *LabelVATy = ArrayType::get(DFSF.DFS.ShadowTy,
                                           CS.arg_size() - FT->getNumParams());
          auto *LabelVAAlloca =
              new AllocaInst(LabelVATy, getDataLayout().getAllocaAddrSpace(),
                             "labelva", &DFSF.F->getEntryBlock().front());

          for (unsigned n = 0; i != CS.arg_end(); ++i, ++n) {
            auto LabelVAPtr = IRB.CreateStructGEP(LabelVATy, LabelVAAlloca, n);
            IRB.CreateStore(DFSF.getShadow(*i), LabelVAPtr);
          }

          Args.push_back(IRB.CreateStructGEP(LabelVATy, LabelVAAlloca, 0));
        }

        if (!FT->getReturnType()->isVoidTy()) {
          if (!DFSF.LabelReturnAlloca) {
            DFSF.LabelReturnAlloca = new AllocaInst(
                DFSF.DFS.ShadowTy, getDataLayout().getAllocaAddrSpace(),
                "labelreturn", &DFSF.F->getEntryBlock().front());
          }
          Args.push_back(DFSF.LabelReturnAlloca);
        }

        for (i = CS.arg_begin() + FT->getNumParams(); i != CS.arg_end(); ++i)
          Args.push_back(*i);

        CallInst *CustomCI = IRB.CreateCall(CustomF, Args);
        CustomCI->setCallingConv(CI->getCallingConv());
        CustomCI->setAttributes(TransformFunctionAttributes(
            CustomFn, CI->getContext(), CI->getAttributes()));

        // Update the parameter attributes of the custom call instruction to
        // zero extend the shadow parameters. This is required for targets
        // which consider ShadowTy an illegal type.
        for (unsigned n = 0; n < FT->getNumParams(); n++) {
          const unsigned ArgNo = ShadowArgStart + n;
          if (CustomCI->getArgOperand(ArgNo)->getType() == DFSF.DFS.ShadowTy)
            CustomCI->addParamAttr(ArgNo, Attribute::ZExt);
        }

        if (!FT->getReturnType()->isVoidTy()) {
          LoadInst *LabelLoad = IRB.CreateLoad(DFSF.LabelReturnAlloca);
          DFSF.setShadow(CustomCI, LabelLoad);
        }

        CI->replaceAllUsesWith(CustomCI);
        CI->eraseFromParent();
        return;
      }
      break;
    }
  }

  FunctionType *FT = cast<FunctionType>(
      CS.getCalledValue()->getType()->getPointerElementType());
  if (DFSF.DFS.getInstrumentedABI() == DataFlowSanitizer::IA_TLS) {
    for (unsigned i = 0, n = FT->getNumParams(); i != n; ++i) {
      IRB.CreateStore(DFSF.getShadow(CS.getArgument(i)),
                      DFSF.getArgTLS(i, CS.getInstruction()));
    }
  }

  Instruction *Next = nullptr;
  if (!CS.getType()->isVoidTy()) {
    if (InvokeInst *II = dyn_cast<InvokeInst>(CS.getInstruction())) {
      if (II->getNormalDest()->getSinglePredecessor()) {
        Next = &II->getNormalDest()->front();
      } else {
        BasicBlock *NewBB =
            SplitEdge(II->getParent(), II->getNormalDest(), &DFSF.DT);
        Next = &NewBB->front();
      }
    } else {
      assert(CS->getIterator() != CS->getParent()->end());
      Next = CS->getNextNode();
    }

    if (DFSF.DFS.getInstrumentedABI() == DataFlowSanitizer::IA_TLS) {
      IRBuilder<> NextIRB(Next);
      LoadInst *LI = NextIRB.CreateLoad(DFSF.getRetvalTLS());
      DFSF.SkipInsts.insert(LI);
      DFSF.setShadow(CS.getInstruction(), LI);
      DFSF.NonZeroChecks.push_back(LI);
    }
  }

  // Do all instrumentation for IA_Args down here to defer tampering with the
  // CFG in a way that SplitEdge may be able to detect.
  if (DFSF.DFS.getInstrumentedABI() == DataFlowSanitizer::IA_Args) {
    FunctionType *NewFT = DFSF.DFS.getArgsFunctionType(FT);
    Value *Func =
        IRB.CreateBitCast(CS.getCalledValue(), PointerType::getUnqual(NewFT));
    std::vector<Value *> Args;

    CallSite::arg_iterator i = CS.arg_begin(), e = CS.arg_end();
    for (unsigned n = FT->getNumParams(); n != 0; ++i, --n)
      Args.push_back(*i);

    i = CS.arg_begin();
    for (unsigned n = FT->getNumParams(); n != 0; ++i, --n)
      Args.push_back(DFSF.getShadow(*i));

    if (FT->isVarArg()) {
      unsigned VarArgSize = CS.arg_size() - FT->getNumParams();
      ArrayType *VarArgArrayTy = ArrayType::get(DFSF.DFS.ShadowTy, VarArgSize);
      AllocaInst *VarArgShadow =
          new AllocaInst(VarArgArrayTy, getDataLayout().getAllocaAddrSpace(),
                         "", &DFSF.F->getEntryBlock().front());
      Args.push_back(IRB.CreateConstGEP2_32(VarArgArrayTy, VarArgShadow, 0, 0));
      for (unsigned n = 0; i != e; ++i, ++n) {
        IRB.CreateStore(
            DFSF.getShadow(*i),
            IRB.CreateConstGEP2_32(VarArgArrayTy, VarArgShadow, 0, n));
        Args.push_back(*i);
      }
    }

    CallSite NewCS;
    if (InvokeInst *II = dyn_cast<InvokeInst>(CS.getInstruction())) {
      NewCS = IRB.CreateInvoke(Func, II->getNormalDest(), II->getUnwindDest(),
                               Args);
    } else {
      NewCS = IRB.CreateCall(Func, Args);
    }
    NewCS.setCallingConv(CS.getCallingConv());
    NewCS.setAttributes(CS.getAttributes().removeAttributes(
        *DFSF.DFS.Ctx, AttributeList::ReturnIndex,
        AttributeFuncs::typeIncompatible(NewCS.getInstruction()->getType())));

    if (Next) {
      ExtractValueInst *ExVal =
          ExtractValueInst::Create(NewCS.getInstruction(), 0, "", Next);
      DFSF.SkipInsts.insert(ExVal);
      ExtractValueInst *ExShadow =
          ExtractValueInst::Create(NewCS.getInstruction(), 1, "", Next);
      DFSF.SkipInsts.insert(ExShadow);
      DFSF.setShadow(ExVal, ExShadow);
      DFSF.NonZeroChecks.push_back(ExShadow);

      CS.getInstruction()->replaceAllUsesWith(ExVal);
    }

    CS.getInstruction()->eraseFromParent();
  }
}

void DFSanVisitor::visitPHINode(PHINode &PN) {
  PHINode *ShadowPN =
      PHINode::Create(DFSF.DFS.ShadowTy, PN.getNumIncomingValues(), "", &PN);

  // Give the shadow phi node valid predecessors to fool SplitEdge into working.
  Value *UndefShadow = UndefValue::get(DFSF.DFS.ShadowTy);
  for (PHINode::block_iterator i = PN.block_begin(), e = PN.block_end(); i != e;
       ++i) {
    ShadowPN->addIncoming(UndefShadow, *i);
  }

  DFSF.PHIFixups.push_back(std::make_pair(&PN, ShadowPN));
  DFSF.setShadow(&PN, ShadowPN);
}



