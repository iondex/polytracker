/*
 * dfsan_function.cpp
 *
 *  Created on: Jul 24, 2020
 *      Author: carson
 */

#include "dfsan_pass.h"

// A convenience function which folds the shadows of each of the operands
// of the provided instruction Inst, inserting the IR before Inst.  Returns
// the computed union Value.
Value *DFSanFunction::combineOperandShadows(Instruction *Inst) {
  if (Inst->getNumOperands() == 0)
    return DFS.ZeroShadow;

  Value *Shadow = getShadow(Inst->getOperand(0));
  for (unsigned i = 1, n = Inst->getNumOperands(); i != n; ++i) {
    Shadow = combineShadows(Shadow, getShadow(Inst->getOperand(i)), Inst);
  }
  return Shadow;
}

// Generates IR to compute the union of the two given shadows, inserting it
// before Pos.  Returns the computed union Value.
Value *DFSanFunction::combineShadows(Value *V1, Value *V2, Instruction *Pos) {
  if (V1 == DFS.ZeroShadow)
    return V2;
  if (V2 == DFS.ZeroShadow)
    return V1;
  if (V1 == V2)
    return V1;

  auto V1Elems = ShadowElements.find(V1);
  auto V2Elems = ShadowElements.find(V2);
  if (V1Elems != ShadowElements.end() && V2Elems != ShadowElements.end()) {
    if (std::includes(V1Elems->second.begin(), V1Elems->second.end(),
                      V2Elems->second.begin(), V2Elems->second.end())) {
      return V1;
    } else if (std::includes(V2Elems->second.begin(), V2Elems->second.end(),
                             V1Elems->second.begin(), V1Elems->second.end())) {
      return V2;
    }
  } else if (V1Elems != ShadowElements.end()) {
    if (V1Elems->second.count(V2))
      return V1;
  } else if (V2Elems != ShadowElements.end()) {
    if (V2Elems->second.count(V1))
      return V2;
  }

  auto Key = std::make_pair(V1, V2);
  if (V1 > V2)
    std::swap(Key.first, Key.second);
  CachedCombinedShadow &CCS = CachedCombinedShadows[Key];
  if (CCS.Block && DT.dominates(CCS.Block, Pos->getParent()))
    return CCS.Shadow;

  IRBuilder<> IRB(Pos);
  if (AvoidNewBlocks) {
    CallInst *Call = IRB.CreateCall(DFS.DFSanCheckedUnionFn, {V1, V2});
    Call->addAttribute(AttributeList::ReturnIndex, Attribute::ZExt);
    Call->addParamAttr(0, Attribute::ZExt);
    Call->addParamAttr(1, Attribute::ZExt);

    CCS.Block = Pos->getParent();
    CCS.Shadow = Call;
  } else {
    BasicBlock *Head = Pos->getParent();
    Value *Ne = IRB.CreateICmpNE(V1, V2);
    BranchInst *BI = cast<BranchInst>(SplitBlockAndInsertIfThen(
        Ne, Pos, /*Unreachable=*/false, DFS.ColdCallWeights, &DT));
    IRBuilder<> ThenIRB(BI);
    CallInst *Call = ThenIRB.CreateCall(DFS.DFSanUnionFn, {V1, V2});
    Call->addAttribute(AttributeList::ReturnIndex, Attribute::ZExt);
    Call->addParamAttr(0, Attribute::ZExt);
    Call->addParamAttr(1, Attribute::ZExt);

    BasicBlock *Tail = BI->getSuccessor(0);
    PHINode *Phi = PHINode::Create(DFS.ShadowTy, 2, "", &Tail->front());
    Phi->addIncoming(Call, Call->getParent());
    Phi->addIncoming(V1, Head);

    CCS.Block = Tail;
    CCS.Shadow = Phi;
  }

  std::set<Value *> UnionElems;
  if (V1Elems != ShadowElements.end()) {
    UnionElems = V1Elems->second;
  } else {
    UnionElems.insert(V1);
  }
  if (V2Elems != ShadowElements.end()) {
    UnionElems.insert(V2Elems->second.begin(), V2Elems->second.end());
  } else {
    UnionElems.insert(V2);
  }
  ShadowElements[CCS.Shadow] = std::move(UnionElems);

  return CCS.Shadow;
}

// Generates IR to load shadow corresponding to bytes [Addr, Addr+Size), where
// Addr has alignment Align, and take the union of each of those shadows.
Value *DFSanFunction::loadShadow(Value *Addr, uint64_t Size, uint64_t Align,
                                 Instruction *Pos) {
  if (AllocaInst *AI = dyn_cast<AllocaInst>(Addr)) {
    const auto i = AllocaShadowMap.find(AI);
    if (i != AllocaShadowMap.end()) {
      IRBuilder<> IRB(Pos);
      return IRB.CreateLoad(i->second);
    }
  }

  uint64_t ShadowAlign = Align * DFS.ShadowWidth / 8;
  SmallVector<Value *, 2> Objs;
  GetUnderlyingObjects(Addr, Objs, Pos->getModule()->getDataLayout());
  bool AllConstants = true;
  for (Value *Obj : Objs) {
    if (isa<Function>(Obj) || isa<BlockAddress>(Obj))
      continue;
    if (isa<GlobalVariable>(Obj) && cast<GlobalVariable>(Obj)->isConstant())
      continue;

    AllConstants = false;
    break;
  }
  if (AllConstants)
    return DFS.ZeroShadow;

  Value *ShadowAddr = DFS.getShadowAddress(Addr, Pos);
  switch (Size) {
  case 0:
    return DFS.ZeroShadow;
  case 1: {
    LoadInst *LI = new LoadInst(ShadowAddr, "", Pos);
    LI->setAlignment(ShadowAlign);
    return LI;
  }
  case 2: {
    IRBuilder<> IRB(Pos);
    Value *ShadowAddr1 = IRB.CreateGEP(DFS.ShadowTy, ShadowAddr,
                                       ConstantInt::get(DFS.IntptrTy, 1));
    return combineShadows(IRB.CreateAlignedLoad(ShadowAddr, ShadowAlign),
                          IRB.CreateAlignedLoad(ShadowAddr1, ShadowAlign), Pos);
  }
  }
  if (!AvoidNewBlocks && Size % (64 / DFS.ShadowWidth) == 0) {
    // Fast path for the common case where each byte has identical shadow: load
    // shadow 64 bits at a time, fall out to a __dfsan_union_load call if any
    // shadow is non-equal.
    BasicBlock *FallbackBB = BasicBlock::Create(*DFS.Ctx, "", F);
    IRBuilder<> FallbackIRB(FallbackBB);
    CallInst *FallbackCall = FallbackIRB.CreateCall(
        DFS.DFSanUnionLoadFn,
        {ShadowAddr, ConstantInt::get(DFS.IntptrTy, Size)});
    FallbackCall->addAttribute(AttributeList::ReturnIndex, Attribute::ZExt);

    // Compare each of the shadows stored in the loaded 64 bits to each other,
    // by computing (WideShadow rotl ShadowWidth) == WideShadow.
    IRBuilder<> IRB(Pos);
    Value *WideAddr =
        IRB.CreateBitCast(ShadowAddr, Type::getInt64PtrTy(*DFS.Ctx));
    Value *WideShadow = IRB.CreateAlignedLoad(WideAddr, ShadowAlign);
    Value *TruncShadow = IRB.CreateTrunc(WideShadow, DFS.ShadowTy);
    Value *ShlShadow = IRB.CreateShl(WideShadow, DFS.ShadowWidth);
    Value *ShrShadow = IRB.CreateLShr(WideShadow, 64 - DFS.ShadowWidth);
    Value *RotShadow = IRB.CreateOr(ShlShadow, ShrShadow);
    Value *ShadowsEq = IRB.CreateICmpEQ(WideShadow, RotShadow);

    BasicBlock *Head = Pos->getParent();
    BasicBlock *Tail = Head->splitBasicBlock(Pos->getIterator());

    if (DomTreeNode *OldNode = DT.getNode(Head)) {
      std::vector<DomTreeNode *> Children(OldNode->begin(), OldNode->end());

      DomTreeNode *NewNode = DT.addNewBlock(Tail, Head);
      for (auto Child : Children)
        DT.changeImmediateDominator(Child, NewNode);
    }

    // In the following code LastBr will refer to the previous basic block's
    // conditional branch instruction, whose true successor is fixed up to point
    // to the next block during the loop below or to the tail after the final
    // iteration.
    BranchInst *LastBr = BranchInst::Create(FallbackBB, FallbackBB, ShadowsEq);
    ReplaceInstWithInst(Head->getTerminator(), LastBr);
    DT.addNewBlock(FallbackBB, Head);

    for (uint64_t Ofs = 64 / DFS.ShadowWidth; Ofs != Size;
         Ofs += 64 / DFS.ShadowWidth) {
      BasicBlock *NextBB = BasicBlock::Create(*DFS.Ctx, "", F);
      DT.addNewBlock(NextBB, LastBr->getParent());
      IRBuilder<> NextIRB(NextBB);
      WideAddr = NextIRB.CreateGEP(Type::getInt64Ty(*DFS.Ctx), WideAddr,
                                   ConstantInt::get(DFS.IntptrTy, 1));
      Value *NextWideShadow = NextIRB.CreateAlignedLoad(WideAddr, ShadowAlign);
      ShadowsEq = NextIRB.CreateICmpEQ(WideShadow, NextWideShadow);
      LastBr->setSuccessor(0, NextBB);
      LastBr = NextIRB.CreateCondBr(ShadowsEq, FallbackBB, FallbackBB);
    }

    LastBr->setSuccessor(0, Tail);
    FallbackIRB.CreateBr(Tail);
    PHINode *Shadow = PHINode::Create(DFS.ShadowTy, 2, "", &Tail->front());
    Shadow->addIncoming(FallbackCall, FallbackBB);
    Shadow->addIncoming(TruncShadow, LastBr->getParent());
    return Shadow;
  }

  IRBuilder<> IRB(Pos);
  CallInst *FallbackCall = IRB.CreateCall(
      DFS.DFSanUnionLoadFn, {ShadowAddr, ConstantInt::get(DFS.IntptrTy, Size)});
  FallbackCall->addAttribute(AttributeList::ReturnIndex, Attribute::ZExt);
  return FallbackCall;
}

void DFSanFunction::storeShadow(Value *Addr, uint64_t Size, uint64_t Align,
                                Value *Shadow, Instruction *Pos) {
  if (AllocaInst *AI = dyn_cast<AllocaInst>(Addr)) {
    const auto i = AllocaShadowMap.find(AI);
    if (i != AllocaShadowMap.end()) {
      IRBuilder<> IRB(Pos);
      IRB.CreateStore(Shadow, i->second);
      return;
    }
  }

  uint64_t ShadowAlign = Align * DFS.ShadowWidth / 8;
  IRBuilder<> IRB(Pos);
  Value *ShadowAddr = DFS.getShadowAddress(Addr, Pos);
  if (Shadow == DFS.ZeroShadow) {
    IntegerType *ShadowTy = IntegerType::get(*DFS.Ctx, Size * DFS.ShadowWidth);
    Value *ExtZeroShadow = ConstantInt::get(ShadowTy, 0);
    Value *ExtShadowAddr =
        IRB.CreateBitCast(ShadowAddr, PointerType::getUnqual(ShadowTy));
    IRB.CreateAlignedStore(ExtZeroShadow, ExtShadowAddr, ShadowAlign);
    return;
  }

  const unsigned ShadowVecSize = 128 / DFS.ShadowWidth;
  uint64_t Offset = 0;
  if (Size >= ShadowVecSize) {
    VectorType *ShadowVecTy = VectorType::get(DFS.ShadowTy, ShadowVecSize);
    Value *ShadowVec = UndefValue::get(ShadowVecTy);
    for (unsigned i = 0; i != ShadowVecSize; ++i) {
      ShadowVec = IRB.CreateInsertElement(
          ShadowVec, Shadow, ConstantInt::get(Type::getInt32Ty(*DFS.Ctx), i));
    }
    Value *ShadowVecAddr =
        IRB.CreateBitCast(ShadowAddr, PointerType::getUnqual(ShadowVecTy));
    do {
      Value *CurShadowVecAddr =
          IRB.CreateConstGEP1_32(ShadowVecTy, ShadowVecAddr, Offset);
      IRB.CreateAlignedStore(ShadowVec, CurShadowVecAddr, ShadowAlign);
      Size -= ShadowVecSize;
      ++Offset;
    } while (Size >= ShadowVecSize);
    Offset *= ShadowVecSize;
  }
  while (Size > 0) {
    Value *CurShadowAddr =
        IRB.CreateConstGEP1_32(DFS.ShadowTy, ShadowAddr, Offset);
    IRB.CreateAlignedStore(Shadow, CurShadowAddr, ShadowAlign);
    --Size;
    ++Offset;
  }
}

Value *DFSanFunction::getArgTLSPtr() {
  if (ArgTLSPtr)
    return ArgTLSPtr;
  if (DFS.ArgTLS)
    return ArgTLSPtr = DFS.ArgTLS;

  IRBuilder<> IRB(&F->getEntryBlock().front());
  return ArgTLSPtr = IRB.CreateCall(DFS.GetArgTLS, {});
}

Value *DFSanFunction::getRetvalTLS() {
  if (RetvalTLSPtr)
    return RetvalTLSPtr;
  if (DFS.RetvalTLS)
    return RetvalTLSPtr = DFS.RetvalTLS;

  IRBuilder<> IRB(&F->getEntryBlock().front());
  return RetvalTLSPtr = IRB.CreateCall(DFS.GetRetvalTLS, {});
}

Value *DFSanFunction::getArgTLS(unsigned Idx, Instruction *Pos) {
  IRBuilder<> IRB(Pos);
  return IRB.CreateConstGEP2_64(getArgTLSPtr(), 0, Idx);
}

Value *DFSanFunction::getShadow(Value *V) {
  if (!isa<Argument>(V) && !isa<Instruction>(V))
    return DFS.ZeroShadow;
  Value *&Shadow = ValShadowMap[V];
  if (!Shadow) {
    if (Argument *A = dyn_cast<Argument>(V)) {
      if (IsNativeABI)
        return DFS.ZeroShadow;
      switch (IA) {
      case DataFlowSanitizer::IA_TLS: {
        Value *ArgTLSPtr = getArgTLSPtr();
        Instruction *ArgTLSPos =
            DFS.ArgTLS ? &*F->getEntryBlock().begin()
                       : cast<Instruction>(ArgTLSPtr)->getNextNode();
        IRBuilder<> IRB(ArgTLSPos);
        Shadow = IRB.CreateLoad(getArgTLS(A->getArgNo(), ArgTLSPos));
        break;
      }
      case DataFlowSanitizer::IA_Args: {
        unsigned ArgIdx = A->getArgNo() + F->arg_size() / 2;
        Function::arg_iterator i = F->arg_begin();
        while (ArgIdx--)
          ++i;
        Shadow = &*i;
        assert(Shadow->getType() == DFS.ShadowTy);
        break;
      }
      }
      NonZeroChecks.push_back(Shadow);
    } else {
      Shadow = DFS.ZeroShadow;
    }
  }
  return Shadow;
}

void DFSanFunction::setShadow(Instruction *I, Value *Shadow) {
  assert(!ValShadowMap.count(I));
  assert(Shadow->getType() == DFS.ShadowTy);
  ValShadowMap[I] = Shadow;
}

