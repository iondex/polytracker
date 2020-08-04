//===- DataFlowSanitizer.cpp - dynamic data flow analysis -----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
/// \file
/// This file is a part of DataFlowSanitizer, a generalised dynamic data flow
/// analysis.
///
/// Unlike other Sanitizer tools, this tool is not designed to detect a specific
/// class of bugs on its own.  Instead, it provides a generic dynamic data flow
/// analysis framework to be used by clients to help detect application-specific
/// issues within their own code.
///
/// The analysis is based on automatic propagation of data flow labels (also
/// known as taint labels) through a program as it performs computation.  Each
/// byte of application memory is backed by two bytes of shadow memory which
/// hold the label.  On Linux/x86_64, memory is laid out as follows:
///
/// +--------------------+ 0x800000000000 (top of memory)
/// | application memory |
/// +--------------------+ 0x700000008000 (kAppAddr)
/// |                    |
/// |       unused       |
/// |                    |
/// +--------------------+ 0x200200000000 (kUnusedAddr)
/// |    union table     |
/// +--------------------+ 0x200000000000 (kUnionTableAddr)
/// |   shadow memory    |
/// +--------------------+ 0x000000010000 (kShadowAddr)
/// | reserved by kernel |
/// +--------------------+ 0x000000000000
///
/// To derive a shadow memory address from an application memory address,
/// bits 44-46 are cleared to bring the address into the range
/// [0x000000008000,0x100000000000).  Then the address is shifted left by 1 to
/// account for the double byte representation of shadow labels and move the
/// address into the shadow memory range.  See the function
/// DataFlowSanitizer::getShadowAddress below.
///
/// For more information, please refer to the design document:
/// http://clang.llvm.org/docs/DataFlowSanitizerDesign.html
//
//===----------------------------------------------------------------------===//

//Instruction visitors TODO
//TODO Switch statement
//All the BinaryOps
//All the BitwiseBinaryOps
//icmp, fcmp, select
//

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

#include "dfsan_pass.h"

using namespace llvm;

// External symbol to be used when generating the shadow address for
// architectures with multiple VMAs. Instead of using a constant integer
// the runtime will set the external mask based on the VMA range.
static const char *const kDFSanExternShadowPtrMask = "__dfsan_shadow_ptr_mask";

// The -dfsan-preserve-alignment flag controls whether this pass assumes that
// alignment requirements provided by the input IR are correct.  For example,
// if the input IR contains a load with alignment 8, this flag will cause
// the shadow load to have alignment 16.  This flag is disabled by default as
// we have unfortunately encountered too much code (including Clang itself;
// see PR14291) which performs misaligned access.
cl::opt<bool> ClPreserveAlignment(
		"polytrack-dfsan-preserve-alignment",
		cl::desc("respect alignment requirements provided by input IR"), cl::Hidden,
		cl::init(false));

// The ABI list files control how shadow parameters are passed. The pass treats
// every function labelled "uninstrumented" in the ABI list file as conforming
// to the "native" (i.e. unsanitized) ABI.  Unless the ABI list contains
// additional annotations for those functions, a call to one of those functions
// will produce a warning message, as the labelling behaviour of the function is
// unknown.  The other supported annotations are "functional" and "discard",
// which are described below under DataFlowSanitizer::WrapperKind.
cl::list<std::string> ClABIListFiles(
		"polytrack-dfsan-abilist",
		cl::desc("File listing native ABI functions and how the pass treats them"),
		cl::Hidden);

// Controls whether the pass uses IA_Args or IA_TLS as the ABI for instrumented
// functions (see DataFlowSanitizer::InstrumentedABI below).
cl::opt<bool>
ClArgsABI("polytrack-dfsan-args-abi",
		cl::desc("Use the argument ABI rather than the TLS ABI"),
		cl::Hidden);

// Controls whether the pass includes or ignores the labels of pointers in load
// instructions.
cl::opt<bool> ClCombinePointerLabelsOnLoad(
		"polytrack-dfsan-combine-pointer-labels-on-load",
		cl::desc("Combine the label of the pointer with the label of the data when "
				"loading from memory."),
				cl::Hidden, cl::init(true));

// Controls whether the pass includes or ignores the labels of pointers in
// stores instructions.
cl::opt<bool> ClCombinePointerLabelsOnStore(
		"polytrack-dfsan-combine-pointer-labels-on-store",
		cl::desc("Combine the label of the pointer with the label of the data when "
				"storing in memory."),
				cl::Hidden, cl::init(false));

cl::opt<bool> ClDebugNonzeroLabels(
		"polytrack-dfsan-debug-nonzero-labels",
		cl::desc("Insert calls to __dfsan_nonzero_label on observing a parameter, "
				"load or return with a nonzero label"),
				cl::Hidden);

char DataFlowSanitizer::ID;

INITIALIZE_PASS(DataFlowSanitizer, "dfsan",
		"DataFlowSanitizer: dynamic data flow analysis.", false, false)

ModulePass *
llvm::createDataFlowSanitizerPass(const std::vector<std::string> &ABIListFiles,
		void *(*getArgTLS)(),
		void *(*getRetValTLS)()) {
	return new DataFlowSanitizer(ABIListFiles, getArgTLS, getRetValTLS);
}

DataFlowSanitizer::DataFlowSanitizer(
		const std::vector<std::string> &ABIListFiles, void *(*getArgTLS)(),
		void *(*getRetValTLS)())
: ModulePass(ID), GetArgTLSPtr(getArgTLS), GetRetvalTLSPtr(getRetValTLS) {
	std::vector<std::string> AllABIListFiles(std::move(ABIListFiles));
	AllABIListFiles.insert(AllABIListFiles.end(), ClABIListFiles.begin(),
			ClABIListFiles.end());
	ABIList.set(SpecialCaseList::createOrDie(AllABIListFiles));
}

FunctionType *DataFlowSanitizer::getArgsFunctionType(FunctionType *T) {
	SmallVector<Type *, 4> ArgTypes(T->param_begin(), T->param_end());
	ArgTypes.append(T->getNumParams(), ShadowTy);
	if (T->isVarArg())
		ArgTypes.push_back(ShadowPtrTy);
	Type *RetType = T->getReturnType();
	if (!RetType->isVoidTy())
		RetType = StructType::get(RetType, ShadowTy);
	return FunctionType::get(RetType, ArgTypes, T->isVarArg());
}

FunctionType *DataFlowSanitizer::getTrampolineFunctionType(FunctionType *T) {
	assert(!T->isVarArg());
	SmallVector<Type *, 4> ArgTypes;
	ArgTypes.push_back(T->getPointerTo());
	ArgTypes.append(T->param_begin(), T->param_end());
	ArgTypes.append(T->getNumParams(), ShadowTy);
	Type *RetType = T->getReturnType();
	if (!RetType->isVoidTy())
		ArgTypes.push_back(ShadowPtrTy);
	return FunctionType::get(T->getReturnType(), ArgTypes, false);
}

TransformedFunction DataFlowSanitizer::getCustomFunctionType(FunctionType *T) {
	SmallVector<Type *, 4> ArgTypes;

	// Some parameters of the custom function being constructed are
	// parameters of T.  Record the mapping from parameters of T to
	// parameters of the custom function, so that parameter attributes
	// at call sites can be updated.
	std::vector<unsigned> ArgumentIndexMapping;
	for (unsigned i = 0, ie = T->getNumParams(); i != ie; ++i) {
		Type *param_type = T->getParamType(i);
		FunctionType *FT;
		if (isa<PointerType>(param_type) &&
				(FT = dyn_cast<FunctionType>(
						cast<PointerType>(param_type)->getElementType()))) {
			ArgumentIndexMapping.push_back(ArgTypes.size());
			ArgTypes.push_back(getTrampolineFunctionType(FT)->getPointerTo());
			ArgTypes.push_back(Type::getInt8PtrTy(*Ctx));
		} else {
			ArgumentIndexMapping.push_back(ArgTypes.size());
			ArgTypes.push_back(param_type);
		}
	}
	for (unsigned i = 0, e = T->getNumParams(); i != e; ++i)
		ArgTypes.push_back(ShadowTy);
	if (T->isVarArg())
		ArgTypes.push_back(ShadowPtrTy);
	Type *RetType = T->getReturnType();
	if (!RetType->isVoidTy())
		ArgTypes.push_back(ShadowPtrTy);
	return TransformedFunction(
			T, FunctionType::get(T->getReturnType(), ArgTypes, T->isVarArg()),
			ArgumentIndexMapping);
}

bool DataFlowSanitizer::doInitialization(Module &M) {
	Triple TargetTriple(M.getTargetTriple());
	bool IsX86_64 = TargetTriple.getArch() == Triple::x86_64;
	bool IsMIPS64 = TargetTriple.isMIPS64();
	bool IsAArch64 = TargetTriple.getArch() == Triple::aarch64 ||
			TargetTriple.getArch() == Triple::aarch64_be;

	const DataLayout &DL = M.getDataLayout();

	Mod = &M;
	Ctx = &M.getContext();
	ShadowTy = IntegerType::get(*Ctx, ShadowWidth);
	ShadowPtrTy = PointerType::getUnqual(ShadowTy);
	IntptrTy = DL.getIntPtrType(*Ctx);
	ZeroShadow = ConstantInt::getSigned(ShadowTy, 0);
	ShadowPtrMul = ConstantInt::getSigned(IntptrTy, ShadowWidth / 8);
	if (IsX86_64)
		ShadowPtrMask = ConstantInt::getSigned(IntptrTy, ~0x700000000000LL);
	else if (IsMIPS64)
		ShadowPtrMask = ConstantInt::getSigned(IntptrTy, ~0xF000000000LL);
	// AArch64 supports multiple VMAs and the shadow mask is set at runtime.
	else if (IsAArch64)
		DFSanRuntimeShadowMask = true;
	else
		report_fatal_error("unsupported triple");

	Type *DFSanUnionArgs[2] = {ShadowTy, ShadowTy};
	DFSanUnionFnTy =
			FunctionType::get(ShadowTy, DFSanUnionArgs, /*isVarArg=*/false);
	Type *DFSanUnionLoadArgs[2] = {ShadowPtrTy, IntptrTy};
	DFSanUnionLoadFnTy =
			FunctionType::get(ShadowTy, DFSanUnionLoadArgs, /*isVarArg=*/false);
	DFSanUnimplementedFnTy = FunctionType::get(
			Type::getVoidTy(*Ctx), Type::getInt8PtrTy(*Ctx), /*isVarArg=*/false);

	Type *DFSanLogTaintArgs[1] = {ShadowTy};
	DFSanLogTaintFnTy =
			FunctionType::get(Type::getVoidTy(*Ctx), DFSanLogTaintArgs, false);

	Type *DFSanLogCmpArgs[1] = {ShadowTy};
	DFSanLogCmpFnTy =
			FunctionType::get(Type::getVoidTy(*Ctx), DFSanLogCmpArgs, false);

	Type *DFSanEntryArgs[1] = {Type::getInt8PtrTy(*Ctx)};
	DFSanEntryFnTy =
			FunctionType::get(IntegerType::getInt64Ty(*Ctx), DFSanEntryArgs, false);

	DFSanExitFnTy = FunctionType::get(Type::getVoidTy(*Ctx), {}, false);
	Type *DFSanEntryBBArgs[3] = {Type::getInt8PtrTy(*Ctx),
			IntegerType::getInt32Ty(*Ctx),
			IntegerType::getInt32Ty(*Ctx)};
	DFSanEntryBBFnTy =
			FunctionType::get(Type::getVoidTy(*Ctx), DFSanEntryBBArgs, false);
	DFSanExitBBFnTy = FunctionType::get(Type::getVoidTy(*Ctx), {}, false);
	Type *DFSanResetFrameArgs[1] = {IntegerType::getInt64PtrTy(*Ctx)};
	DFSanResetFrameFnTy =
			FunctionType::get(Type::getVoidTy(*Ctx), DFSanResetFrameArgs, false);

	Type *DFSanSetLabelArgs[3] = {ShadowTy, Type::getInt8PtrTy(*Ctx), IntptrTy};
	DFSanSetLabelFnTy = FunctionType::get(Type::getVoidTy(*Ctx),
			DFSanSetLabelArgs, /*isVarArg=*/false);

	DFSanNonzeroLabelFnTy =
			FunctionType::get(Type::getVoidTy(*Ctx), None, /*isVarArg=*/false);
	DFSanVarargWrapperFnTy = FunctionType::get(
			Type::getVoidTy(*Ctx), Type::getInt8PtrTy(*Ctx), /*isVarArg=*/false);

	if (GetArgTLSPtr) {
		Type *ArgTLSTy = ArrayType::get(ShadowTy, 64);
		ArgTLS = nullptr;
		GetArgTLS = ConstantExpr::getIntToPtr(
				ConstantInt::get(IntptrTy, uintptr_t(GetArgTLSPtr)),
				PointerType::getUnqual(
						FunctionType::get(PointerType::getUnqual(ArgTLSTy), false)));
	}
	if (GetRetvalTLSPtr) {
		RetvalTLS = nullptr;
		GetRetvalTLS = ConstantExpr::getIntToPtr(
				ConstantInt::get(IntptrTy, uintptr_t(GetRetvalTLSPtr)),
				PointerType::getUnqual(
						FunctionType::get(PointerType::getUnqual(ShadowTy), false)));
	}

	ColdCallWeights = MDBuilder(*Ctx).createBranchWeights(1, 1000);
	return true;
}

bool DataFlowSanitizer::isInstrumented(const Function *F) {
	return !ABIList.isIn(*F, "uninstrumented");
}

bool DataFlowSanitizer::isInstrumented(const GlobalAlias *GA) {
	return !ABIList.isIn(*GA, "uninstrumented");
}

DataFlowSanitizer::InstrumentedABI DataFlowSanitizer::getInstrumentedABI() {
	return ClArgsABI ? IA_Args : IA_TLS;
}

DataFlowSanitizer::WrapperKind DataFlowSanitizer::getWrapperKind(Function *F) {
	if (ABIList.isIn(*F, "custom"))
		return WK_Custom;
	if (ABIList.isIn(*F, "functional"))
		return WK_Functional;
	if (ABIList.isIn(*F, "discard"))
		return WK_Discard;

	return WK_Warning;
}

void DataFlowSanitizer::addGlobalNamePrefix(GlobalValue *GV) {
	std::string GVName = GV->getName(), Prefix = "dfs$";
	GV->setName(Prefix + GVName);

	// Try to change the name of the function in module inline asm.  We only do
	// this for specific asm directives, currently only ".symver", to try to avoid
	// corrupting asm which happens to contain the symbol name as a substring.
	// Note that the substitution for .symver assumes that the versioned symbol
	// also has an instrumented name.
	std::string Asm = GV->getParent()->getModuleInlineAsm();
	std::string SearchStr = ".symver " + GVName + ",";
	size_t Pos = Asm.find(SearchStr);
	if (Pos != std::string::npos) {
		Asm.replace(Pos, SearchStr.size(),
				".symver " + Prefix + GVName + "," + Prefix);
		GV->getParent()->setModuleInlineAsm(Asm);
	}
}

Function *
DataFlowSanitizer::buildWrapperFunction(Function *F, StringRef NewFName,
		GlobalValue::LinkageTypes NewFLink,
		FunctionType *NewFT) {
	FunctionType *FT = F->getFunctionType();
	Function *NewF = Function::Create(NewFT, NewFLink, NewFName, F->getParent());
	NewF->copyAttributesFrom(F);
	NewF->removeAttributes(
			AttributeList::ReturnIndex,
			AttributeFuncs::typeIncompatible(NewFT->getReturnType()));

	BasicBlock *BB = BasicBlock::Create(*Ctx, "entry", NewF);
	if (F->isVarArg()) {
		NewF->removeAttributes(AttributeList::FunctionIndex,
				AttrBuilder().addAttribute("split-stack"));
		CallInst::Create(DFSanVarargWrapperFn,
				IRBuilder<>(BB).CreateGlobalStringPtr(F->getName()), "",
				BB);
		new UnreachableInst(*Ctx, BB);
	} else {
		std::vector<Value *> Args;
		unsigned n = FT->getNumParams();
		for (Function::arg_iterator ai = NewF->arg_begin(); n != 0; ++ai, --n)
			Args.push_back(&*ai);
		CallInst *CI = CallInst::Create(F, Args, "", BB);
		if (FT->getReturnType()->isVoidTy())
			ReturnInst::Create(*Ctx, BB);
		else
			ReturnInst::Create(*Ctx, CI, BB);
	}

	return NewF;
}

Constant *DataFlowSanitizer::getOrBuildTrampolineFunction(FunctionType *FT,
		StringRef FName) {
	FunctionType *FTT = getTrampolineFunctionType(FT);
	Constant *C = Mod->getOrInsertFunction(FName, FTT);
	Function *F = dyn_cast<Function>(C);
	if (F && F->isDeclaration()) {
		F->setLinkage(GlobalValue::LinkOnceODRLinkage);
		BasicBlock *BB = BasicBlock::Create(*Ctx, "entry", F);
		std::vector<Value *> Args;
		Function::arg_iterator AI = F->arg_begin();
		++AI;
		for (unsigned N = FT->getNumParams(); N != 0; ++AI, --N)
			Args.push_back(&*AI);
		CallInst *CI = CallInst::Create(&*F->arg_begin(), Args, "", BB);
		ReturnInst *RI;
		if (FT->getReturnType()->isVoidTy())
			RI = ReturnInst::Create(*Ctx, BB);
		else
			RI = ReturnInst::Create(*Ctx, CI, BB);

		DFSanFunction DFSF(*this, F, /*IsNativeABI=*/true);
		Function::arg_iterator ValAI = F->arg_begin(), ShadowAI = AI;
		++ValAI;
		for (unsigned N = FT->getNumParams(); N != 0; ++ValAI, ++ShadowAI, --N)
			DFSF.ValShadowMap[&*ValAI] = &*ShadowAI;
		DFSanVisitor(DFSF).visitCallInst(*CI);
		if (!FT->getReturnType()->isVoidTy())
			new StoreInst(DFSF.getShadow(RI->getReturnValue()),
					&*std::prev(F->arg_end()), RI);
	}

	return C;
}
/*
 * This function inserts function prototypes that match that of the
 * runtime library. This allows us to insert calls to our runtime library functions
 */
void DataFlowSanitizer::insertRuntimeFunctions() {
	if (!GetArgTLSPtr) {
		Type *ArgTLSTy = ArrayType::get(ShadowTy, 64);
		ArgTLS = Mod->getOrInsertGlobal("__dfsan_arg_tls", ArgTLSTy);
		if (GlobalVariable *G = dyn_cast<GlobalVariable>(ArgTLS))
			G->setThreadLocalMode(GlobalVariable::InitialExecTLSModel);
	}
	if (!GetRetvalTLSPtr) {
		RetvalTLS = Mod->getOrInsertGlobal("__dfsan_retval_tls", ShadowTy);
		if (GlobalVariable *G = dyn_cast<GlobalVariable>(RetvalTLS))
			G->setThreadLocalMode(GlobalVariable::InitialExecTLSModel);
	}

	ExternalShadowMask =
			Mod->getOrInsertGlobal(kDFSanExternShadowPtrMask, IntptrTy);

	DFSanUnionFn = Mod->getOrInsertFunction("__dfsan_union", DFSanUnionFnTy);
	if (Function *F = dyn_cast<Function>(DFSanUnionFn)) {
		F->addAttribute(AttributeList::FunctionIndex, Attribute::NoUnwind);
		F->addAttribute(AttributeList::FunctionIndex, Attribute::ReadNone);
		F->addAttribute(AttributeList::ReturnIndex, Attribute::ZExt);
		F->addParamAttr(0, Attribute::ZExt);
		F->addParamAttr(1, Attribute::ZExt);
	}
	DFSanCheckedUnionFn = Mod->getOrInsertFunction("dfsan_union", DFSanUnionFnTy);
	if (Function *F = dyn_cast<Function>(DFSanCheckedUnionFn)) {
		F->addAttribute(AttributeList::FunctionIndex, Attribute::NoUnwind);
		F->addAttribute(AttributeList::FunctionIndex, Attribute::ReadNone);
		F->addAttribute(AttributeList::ReturnIndex, Attribute::ZExt);
		F->addParamAttr(0, Attribute::ZExt);
		F->addParamAttr(1, Attribute::ZExt);
	}
	DFSanUnionLoadFn =
			Mod->getOrInsertFunction("__dfsan_union_load", DFSanUnionLoadFnTy);
	if (Function *F = dyn_cast<Function>(DFSanUnionLoadFn)) {
		F->addAttribute(AttributeList::FunctionIndex, Attribute::NoUnwind);
		F->addAttribute(AttributeList::FunctionIndex, Attribute::ReadOnly);
		F->addAttribute(AttributeList::ReturnIndex, Attribute::ZExt);
	}
	DFSanUnimplementedFn =
			Mod->getOrInsertFunction("__dfsan_unimplemented", DFSanUnimplementedFnTy);
	DFSanSetLabelFn =
			Mod->getOrInsertFunction("__dfsan_set_label", DFSanSetLabelFnTy);
	if (Function *F = dyn_cast<Function>(DFSanSetLabelFn)) {
		F->addParamAttr(0, Attribute::ZExt);
	}
	DFSanNonzeroLabelFn =
			Mod->getOrInsertFunction("__dfsan_nonzero_label", DFSanNonzeroLabelFnTy);
	DFSanVarargWrapperFn = Mod->getOrInsertFunction("__dfsan_vararg_wrapper",
			DFSanVarargWrapperFnTy);
	DFSanLogTaintFn =
			Mod->getOrInsertFunction("__dfsan_log_taint", DFSanLogTaintFnTy);
	DFSanLogCmpFn =
			Mod->getOrInsertFunction("__dfsan_log_taint_cmp", DFSanLogCmpFnTy);
	DFSanLogInstFn =
			Mod->getOrInsertFunction("__dfsan_test_fn", DFSanLogInstFnTy);
	DFSanEntryFn = Mod->getOrInsertFunction("__dfsan_func_entry", DFSanEntryFnTy);
	DFSanExitFn = Mod->getOrInsertFunction("__dfsan_func_exit", DFSanExitFnTy);
	DFSanEntryBBFn =
			Mod->getOrInsertFunction("__dfsan_bb_entry", DFSanEntryBBFnTy);
	DFSanExitBBFn = Mod->getOrInsertFunction("__dfsan_bb_exit", DFSanExitBBFnTy);
	DFSanResetFrameFn =
			Mod->getOrInsertFunction("__dfsan_reset_frame", DFSanResetFrameFnTy);
}
void DataFlowSanitizer::collectFunctions(std::vector<Function*> &FnsToInstrument, Module& M) {
	for (Function &i : M) {
		if (!i.isIntrinsic() && &i != DFSanUnionFn && &i != DFSanCheckedUnionFn &&
				&i != DFSanUnionLoadFn && &i != DFSanUnimplementedFn &&
				&i != DFSanSetLabelFn && &i != DFSanNonzeroLabelFn &&
				&i != DFSanVarargWrapperFn && &i != DFSanLogTaintFn &&
				&i != DFSanLogCmpFn && &i != DFSanEntryFn && &i != DFSanExitFn &&
				&i != DFSanResetFrameFn && &i != DFSanLogInstFn)
			FnsToInstrument.push_back(&i);
	}

	// Give function aliases prefixes when necessary, and build wrappers where the
	// instrumentedness is inconsistent.
	for (Module::alias_iterator i = M.alias_begin(), e = M.alias_end(); i != e;) {
		GlobalAlias *GA = &*i;
		++i;
		// Don't stop on weak.  We assume people aren't playing games with the
		// instrumentedness of overridden weak aliases.
		if (auto F = dyn_cast<Function>(GA->getBaseObject())) {
			bool GAInst = isInstrumented(GA), FInst = isInstrumented(F);
			if (GAInst && FInst) {
				addGlobalNamePrefix(GA);
			} else if (GAInst != FInst) {
				// Non-instrumented alias of an instrumented function, or vice versa.
				// Replace the alias with a native-ABI wrapper of the aliasee.  The pass
				// below will take care of instrumenting it.
				Function *NewF =
						buildWrapperFunction(F, "", GA->getLinkage(), F->getFunctionType());
				GA->replaceAllUsesWith(ConstantExpr::getBitCast(NewF, GA->getType()));
				NewF->takeName(GA);
				GA->eraseFromParent();
				FnsToInstrument.push_back(NewF);
			}
		}
	}
}

void DataFlowSanitizer::collectBasicBlocks(std::vector<BasicBlock*>& BasicBlocks, Module& M) {

}

bool DataFlowSanitizer::runOnModule(Module &M) {
	if (ABIList.isIn(M, "skip")) {
		return false;
	}
	insertRuntimeFunctions();

	std::vector<Function *> FnsToInstrument;
	SmallPtrSet<Function *, 2> FnsWithNativeABI;
	for (Function &i : M) {
		if (!i.isIntrinsic() && &i != DFSanUnionFn && &i != DFSanCheckedUnionFn &&
				&i != DFSanUnionLoadFn && &i != DFSanUnimplementedFn &&
				&i != DFSanSetLabelFn && &i != DFSanNonzeroLabelFn &&
				&i != DFSanVarargWrapperFn && &i != DFSanLogTaintFn &&
				&i != DFSanLogCmpFn && &i != DFSanEntryFn && &i != DFSanExitFn &&
				&i != DFSanEntryBBFn && &i != DFSanExitBBFn && &i != DFSanResetFrameFn)
			FnsToInstrument.push_back(&i);
	}

	// Give function aliases prefixes when necessary, and build wrappers where the
	// instrumentedness is inconsistent.
	for (Module::alias_iterator i = M.alias_begin(), e = M.alias_end(); i != e;) {
		GlobalAlias *GA = &*i;
		++i;
		// Don't stop on weak.  We assume people aren't playing games with the
		// instrumentedness of overridden weak aliases.
		if (auto F = dyn_cast<Function>(GA->getBaseObject())) {
			bool GAInst = isInstrumented(GA), FInst = isInstrumented(F);
			if (GAInst && FInst) {
				addGlobalNamePrefix(GA);
			} else if (GAInst != FInst) {
				// Non-instrumented alias of an instrumented function, or vice versa.
				// Replace the alias with a native-ABI wrapper of the aliasee.  The pass
				// below will take care of instrumenting it.
				Function *NewF =
						buildWrapperFunction(F, "", GA->getLinkage(), F->getFunctionType());
				GA->replaceAllUsesWith(ConstantExpr::getBitCast(NewF, GA->getType()));
				NewF->takeName(GA);
				GA->eraseFromParent();
				FnsToInstrument.push_back(NewF);
			}
		}
	}

	ReadOnlyNoneAttrs.addAttribute(Attribute::ReadOnly)
    				  .addAttribute(Attribute::ReadNone);

	// First, change the ABI of every function in the module.  ABI-listed
	// functions keep their original ABI and get a wrapper function.
	for (std::vector<Function *>::iterator i = FnsToInstrument.begin(),
			e = FnsToInstrument.end();
			i != e; ++i) {
		Function &F = **i;
		FunctionType *FT = F.getFunctionType();

		bool IsZeroArgsVoidRet = (FT->getNumParams() == 0 && !FT->isVarArg() &&
				FT->getReturnType()->isVoidTy());

		if (isInstrumented(&F)) {
			// Instrumented functions get a 'dfs$' prefix.  This allows us to more
			// easily identify cases of mismatching ABIs.
			if (getInstrumentedABI() == IA_Args && !IsZeroArgsVoidRet) {
				FunctionType *NewFT = getArgsFunctionType(FT);
				Function *NewF = Function::Create(NewFT, F.getLinkage(), "", &M);
				NewF->copyAttributesFrom(&F);
				NewF->removeAttributes(
						AttributeList::ReturnIndex,
						AttributeFuncs::typeIncompatible(NewFT->getReturnType()));
				for (Function::arg_iterator FArg = F.arg_begin(),
						NewFArg = NewF->arg_begin(),
						FArgEnd = F.arg_end();
						FArg != FArgEnd; ++FArg, ++NewFArg) {
					FArg->replaceAllUsesWith(&*NewFArg);
				}
				NewF->getBasicBlockList().splice(NewF->begin(), F.getBasicBlockList());

				for (Function::user_iterator UI = F.user_begin(), UE = F.user_end();
						UI != UE;) {
					BlockAddress *BA = dyn_cast<BlockAddress>(*UI);
					++UI;
					if (BA) {
						BA->replaceAllUsesWith(
								BlockAddress::get(NewF, BA->getBasicBlock()));
						delete BA;
					}
				}
				F.replaceAllUsesWith(
						ConstantExpr::getBitCast(NewF, PointerType::getUnqual(FT)));
				NewF->takeName(&F);
				F.eraseFromParent();
				*i = NewF;
				addGlobalNamePrefix(NewF);
			} else {
				addGlobalNamePrefix(&F);
			}
		}
		// Was !isZeroArgsRetVoid, but when we specify
		// Uninstrumented and Discard we MEAN dont touch
		else if (getWrapperKind(&F) == WK_Custom) {
			// Build a wrapper function for F.  The wrapper simply calls F, and is
			// added to FnsToInstrument so that any instrumentation according to its
			// WrapperKind is done in the second pass below.
			FunctionType *NewFT =
					getInstrumentedABI() == IA_Args ? getArgsFunctionType(FT) : FT;

			// If the function being wrapped has local linkage, then preserve the
			// function's linkage in the wrapper function.
			GlobalValue::LinkageTypes wrapperLinkage =
					F.hasLocalLinkage() ? F.getLinkage()
							: GlobalValue::LinkOnceODRLinkage;

#ifdef DEBUG_INFO
			// Looking for open and reads we might not have hooked
			std::string test_fname = F.getName();
			size_t found_place = test_fname.find("open");
			if (found_place != std::string::npos) {
				std::cout << "Getting OPEN fname " << test_fname << std::endl;
				bool is_custom = getWrapperKind(&F) == WK_Custom;
				std::cout << "Is custom func: " << is_custom << std::endl;
			}
			found_place = test_fname.find("read");
			if (found_place != std::string::npos) {
				std::cout << "Getting READ fname " << test_fname << std::endl;
				bool is_custom = getWrapperKind(&F) == WK_Custom;
				std::cout << "Is custom func: " << is_custom << std::endl;
			}
#endif

			Function *NewF = buildWrapperFunction(
					&F, std::string("dfsw$") + std::string(F.getName()), wrapperLinkage,
					NewFT);
			if (getInstrumentedABI() == IA_TLS)
				NewF->removeAttributes(AttributeList::FunctionIndex, ReadOnlyNoneAttrs);

			Value *WrappedFnCst =
					ConstantExpr::getBitCast(NewF, PointerType::getUnqual(FT));
			F.replaceAllUsesWith(WrappedFnCst);

			UnwrappedFnMap[WrappedFnCst] = &F;
			*i = NewF;

			if (!F.isDeclaration()) {
				// This function is probably defining an interposition of an
				// uninstrumented function and hence needs to keep the original ABI.
				// But any functions it may call need to use the instrumented ABI, so
				// we instrument it in a mode which preserves the original ABI.
				FnsWithNativeABI.insert(&F);

				// This code needs to rebuild the iterators, as they may be invalidated
				// by the push_back, taking care that the new range does not include
				// any functions added by this code.
				size_t N = i - FnsToInstrument.begin(),
						Count = e - FnsToInstrument.begin();
				FnsToInstrument.push_back(&F);
				i = FnsToInstrument.begin() + N;
				e = FnsToInstrument.begin() + Count;
			}
			// Hopefully, nobody will try to indirectly call a vararg
			// function... yet.
		} else if (FT->isVarArg()) {
			UnwrappedFnMap[&F] = &F;
			*i = nullptr;
		}
	}

	uint32_t functionIndex = 0;
	for (Function *i : FnsToInstrument) {
		if (!i || i->isDeclaration())
			continue;

		Value *FuncIndex =
				ConstantInt::get(IntegerType::getInt32Ty(*Ctx), functionIndex++, false);

		removeUnreachableBlocks(*i);

		std::string curr_fname = i->getName();
		if (!(getWrapperKind(i) == WK_Custom || isInstrumented(i))) {
			if (curr_fname != "main") {

#ifdef DEBUG_INFO
				std::cout << "SKIPPING: " << curr_fname << std::endl;
#endif
				continue;
			} else {
#ifdef DEBUG_INFO
				std::cout << "ADDING ENTRY: " << curr_fname << std::endl;
#endif
			}
		}
		// Instrument function entry here
		BasicBlock *BB = &(i->getEntryBlock());
		Instruction *InsertPoint = &(*(BB->getFirstInsertionPt()));
		IRBuilder<> IRB(InsertPoint);
		Value *FuncName = IRB.CreateGlobalStringPtr(i->getName());
		Value *FrameIndex = IRB.CreateAlloca(IntegerType::getInt64Ty(*Ctx));
		auto store_inst =
				IRB.CreateStore(IRB.CreateCall(DFSanEntryFn, FuncName), FrameIndex);

#ifdef DEBUG_INFO
		llvm::errs() << "INSTRUMENTING " + i->getName() + " FUNCTION ENTRY!\n";
		if (i->getName().find("is_equal") != std::string::npos) {
		}
#endif
		DFSanFunction DFSF(*this, i, FnsWithNativeABI.count(i));

		// DFSanVisitor may create new basic blocks, which confuses df_iterator.
		// Build a copy of the list before iterating over it.
		SmallVector<BasicBlock *, 4> BBList(depth_first(&i->getEntryBlock()));

		for (BasicBlock *i : BBList) {
			Instruction *Inst = &i->front();
			while (true) {
				// DFSanVisitor may split the current basic block, changing the current
				// instruction's next pointer and moving the next instruction to the
				// tail block from which we should continue.
				Instruction *Next = Inst->getNextNode();
				// DFSanVisitor may delete Inst, so keep track of whether it was a
				// terminator.
				bool IsTerminator = isa<TerminatorInst>(Inst);
				if (!DFSF.SkipInsts.count(Inst))
					DFSanVisitor(DFSF).visit(Inst);
				if (IsTerminator)
					break;
				Inst = Next;
			}
		}
		// Add instrumentation for handling setjmp/longjmp here
		// This adds a function that resets the shadow call stack
		// When a longjmp is called.
		uint32_t bbIndex = 0;
		for (BasicBlock *curr_bb : BBList) {
			Instruction *Inst = &curr_bb->front();

			// Add a callback for BB entry
			{
				Value *BBIndex =
						ConstantInt::get(IntegerType::getInt32Ty(*Ctx), bbIndex++, false);
				Instruction *InsertBefore = Inst;
				while (isa<PHINode>(InsertBefore) ||
						isa<LandingPadInst>(InsertBefore)) {
					// This is a PHI or landing pad instruction,
					// so we need to add the callback afterward
					InsertBefore = InsertBefore->getNextNode();
				}
				IRBuilder<> IRB(InsertBefore);
				basic_block_id_map[curr_bb] = BBIndex;
				IRB.CreateCall(DFSanEntryBBFn, {FuncName, FuncIndex, BBIndex});
			}
			while (true) {
				Instruction *Next = Inst->getNextNode();
				CallInst *potential_call = dyn_cast<CallInst>(Inst);
				if (potential_call != nullptr) {
					Function *F = potential_call->getCalledFunction();
					if (F != nullptr) {
						if (F->getName() == "setjmp" || F->getName() == "sigsetjump" ||
								F->getName() == "_setjmp") {
							// Insert before the next inst.
							IRBuilder<> IRB(Next);
							IRB.CreateCall(DFSanResetFrameFn, FrameIndex);
						}
					}
				}
				bool IsTerminator = isa<TerminatorInst>(Inst);
				if (IsTerminator)
					break;
				Inst = Next;
			}
			IRBuilder<>(Inst).CreateCall(DFSanExitBBFn);
		}

		// We will not necessarily be able to compute the shadow for every phi node
		// until we have visited every block.  Therefore, the code that handles phi
		// nodes adds them to the PHIFixups list so that they can be properly
		// handled here.
		for (std::vector<std::pair<PHINode *, PHINode *>>::iterator
				i = DFSF.PHIFixups.begin(),
				e = DFSF.PHIFixups.end();
				i != e; ++i) {
			for (unsigned val = 0, n = i->first->getNumIncomingValues(); val != n;
					++val) {
				i->second->setIncomingValue(
						val, DFSF.getShadow(i->first->getIncomingValue(val)));
			}
		}

		// -dfsan-debug-nonzero-labels will split the CFG in all kinds of crazy
		// places (i.e. instructions in basic blocks we haven't even begun visiting
		// yet).  To make our life easier, do this work in a pass after the main
		// instrumentation.
		if (ClDebugNonzeroLabels) {
			for (Value *V : DFSF.NonZeroChecks) {
				Instruction *Pos;
				if (Instruction *I = dyn_cast<Instruction>(V))
					Pos = I->getNextNode();
				else
					Pos = &DFSF.F->getEntryBlock().front();
				while (isa<PHINode>(Pos) || isa<AllocaInst>(Pos))
					Pos = Pos->getNextNode();
				IRBuilder<> IRB(Pos);
				Value *Ne = IRB.CreateICmpNE(V, DFSF.DFS.ZeroShadow);
				BranchInst *BI = cast<BranchInst>(SplitBlockAndInsertIfThen(
						Ne, Pos, /*Unreachable=*/false, ColdCallWeights));
				IRBuilder<> ThenIRB(BI);
				ThenIRB.CreateCall(DFSF.DFS.DFSanNonzeroLabelFn, {});
			}
		}
	}

	return false;
}


Value *DataFlowSanitizer::getShadowAddress(Value *Addr, Instruction *Pos) {
	assert(Addr != RetvalTLS && "Reinstrumenting?");
	IRBuilder<> IRB(Pos);
	Value *ShadowPtrMaskValue;
	if (DFSanRuntimeShadowMask)
		ShadowPtrMaskValue = IRB.CreateLoad(IntptrTy, ExternalShadowMask);
	else
		ShadowPtrMaskValue = ShadowPtrMask;
	return IRB.CreateIntToPtr(
			IRB.CreateMul(
					IRB.CreateAnd(IRB.CreatePtrToInt(Addr, IntptrTy),
							IRB.CreatePtrToInt(ShadowPtrMaskValue, IntptrTy)),
							ShadowPtrMul),
							ShadowPtrTy);
}


static RegisterPass<DataFlowSanitizer> X("dfsan_pass", "DataflowSan Pass");

static void registerAflDFSanPass(const PassManagerBuilder &,
		legacy::PassManagerBase &PM) {

	PM.add(new DataFlowSanitizer());
}

static RegisterStandardPasses
RegisterAflDFSanPass(PassManagerBuilder::EP_OptimizerLast,
		registerAflDFSanPass);

static RegisterStandardPasses
RegisterAflDFSanPass0(PassManagerBuilder::EP_EnabledOnOptLevel0,
		registerAflDFSanPass);
