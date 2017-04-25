//===- GenObjcFuncs.cpp - Generate objc message functions -------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===------------------------------------------------------------------===//
//
//===------------------------------------------------------------------===//

#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/IR/CFG.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Transforms/NaCl.h"
#include "llvm/Transforms/Utils/Local.h"
#include <map>

#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace {
  const std::string OBJC_MSG_SEND("objc_msgSend");
  const std::string OBJC_MSG_SEND_SUPER("objc_msgSendSuper");
  const std::string OBJC_MSG_SEND_SUPER2("objc_msgSendSuper2");
  const std::string OBJC_METHOD_INVOKE("method_invoke");

  class GenObjcFuncs : public ModulePass {
  public:
    static char ID;
    GenObjcFuncs() : ModulePass(ID) {
      initializeGenObjcFuncsPass(*PassRegistry::getPassRegistry());
    }

    virtual bool runOnModule(Module &M);
  };

  class ObjcFunction {
  public:
    ObjcFunction(std::string Name, FunctionType *MessageFunctionType, Module *M);
    ObjcFunction(const ObjcFunction& other) :Name(other.Name), MessageFunctionType(other.MessageFunctionType) {};
    ~ObjcFunction() {};

    bool operator<(const ObjcFunction &right) const {return getFullName() < right.getFullName();}
    std::string getFullName(void) const;
    std::string getSignature(void) const;
    bool isObjcFunction(void) const;
    bool isObjcMsgSend(void) const;
    bool isObjcMsgSendSuper(void) const;
    bool isObjcMsgSendSuper2(void) const;
    bool isMethodInvoke(void) const;
    bool isStret(void) const;
    Function *getCacheGetImpFunction(Module &M);
    Function *getLookupMethodAndLoadCache3Functions(Module &M);
    Function *getForwardingFunction(Module &M);
    Function *getAbortFunction(Module &M);

    static char getFunctionSignatureLetter(Type *T);
    static bool isObjcFunction(std::string &Name);
    Function *generateFunction(Module &M);
  private:
    std::string Name;
    FunctionType *MessageFunctionType;
    Function *generateMsgSendFunction(Module &M);
    Function *generateMethodInvokeFunction(Module &M);
  };

  class ObjcCallVisitor: public InstVisitor<ObjcCallVisitor> {
  public:
    ObjcCallVisitor(std::map<ObjcFunction, std::vector<Instruction*>> &funcs) :funcs(funcs) {};

    void visitCallInst(CallInst &CI);
    void visitInvokeInst(InvokeInst &I);

    void handleCall(Instruction *CI);
  private:
    std::map<ObjcFunction, std::vector<Instruction*>> &funcs;
  };
}

char GenObjcFuncs::ID = 0;
INITIALIZE_PASS(GenObjcFuncs, "generate-objc-message-function",
                "Generate objective-c message functions",
                false, false)

bool GenObjcFuncs::runOnModule(Module &M) {
  std::map<ObjcFunction, std::vector<Instruction*>> funcs;
  ObjcCallVisitor visitor(funcs);
  visitor.visit(M);

  for(auto I = funcs.begin(), E = funcs.end(); I != E; ++I) {
    ObjcFunction func = I->first;
    Function *F = func.generateFunction(M);
    std::vector<Instruction*> Instructions = I->second;
    for(auto CI = Instructions.begin(), CE = Instructions.end(); CI != CE; ++CI) {
      CallSite CS(*CI);
      CS.setCalledFunction(F);
    }
  }

  // TODO erase old functions
  return true;
}

ObjcFunction::ObjcFunction(std::string Name, FunctionType *FT, Module *M) :Name(Name) {
  Type *I8 = Type::getInt8PtrTy(M->getContext());

  SmallVector<Type*, 10> Args;
  int i = 0;
  for(auto I = FT->param_begin(), E = FT->param_end(); I != E; ++i, ++I) {
    Type *T = *I;

    // keep objcSuper
    bool keep = false;
    if(isObjcMsgSendSuper() || isObjcMsgSendSuper2()) {
      if(!isStret() && i == 0) keep = true;
      if(isStret() && i == 1) keep = true;
    }

    if(!keep && T->isPointerTy()) {
      Args.push_back(I8);
    } else {
      Args.push_back(T);
    }
  }

  MessageFunctionType = FunctionType::get(FT->getReturnType(), Args, false);
}

std::string ObjcFunction::getFullName(void) const {
  return Name + "_" + getSignature();
}

std::string ObjcFunction::getSignature(void) const {
  std::string Sig;
  Sig = getFunctionSignatureLetter(MessageFunctionType->getReturnType());
  for(auto iter = MessageFunctionType->param_begin(); iter != MessageFunctionType->param_end(); ++iter) {
    Type *T = *iter;
    Sig += ObjcFunction::getFunctionSignatureLetter(T);
  }
  return Sig;
}

char ObjcFunction::getFunctionSignatureLetter(Type *T) {
  if (T->isVoidTy()) return 'v';
  else if (T->isFloatingPointTy()) {
    if (T->isFloatTy()) {
      return 'f';
    } else {
      return 'd';
    }
  } else if (T->isIntegerTy()) {
    if(T->getIntegerBitWidth() == 64) {
      return 'j';
    } else {
      return 'i';
    }
  } else if(T->isPointerTy()){
    return 'i';
  } else {
    errs() << "*** Unsupported type!\n";
    T->dump();
    return 'x';
  }
}

bool ObjcFunction::isObjcFunction(std::string &Name) {
  return Name.compare(0, OBJC_MSG_SEND.length(), OBJC_MSG_SEND) == 0
    || Name.compare(0, OBJC_MSG_SEND_SUPER.length(), OBJC_MSG_SEND_SUPER) == 0
    || Name.compare(0, OBJC_MSG_SEND_SUPER2.length(), OBJC_MSG_SEND_SUPER2) == 0
    || Name.compare(0, OBJC_METHOD_INVOKE.length(), OBJC_METHOD_INVOKE) == 0;
}


bool ObjcFunction::isObjcMsgSend(void) const {
  return Name == OBJC_MSG_SEND || Name == (OBJC_MSG_SEND+"_stret");
}

bool ObjcFunction::isObjcMsgSendSuper(void) const {
  return Name == OBJC_MSG_SEND_SUPER || Name == (OBJC_MSG_SEND_SUPER+"_stret");
}

bool ObjcFunction::isObjcMsgSendSuper2(void) const {
  return Name == OBJC_MSG_SEND_SUPER2 || Name == (OBJC_MSG_SEND_SUPER2+"_stret");
}

bool ObjcFunction::isMethodInvoke(void) const {
  return Name == OBJC_METHOD_INVOKE || Name == (OBJC_METHOD_INVOKE+"_stret");
}

bool ObjcFunction::isStret(void) const {
  return Name.find("_stret") != std::string::npos;
}

Function *ObjcFunction::getCacheGetImpFunction(Module &M) {
  auto F = M.getFunction("cache_getImp");
  if(!F) {
    Type *I8 = Type::getInt8PtrTy(M.getContext());
    Type *Args[] = { I8, I8 };
    auto VoidFuncType = FunctionType::get(Type::getVoidTy(M.getContext()), false);
    auto CacheGetImpFuncType = FunctionType::get(PointerType::getUnqual(VoidFuncType), Args, false);
    F = Function::Create(CacheGetImpFuncType, GlobalValue::ExternalLinkage, "cache_getImp", &M);
  }
  return F;
}

Function *ObjcFunction::getLookupMethodAndLoadCache3Functions(Module &M) {
  auto F = M.getFunction("_class_lookupMethodAndLoadCache3");
  if(!F) {
    Type *I8 = Type::getInt8PtrTy(M.getContext());
    Type *Args[] = { I8, I8, I8 };
    auto VoidFuncType = FunctionType::get(Type::getVoidTy(M.getContext()), false);
    auto LookupFuncType = FunctionType::get(PointerType::getUnqual(VoidFuncType), Args, false);
    F = Function::Create(LookupFuncType, GlobalValue::ExternalLinkage, "_class_lookupMethodAndLoadCache3", &M);
  }
  return F;
}

Function *ObjcFunction::getForwardingFunction(Module &M) {
  auto F = M.getFunction("__forwarding__");
  if(!F) {
    Type *I8 = Type::getInt8PtrTy(M.getContext());
    Type *Args[] = { I8, I8 };
    auto CacheGetImpFuncType = FunctionType::get(I8, Args, false);
    F = Function::Create(CacheGetImpFuncType, GlobalValue::ExternalLinkage, "__forwarding__", &M);
  }
  return F;
}

Function *ObjcFunction::getAbortFunction(Module &M) {
  auto F = M.getFunction("abort");
  if(!F) {
    auto VoidFuncType = FunctionType::get(Type::getVoidTy(M.getContext()), false);
    F = Function::Create(VoidFuncType, GlobalValue::ExternalLinkage, "abort", &M);
    F->addFnAttr(Attribute::NoReturn);
  }
  return F;
}

Function *ObjcFunction::generateFunction(Module &M) {
  if(isMethodInvoke()) {
    return generateMethodInvokeFunction(M);
  } else {
    return generateMsgSendFunction(M);
  }
}

Function *ObjcFunction::generateMsgSendFunction(Module &M) {
  Function* Func = Function::Create(MessageFunctionType, GlobalValue::InternalLinkage, getFullName(), &M);

  // common Type
  Type *I32 = Type::getInt32Ty(Func->getContext());
  Type *ReturnType = MessageFunctionType->getReturnType();
  Value *Index1[] = {ConstantInt::get(I32, 1)};
  Value *Index00[] = {ConstantInt::get(I32, 0), ConstantInt::get(I32, 0)};
  Value *Index01[] = {ConstantInt::get(I32, 0), ConstantInt::get(I32, 1)};
  bool isVoidReturn = ReturnType->isVoidTy();

  // Prepare blocks
  BasicBlock *EntryBB = BasicBlock::Create(Func->getContext(), "", Func);
  BasicBlock *CacheBB = BasicBlock::Create(Func->getContext(), "Cache", Func);
  BasicBlock *LookupBB = BasicBlock::Create(Func->getContext(), "Lookup", Func);
  BasicBlock *CheckBB = BasicBlock::Create(Func->getContext(), "Check", Func);
  BasicBlock *CallBB = BasicBlock::Create(Func->getContext(), "Call", Func);
  BasicBlock *ForwardBB = BasicBlock::Create(Func->getContext(), "Foward", Func);
  BasicBlock *RetargetBB = BasicBlock::Create(Func->getContext(), "Retarget", Func);
  BasicBlock *ForwardReturnBB = isVoidReturn ? nullptr : BasicBlock::Create(Func->getContext(), "ForwardReturn", Func);
  BasicBlock *ReturnBB = BasicBlock::Create(Func->getContext(), "Return", Func);


  // Setup arguments
  SmallVector<Value*, 10> Args;
  for(auto &Arg: Func->args()) {
    Arg.setName("arg");
    Args.push_back(&Arg);
  }

  auto ArgIter = Func->arg_begin();
  Argument *FisrtArg = &*ArgIter++;
  Argument *SecondArg = &*ArgIter++;
  Argument *ThirdArg = isStret() ? &*ArgIter : nullptr;

  Value *Self, *ObjcSuper, *StAddr, *Sel;

  if(isObjcMsgSend()) {
    if(!isStret()) {
      FisrtArg->setName("self");
      SecondArg->setName("sel");
      Self = FisrtArg;
      Sel = SecondArg;
    } else {
      FisrtArg->setName("staddr");
      SecondArg->setName("self");
      ThirdArg->setName("sel");
      StAddr = FisrtArg;
      Self = SecondArg;
      Sel = ThirdArg;
    }
  } else { // Super or Super2
    if(!isStret()) {
      FisrtArg->setName("objcSuper");
      SecondArg->setName("sel");
      ObjcSuper = FisrtArg;
      Sel = SecondArg;
    } else {
      FisrtArg->setName("staddr");
      SecondArg->setName("objcSuper");
      ThirdArg->setName("sel");
      StAddr = FisrtArg;
      ObjcSuper = SecondArg;
      Sel = ThirdArg;
    }
  }

  // Function body

  // check self is not null
  if(isObjcMsgSend()) {
    auto SelfIsNull = new ICmpInst(*EntryBB, CmpInst::ICMP_EQ, Self, ConstantInt::get(I32, 0), "self_is_null");
    BranchInst::Create(ReturnBB, CacheBB, SelfIsNull, EntryBB);
  } else {
    BranchInst::Create(CacheBB, EntryBB);
  }

  // get class
  Value *Cls;
  if(isObjcMsgSend()) {
    auto SelfIsa = new BitCastInst(Self, PointerType::getUnqual(Self->getType()), "self.isa", CacheBB);
    Cls = new LoadInst(SelfIsa, "cls", CacheBB);
  } else if(isObjcMsgSendSuper()) {
    auto ObjcSuperSelf = GetElementPtrInst::CreateInBounds(ObjcSuper, Index00, "objcSuper.self", CacheBB);
    Self = new LoadInst(ObjcSuperSelf, "self", CacheBB);

    auto ObjcSuperCls = GetElementPtrInst::CreateInBounds(ObjcSuper, Index01, "objcSuper.cls", CacheBB);
    Cls = new LoadInst(ObjcSuperCls, "supercls", CacheBB);
  } else if(isObjcMsgSendSuper2()) {
    auto ObjcSuperSelf = GetElementPtrInst::CreateInBounds(ObjcSuper, Index00, "objcSuper.self", CacheBB);
    Self = new LoadInst(ObjcSuperSelf, "self", CacheBB);

    auto ObjcSuperCls = GetElementPtrInst::CreateInBounds(ObjcSuper, Index01, "objcSuper.cls", CacheBB);
    auto MyClsAddr = new BitCastInst(ObjcSuperCls, PointerType::getUnqual(ObjcSuperCls->getType()), "cls_addr", CacheBB);
    auto MyCls = new LoadInst(MyClsAddr, "cls", CacheBB);

    auto SuperClsAddr = GetElementPtrInst::CreateInBounds(MyCls, Index1, "cls.super", CacheBB);
    Cls = new LoadInst(SuperClsAddr, "supercls", CacheBB);
  } else {
    llvm_unreachable("Unexpected function type");
  }

  // call cache_getImp
  auto CacheGetImpFunc = getCacheGetImpFunction(M);
  Value *CacheGetImpArgs[] = { Cls, Sel };
  auto CacheImp = CallInst::Create(CacheGetImpFunc, CacheGetImpArgs, "cache_imp", CacheBB);
  auto CacheImpIsNull = new ICmpInst(*CacheBB, CmpInst::ICMP_EQ, CacheImp, ConstantInt::get(I32, 0), "cache_imp_is_null");
  BranchInst::Create(LookupBB, CheckBB, CacheImpIsNull, CacheBB);

  // call _class_lookupMethodAndLoadCache3
  auto LookupFunc = getLookupMethodAndLoadCache3Functions(M);
  Value *LookupArgs[] = { Self, Sel, Cls };
  auto LookupImp = CallInst::Create(LookupFunc, LookupArgs, "lookup_imp", LookupBB);
  BranchInst::Create(CheckBB, LookupBB);

  // check imp is not negative
  auto Imp = PHINode::Create(CacheImp->getType(), 2, "imp", CheckBB);
  Imp->addIncoming(CacheImp, CacheBB);
  Imp->addIncoming(LookupImp, LookupBB);
  auto ImpIsZeroOrPositive = new ICmpInst(*CheckBB, CmpInst::ICMP_SGT, Imp, ConstantInt::get(I32, -1), "imp_ge_zero");
  BranchInst::Create(CallBB, ForwardBB, ImpIsZeroOrPositive, CheckBB);

  // call actual function
  auto ActualFunc = new BitCastInst(Imp, PointerType::getUnqual(MessageFunctionType), "actual_func", CallBB);
  SmallVector<Value*, 10> ActualArgs(Args);
  if(!isObjcMsgSend()) {
    if(!isStret()) {
      ActualArgs[0] = Self;
    } else {
      ActualArgs[1] = Self;
    }
  }
  auto CallRet = CallInst::Create(ActualFunc, ActualArgs, "call_ret", CallBB);
  BranchInst::Create(ReturnBB, CallBB);

  // forward to method missing
  // not stret: margs = args, return_storage = margs
  // stret: margs = args.slice(1), return_storage = staddr(= args[0])
  auto Margs = new AllocaInst(ArrayType::get(Self->getType(), isStret() ? ActualArgs.size()-1 : ActualArgs.size()), "margs", ForwardBB);
  Value *ReturnStorage;
  auto ForwardArgBegin = ActualArgs.begin();
  if(!isStret()) {
    ReturnStorage = GetElementPtrInst::CreateInBounds(Margs, Index00, "return_storage", ForwardBB);
  } else {
    ReturnStorage = StAddr;
    ForwardArgBegin++;
  }
  int i = 0;
  for(Value *Arg: SmallVector<Value*,0>(ForwardArgBegin, ActualArgs.end())) {
    Value *Indexes[] = {ConstantInt::get(I32, 0), ConstantInt::get(I32, i)};
    auto Ptr = GetElementPtrInst::CreateInBounds(Margs, Indexes, "ptr", ForwardBB);
    new StoreInst(Arg, Ptr, ForwardBB);
    i++;
  }
  auto ForwardingFunc = getForwardingFunction(M);
  Value *ForwardingArgs[] = {Margs, ReturnStorage};
  auto Target = CallInst::Create(ForwardingFunc, ForwardingArgs, "target", ForwardBB);
  auto TargetIsNull = new ICmpInst(*ForwardBB, CmpInst::ICMP_EQ, Target, ConstantInt::get(I32, 0), "target_is_null");
  BranchInst::Create(isVoidReturn ? ReturnBB : ForwardReturnBB, RetargetBB, TargetIsNull, ForwardBB);

  // Call objc_msgSend with setting target as self
  // TODO implement
  auto AbortFunc = getAbortFunction(M);
  CallInst::Create(AbortFunc, "", RetargetBB);
  new UnreachableInst(Func->getContext(), RetargetBB);

  if(!isVoidReturn) {
    // return forward result
    auto ForwardRetAddr = new BitCastInst(ReturnStorage, PointerType::getUnqual(ReturnType), "forward_ret_addr", ForwardReturnBB);
    auto ForwardRet = new LoadInst(ForwardRetAddr, "forward_ret", ForwardReturnBB);
    BranchInst::Create(ReturnBB, ForwardReturnBB);

    // return
    auto Ret = PHINode::Create(ReturnType, 3, "ret", ReturnBB);

    Type *T = ReturnType;

    Value *ZeroValue;
    if (T->isFloatingPointTy()) {
      ZeroValue = ConstantFP::get(T, 0.0);
    } else if (T->isIntegerTy()) {
      ZeroValue = ConstantInt::get(T, 0);
    } else {
      ZeroValue = ConstantInt::get(I32, 0);
    }
    Ret->addIncoming(ZeroValue, EntryBB);
    Ret->addIncoming(CallRet, CallBB);
    Ret->addIncoming(ForwardRet, ForwardReturnBB);
    ReturnInst::Create(Func->getContext(), Ret, ReturnBB);
  } else {
    ReturnInst::Create(Func->getContext(), ReturnBB);
  }
  // Func->dump();
  return Func;
}

Function *ObjcFunction::generateMethodInvokeFunction(Module &M) {
  Function* Func = Function::Create(MessageFunctionType, GlobalValue::InternalLinkage, getFullName(), &M);

  bool isVoidReturn = MessageFunctionType->getReturnType()->isVoidTy();

  BasicBlock *BB = BasicBlock::Create(Func->getContext(), "", Func);

  SmallVector<Value*, 10> Args;
  for(auto &Arg: Func->args()) {
    Arg.setName("arg");
    Args.push_back(&Arg);
  }
  auto ArgIter = Func->arg_begin();
  Argument *FisrtArg = &*ArgIter++;
  Argument *SecondArg = &*ArgIter++;
  Argument *ThirdArg = isStret() ? &*ArgIter : nullptr;

  Value *Method;
  if(!isStret()) {
    FisrtArg->setName("self");
    SecondArg->setName("method");
    Method = SecondArg;
  } else {
    FisrtArg->setName("staddr");
    SecondArg->setName("self");
    ThirdArg->setName("method");
    Method = ThirdArg;
  }
  Type *I8 = Type::getInt8PtrTy(Func->getContext());
  auto Meth = new BitCastInst(Method, PointerType::getUnqual(I8), "method.sel", BB);
  auto Sel = new LoadInst(Meth, "sel", BB);
  assert(Sel);

  Type *I32 = Type::getInt32Ty(Func->getContext());
  Value *Index2[] = {ConstantInt::get(I32, 2)};
  auto ImpAddr = GetElementPtrInst::CreateInBounds(Meth, Index2, "method.imp", BB);
  auto Imp = new LoadInst(ImpAddr, "imp", BB);
  assert(Imp);

  SmallVector<Value*, 10> InvokeArgs(Args);
  SmallVector<Type*, 10> InvokeArgTypes(MessageFunctionType->param_begin(), MessageFunctionType->param_end());
  if(!isStret()) {
    InvokeArgs[1] = Sel;
    InvokeArgTypes[1] = Sel->getType();
  } else {
    InvokeArgs[2] = Sel;
    InvokeArgTypes[2] = Sel->getType();
  }

  auto InvokedFunc = new BitCastInst(Imp, PointerType::getUnqual(FunctionType::get(MessageFunctionType->getReturnType(), InvokeArgTypes, false)), "func", BB);
  auto Ret = CallInst::Create(InvokedFunc, InvokeArgs, "ret", BB);
  if(!isVoidReturn) {
    ReturnInst::Create(Func->getContext(), Ret, BB);
  } else {
    ReturnInst::Create(Func->getContext(), BB);
  }
  return Func;
}

void ObjcCallVisitor::visitCallInst(CallInst &CI) {
  handleCall(&CI);
}

void ObjcCallVisitor::visitInvokeInst(InvokeInst &I) {
  handleCall(&I);
}

void ObjcCallVisitor::handleCall(Instruction *CI) {
  CallSite CS(CI);
  const Value *CV = CS.getCalledValue();
  const Function *F = dyn_cast<const Function>(CV);
  if(!F) {
    CV = CV->stripPointerCasts();
    F = dyn_cast<const Function>(CV);
  }
  if(!F) {
    return;
  }

  std::string Name = F->getName();
  if(!ObjcFunction::isObjcFunction(Name)) return;

  ObjcFunction function(Name, CS.getFunctionType(), CI->getParent()->getModule());

  funcs[function].push_back(CI);
}


ModulePass *llvm::createGenObjcFuncsPass() {
  return new GenObjcFuncs();
}
