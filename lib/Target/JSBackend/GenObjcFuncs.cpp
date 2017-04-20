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
    ObjcFunction(std::string Name, FunctionType *MessageFunctionType) :Name(Name), MessageFunctionType(MessageFunctionType) {};
    ObjcFunction(const ObjcFunction& other) :Name(other.Name), MessageFunctionType(other.MessageFunctionType) {};
    ~ObjcFunction() {};

    bool operator<(const ObjcFunction &right) const {return getFullName() < right.getFullName();}
    std::string getFullName(void) const;
    std::string getSignature(void) const;

    static char getFunctionSignatureLetter(Type *T);
    static bool isObjcFunction(std::string &Name);
    Function *generateFunction(Module &M);
  protected:
    std::string Name;
    FunctionType *MessageFunctionType;
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

  // 1. funcs -> generate Function
  // 2. replace CI's CalledValue with generated Fucntion
  // 3. erase old functions
  return false;
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

Function *ObjcFunction::generateFunction(Module &M) {
  Function* Func = Function::Create(MessageFunctionType, GlobalValue::InternalLinkage, getFullName(), &M);

  BasicBlock *EntryBB = BasicBlock::Create(Func->getContext(), "", Func);
  BasicBlock *L5BB    = BasicBlock::Create(Func->getContext(), "L5", Func);
  BasicBlock *L10BB   = BasicBlock::Create(Func->getContext(), "L10", Func);
  BasicBlock *L12BB   = BasicBlock::Create(Func->getContext(), "L12", Func);
  BasicBlock *L14BB   = BasicBlock::Create(Func->getContext(), "L14", Func);
  BasicBlock *L17BB   = BasicBlock::Create(Func->getContext(), "L17", Func);
  BasicBlock *L19BB   = BasicBlock::Create(Func->getContext(), "L19", Func);

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

  errs() << "In function " << CI->getParent()->getParent()->getName() << "()\n";

  ObjcFunction function(Name, CS.getFunctionType());

  funcs[function].push_back(CI);

  errs() << function.getFullName() << "\n";
}


ModulePass *llvm::createGenObjcFuncsPass() {
  return new GenObjcFuncs();
}
