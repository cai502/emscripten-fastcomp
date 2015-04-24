//===-- JSTargetMachine.cpp - Define TargetMachine for the JS -------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file defines the JS specific subclass of TargetMachine.
//
//===----------------------------------------------------------------------===//

#include "JSTargetMachine.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/PassManager.h"
using namespace llvm;

JSTargetMachine::JSTargetMachine(const Target &T, StringRef Triple,
                                 StringRef CPU, StringRef FS, const TargetOptions &Options,
                                 Reloc::Model RM, CodeModel::Model CM,
                                 CodeGenOpt::Level OL)
  : TargetMachine(T, Triple, CPU, FS, Options),
    DL("e-p:32:32-i64:64-v128:32:128-n32-S128"),
    Subtarget(&DL) {
  CodeGenInfo = T.createMCCodeGenInfo(Triple, RM, CM, OL);
}

void JSTargetMachine::addAnalysisPasses(PassManagerBase &PM) {
  // We don't currently use BasicTTI because that depends on
  // TargetLoweringInfo, which we don't currently implement.
  PM.add(createJSTargetTransformInfoPass(this));
}
