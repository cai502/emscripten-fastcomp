; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc < %s -mtriple=x86_64-apple-darwin -mcpu=skx | FileCheck --check-prefix=SKX --check-prefix=SKX_ONLY %s

; TODO - fix fail on KNL and move this test to avx512-insert-extract.ll

define zeroext i8 @test_extractelement_varible_v64i1(<64 x i8> %a, <64 x i8> %b, i32 %index) {
; SKX-LABEL: test_extractelement_varible_v64i1:
; SKX:       ## %bb.0:
; SKX-NEXT:    pushq %rbp
; SKX-NEXT:    .cfi_def_cfa_offset 16
; SKX-NEXT:    .cfi_offset %rbp, -16
; SKX-NEXT:    movq %rsp, %rbp
; SKX-NEXT:    .cfi_def_cfa_register %rbp
; SKX-NEXT:    andq $-64, %rsp
; SKX-NEXT:    subq $128, %rsp
; SKX-NEXT:    ## kill: def %edi killed %edi def %rdi
; SKX-NEXT:    vpcmpnleub %zmm1, %zmm0, %k0
; SKX-NEXT:    vpmovm2b %k0, %zmm0
; SKX-NEXT:    vmovdqa32 %zmm0, (%rsp)
; SKX-NEXT:    andl $63, %edi
; SKX-NEXT:    movzbl (%rsp,%rdi), %eax
; SKX-NEXT:    andl $1, %eax
; SKX-NEXT:    movq %rbp, %rsp
; SKX-NEXT:    popq %rbp
; SKX-NEXT:    vzeroupper
; SKX-NEXT:    retq
  %t1 = icmp ugt <64 x i8> %a, %b
  %t2 = extractelement <64 x i1> %t1, i32 %index
  %res = zext i1 %t2 to i8
  ret i8 %res
}

