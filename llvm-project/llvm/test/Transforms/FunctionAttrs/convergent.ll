; NOTE: Assertions have been autogenerated by utils/update_test_checks.py UTC_ARGS: --function-signature --check-attributes
; RUN: opt -passes=function-attrs -S < %s | FileCheck %s

define i32 @nonleaf() convergent {
; CHECK: Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none)
; CHECK-LABEL: define {{[^@]+}}@nonleaf
; CHECK-SAME: () #[[ATTR0:[0-9]+]] {
; CHECK-NEXT:    [[A:%.*]] = call i32 @leaf()
; CHECK-NEXT:    ret i32 [[A]]
;
  %a = call i32 @leaf()
  ret i32 %a
}

define i32 @leaf() convergent {
; CHECK: Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none)
; CHECK-LABEL: define {{[^@]+}}@leaf
; CHECK-SAME: () #[[ATTR0]] {
; CHECK-NEXT:    ret i32 0
;
  ret i32 0
}

declare i32 @k() convergent

define i32 @extern() convergent {
; CHECK: Function Attrs: convergent
; CHECK-LABEL: define {{[^@]+}}@extern
; CHECK-SAME: () #[[ATTR1:[0-9]+]] {
; CHECK-NEXT:    [[A:%.*]] = call i32 @k() #[[ATTR1]]
; CHECK-NEXT:    ret i32 [[A]]
;
  %a = call i32 @k() convergent
  ret i32 %a
}

; Convergent should not be removed on the function here.  Although the call is
; not explicitly convergent, it picks up the convergent attr from the callee.
define i32 @extern_non_convergent_call() convergent {
; CHECK: Function Attrs: convergent
; CHECK-LABEL: define {{[^@]+}}@extern_non_convergent_call
; CHECK-SAME: () #[[ATTR1]] {
; CHECK-NEXT:    [[A:%.*]] = call i32 @k()
; CHECK-NEXT:    ret i32 [[A]]
;
  %a = call i32 @k()
  ret i32 %a
}

define i32 @indirect_convergent_call(ptr %f) convergent {
; CHECK: Function Attrs: convergent
; CHECK-LABEL: define {{[^@]+}}@indirect_convergent_call
; CHECK-SAME: (ptr nocapture readonly [[F:%.*]]) #[[ATTR1]] {
; CHECK-NEXT:    [[A:%.*]] = call i32 [[F]]() #[[ATTR1]]
; CHECK-NEXT:    ret i32 [[A]]
;
  %a = call i32 %f() convergent
  ret i32 %a
}
; Give indirect_non_convergent_call the norecurse attribute so we get a
; "Function Attrs" comment in the output.
define i32 @indirect_non_convergent_call(ptr %f) convergent norecurse {
; CHECK: Function Attrs: norecurse
; CHECK-LABEL: define {{[^@]+}}@indirect_non_convergent_call
; CHECK-SAME: (ptr nocapture readonly [[F:%.*]]) #[[ATTR2:[0-9]+]] {
; CHECK-NEXT:    [[A:%.*]] = call i32 [[F]]()
; CHECK-NEXT:    ret i32 [[A]]
;
  %a = call i32 %f()
  ret i32 %a
}

declare void @llvm.nvvm.barrier0() convergent

define i32 @intrinsic() convergent {
  ; Implicitly convergent, because the intrinsic is convergent.
; CHECK: Function Attrs: convergent nounwind
; CHECK-LABEL: define {{[^@]+}}@intrinsic
; CHECK-SAME: () #[[ATTR4:[0-9]+]] {
; CHECK-NEXT:    call void @llvm.nvvm.barrier0()
; CHECK-NEXT:    ret i32 0
;
  call void @llvm.nvvm.barrier0()
  ret i32 0
}

define i32 @recursive1() convergent {
; CHECK: Function Attrs: nofree nosync nounwind memory(none)
; CHECK-LABEL: define {{[^@]+}}@recursive1
; CHECK-SAME: () #[[ATTR5:[0-9]+]] {
; CHECK-NEXT:    [[A:%.*]] = call i32 @recursive2() #[[ATTR1]]
; CHECK-NEXT:    ret i32 [[A]]
;
  %a = call i32 @recursive2() convergent
  ret i32 %a
}

define i32 @recursive2() convergent {
; CHECK: Function Attrs: nofree nosync nounwind memory(none)
; CHECK-LABEL: define {{[^@]+}}@recursive2
; CHECK-SAME: () #[[ATTR5]] {
; CHECK-NEXT:    [[A:%.*]] = call i32 @recursive1() #[[ATTR1]]
; CHECK-NEXT:    ret i32 [[A]]
;
  %a = call i32 @recursive1() convergent
  ret i32 %a
}

define i32 @noopt() convergent optnone noinline {
; CHECK: Function Attrs: convergent noinline optnone
; CHECK-LABEL: define {{[^@]+}}@noopt
; CHECK-SAME: () #[[ATTR6:[0-9]+]] {
; CHECK-NEXT:    [[A:%.*]] = call i32 @noopt_friend() #[[ATTR1]]
; CHECK-NEXT:    ret i32 0
;
  %a = call i32 @noopt_friend() convergent
  ret i32 0
}

; A function which is mutually-recursive with a convergent, optnone function
; shouldn't have its convergent attribute stripped.
define i32 @noopt_friend() convergent {
; CHECK: Function Attrs: convergent
; CHECK-LABEL: define {{[^@]+}}@noopt_friend
; CHECK-SAME: () #[[ATTR1]] {
; CHECK-NEXT:    [[A:%.*]] = call i32 @noopt()
; CHECK-NEXT:    ret i32 0
;
  %a = call i32 @noopt()
  ret i32 0
}