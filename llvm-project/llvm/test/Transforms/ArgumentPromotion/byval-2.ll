; NOTE: Assertions have been autogenerated by utils/update_test_checks.py UTC_ARGS: --function-signature --scrub-attributes
; RUN: opt < %s -passes=argpromotion -S | FileCheck %s

; Arg promotion eliminates the struct argument.

%struct.ss = type { i32, i64 }

define internal void @f(ptr byval(%struct.ss) align 8 %b, ptr byval(i32) align 4 %X) nounwind  {
; CHECK-LABEL: define {{[^@]+}}@f
; CHECK-SAME: (i32 [[B_0:%.*]], i32 [[X:%.*]]) #[[ATTR0:[0-9]+]] {
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[TEMP:%.*]] = add i32 [[B_0]], 1
; CHECK-NEXT:    ret void
;
entry:
  %temp1 = load i32, ptr %b, align 4
  %temp2 = add i32 %temp1, 1
  store i32 %temp2, ptr %b, align 4

  store i32 0, ptr %X
  ret void
}

define i32 @test(ptr %X) {
; CHECK-LABEL: define {{[^@]+}}@test
; CHECK-SAME: (ptr [[X:%.*]]) {
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[S:%.*]] = alloca [[STRUCT_SS:%.*]], align 8
; CHECK-NEXT:    store i32 1, ptr [[S]], align 8
; CHECK-NEXT:    [[TEMP4:%.*]] = getelementptr [[STRUCT_SS]], ptr [[S]], i32 0, i32 1
; CHECK-NEXT:    store i64 2, ptr [[TEMP4]], align 4
; CHECK-NEXT:    [[S_0_VAL:%.*]] = load i32, ptr [[S]], align 4
; CHECK-NEXT:    [[X_VAL:%.*]] = load i32, ptr [[X]], align 4
; CHECK-NEXT:    call void @f(i32 [[S_0_VAL]], i32 [[X_VAL]])
; CHECK-NEXT:    ret i32 0
;
entry:
  %S = alloca %struct.ss, align 8
  store i32 1, ptr %S, align 8
  %temp4 = getelementptr %struct.ss, ptr %S, i32 0, i32 1
  store i64 2, ptr %temp4, align 4
  call void @f( ptr byval(%struct.ss) align 8 %S, ptr byval(i32) align 4 %X)
  ret i32 0
}