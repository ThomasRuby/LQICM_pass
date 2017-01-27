; ModuleID = 'LICMtest/files/Fact.c'
source_filename = "LICMtest/files/Fact.c"
target datalayout = "e-m:e-p:32:32-i64:64-v128:64:128-a:0:32-n32-S64"
target triple = "armv7-unknown-linux-gnueabihf"

@.str = private unnamed_addr constant [13 x i8] c"blabla %d %d\00", align 1

; Function Attrs: noinline nounwind
define i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %i = alloca i32, align 4
  %fact = alloca i32, align 4
  %n = alloca i32, align 4
  %j = alloca i32, align 4
  store i32 0, i32* %retval, align 4
  %call = call i32 @time(i32* null) #3
  call void @srand(i32 %call) #3
  %call1 = call i32 @rand() #3
  %rem = srem i32 %call1, 100
  store i32 %rem, i32* %n, align 4
  store i32 0, i32* %j, align 4
  store i32 1, i32* %fact, align 4
  store i32 1, i32* %i, align 4
  br label %while.cond

while.cond:                                       ; preds = %while.end, %entry
  %0 = load i32, i32* %j, align 4
  %cmp = icmp slt i32 %0, 100
  br i1 %cmp, label %while.body, label %while.end6

while.body:                                       ; preds = %while.cond
  store i32 1, i32* %fact, align 4
  store i32 1, i32* %i, align 4
  br label %while.cond2

while.cond2:                                      ; preds = %while.body4, %while.body
  %1 = load i32, i32* %i, align 4
  %2 = load i32, i32* %n, align 4
  %cmp3 = icmp slt i32 %1, %2
  br i1 %cmp3, label %while.body4, label %while.end

while.body4:                                      ; preds = %while.cond2
  %3 = load i32, i32* %fact, align 4
  %4 = load i32, i32* %i, align 4
  %mul = mul nsw i32 %3, %4
  store i32 %mul, i32* %fact, align 4
  %5 = load i32, i32* %i, align 4
  %add = add nsw i32 %5, 1
  store i32 %add, i32* %i, align 4
  br label %while.cond2

while.end:                                        ; preds = %while.cond2
  %6 = load i32, i32* %j, align 4
  %add5 = add nsw i32 %6, 1
  store i32 %add5, i32* %j, align 4
  br label %while.cond

while.end6:                                       ; preds = %while.cond
  %7 = load i32, i32* %i, align 4
  %8 = load i32, i32* %fact, align 4
  %call7 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([13 x i8], [13 x i8]* @.str, i32 0, i32 0), i32 %7, i32 %8)
  %9 = load i32, i32* %i, align 4
  ret i32 %9
}

; Function Attrs: nounwind
declare void @srand(i32) #1

; Function Attrs: nounwind
declare i32 @time(i32*) #1

; Function Attrs: nounwind
declare i32 @rand() #1

declare i32 @printf(i8*, ...) #2

attributes #0 = { noinline nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="cortex-a8" "target-features"="+dsp,+neon,+vfp3" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="cortex-a8" "target-features"="+dsp,+neon,+vfp3" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="cortex-a8" "target-features"="+dsp,+neon,+vfp3" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 1, !"min_enum_size", i32 4}
!2 = !{!"clang version 4.0.0 (http://llvm.org/git/clang.git c311b06da6522cfdf2e28000e70ed4dfeb390b37) (http://llvm.org/git/llvm.git 356e45bf08b4994f3612ca29fe602aec10ec9555)"}
