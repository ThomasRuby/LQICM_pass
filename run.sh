LLVM_BUILD="../llvm_build"
tmpIR="./test/llvmIR/tmp.ll"
licmIR="./test/llvmIR/tmpLICM.ll"
O3IR="./test/llvmIR/tmpO3.ll"
bicmIR="./test/llvmIR/tmpBICM.ll"
${LLVM_BUILD}/bin/clang -O0 -emit-llvm -S $1 -o $tmpIR
${LLVM_BUILD}/bin/opt -O0 -load ./build/LQICM/libLQICMPass.so -debug -mem2reg -lqicm -S --debug-pass=Arguments $tmpIR -o $bicmIR
