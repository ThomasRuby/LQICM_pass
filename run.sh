LLVM_BUILD="../llvm_build"
tmpIR="./test/llvmIR/tmp.ll"
licmIR="./test/llvmIR/tmpLICM.ll"
O3IR="./test/llvmIR/tmpO3.ll"
bicmIR="./test/llvmIR/tmpBICM.ll"
echo "******************** OPT -O0 *******************"
${LLVM_BUILD}/bin/clang -O0 -emit-llvm -S $1 -o $tmpIR
# echo "******************** UNROLL TRY *******************"
# ${LLVM_BUILD}/bin/opt -debug -mem2reg -simplifycfg -loops -lcssa -loop-simplify -loop-unroll -unroll-count=3 -unroll-allow-partial -S --debug-pass=Arguments  $tmpIR -o $licmIR
# echo "******************** OPT -O3 *******************"
# ${LLVM_BUILD}/bin/opt -debug -O3 -S --debug-pass=Arguments  $tmpIR -o $O3IR
echo "******************** OUR PASS *******************"
${LLVM_BUILD}/bin/opt -O0 -load ./build/LQICM/libLQICMPass.so -debug -mem2reg -lqicm -S --debug-pass=Arguments $tmpIR -o $bicmIR
# ${LLVM_BUILD}/bin/clang -O0 -emit-llvm -S -Xclang -load -Xclang build/BICM/libBICMPass.so -bicm $1 -o $bicmIR
# ${LLVM_BUILD}/bin/opt -load build/BICM/libBICMPass.so < LICMtest/llvmIR/tmp.ll > /dev/null
