LLVM_BUILD="../llvm_build"
tmpIR="./test/llvmIR/tmp.ll"
licmIR="./test/llvmIR/tmpLICM.ll"
O3IR="./test/llvmIR/tmpO3.ll"
bicmIR="./test/llvmIR/tmpBICM.ll"
toLoad="./build/LQICM/libLQICMPass.so"
# echo "******************** OPT -O0 *******************"
if [ -e $tmpIR ]
then
    rm $tmpIR
fi
if [[ $1 == *.c ]]
then
    ${LLVM_BUILD}/bin/clang -O0 -emit-llvm -S $1 -o $tmpIR
else
    if [[ $1 == *.ll ]]
    then
        tmpIR=$1
    else
        echo "Given file should be of extension .c or .ll"
        exit 1
    fi
fi

# ${LLVM_BUILD}/bin/opt -O0 -mem2reg -lcssa -S  $tmpIR -o $tmpIR

${LLVM_BUILD}/bin/opt -O0 -mem2reg -lcssa -loop-deletion -indvars -simplifycfg -loop-simplify -loop-instsimplify -loop-simplifycfg -sink -loop-sink -S  $tmpIR -o $tmpIR

# echo "******************** OUR PASS *******************"

# rm -f /tmp/*.dot
# rm -f ./test/dot/*

# ${LLVM_BUILD}/bin/opt -O0 -load $toLoad -debug -lqicm -S --debug-pass=Arguments -p $tmpIR -o $bicmIR

${LLVM_BUILD}/bin/opt -O0 -load $toLoad -debug -lqicm -simplifycfg -loop-simplifycfg -view-cfg-only -view-dom-only -S --debug-pass=Arguments -p $tmpIR -o $bicmIR

# ${LLVM_BUILD}/bin/opt -O0 -load $toLoad -debug -mem2reg -lcssa -indvars -loop-simplify -loop-instsimplify -loop-simplifycfg -lqicm -view-cfg-only -view-dom-only -S --debug-pass=Arguments $tmpIR -o $bicmIR

# Get dom and cfg in png
# 2>/dev/null
# for dot in `ls /tmp/*.dot`
# do
#   name=$(basename "$dot")
#   dot -Tpng $dot -o "./test/dot/$name.png"
# done
# gvfs-open ./test/dot/*.png
