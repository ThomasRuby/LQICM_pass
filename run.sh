LLVM_BUILD="../llvm_build"
tmpIR="./test/llvmIR/tmp.ll"
licmIR="./test/llvmIR/tmpLICM.ll"
O3IR="./test/llvmIR/tmpO3.ll"
bicmIR="./test/llvmIR/tmpBICM.ll"
toLoad="./build/LQICM/libLQICMPass.so"
cfg=false

if [ $# -lt 1 ] ; then
  echo "need a file .c or .ll to compile"
  exit 1
fi

while getopts 'gv' arguments;
do
  case ${arguments} in
    g) echo "graph view activated…" ; cfg=true ;;
    v) echo "no version yet…" ;;
  esac
done

# echo "******************** OPT -O0 *******************"
if [ -e $tmpIR ]
then
    rm $tmpIR
fi

echo "file to compile is ${@: -1}"
file=${@: -1}

if [[ $file == *.c ]]
then
  if $cfg ;
  then
    ${LLVM_BUILD}/bin/clang -O0 -emit-llvm -S $file -o $tmpIR
  else
    ${LLVM_BUILD}/bin/clang -emit-llvm -S -fno-vectorize -Xclang -load \
    -Xclang $toLoad -mllvm -stats -mllvm -debug-pass=Arguments \
    -mllvm -debug -p -O3 $file -o $bicmIR
  fi
else
    if [[ $file == *.ll ]]
    then
        tmpIR=$file
    else
        echo "Given file should be of extension .c or .ll"
        exit 1
    fi
fi

# ${LLVM_BUILD}/bin/opt -O0 -mem2reg -lcssa -S  $tmpIR -o $tmpIR

# echo "******************** pass before ****************"

if $cfg ;
then
  rm -f ./*.dot
  rm -f /tmp/*.dot
  rm -f ./test/dot/*
fi

# echo "******************** WITHOUT OUR PASS *******************"

# if $cfg ;
# then
#   ${LLVM_BUILD}/bin/opt -O0 -mem2reg -lcssa -loop-deletion -indvars -simplifycfg -loop-simplify -loop-instsimplify -loop-simplifycfg -sink -loop-sink -dot-cfg -S  $tmpIR -o $tmpIR
#   mv *main*.dot /tmp/cfgmain1.dot
#   rm -f ./*.dot
# else
#   ${LLVM_BUILD}/bin/opt -O0 -mem2reg -lcssa -loop-deletion -indvars -simplifycfg -loop-simplify -loop-instsimplify -loop-simplifycfg -sink -loop-sink -S  $tmpIR -o $tmpIR
# fi

# echo "******************** WITH OUR PASS *******************"

if $cfg ;
then
  ${LLVM_BUILD}/bin/opt -O3 -stats -load $toLoad -debug -simplifycfg -dot-cfg \
  -S --debug-pass=Arguments -p $tmpIR -o $bicmIR
  mv *main*.dot /tmp/cfgmain2.dot
  rm -f ./*.dot
# else
#   ${LLVM_BUILD}/bin/opt -O0 -stats -load $toLoad -debug -simplifycfg -S \
#   --debug-pass=Arguments -p $tmpIR -o $bicmIR
fi

# ${LLVM_BUILD}/bin/opt -O0 -load $toLoad -debug -mem2reg -lcssa -indvars -loop-simplify -loop-instsimplify -loop-simplifycfg -lqicm -view-cfg-only -view-dom-only -S --debug-pass=Arguments $tmpIR -o $bicmIR
# Get dom and cfg in png
if $cfg ;
then
  2>/dev/null
  for dot in `ls /tmp/*.dot`
  do
    name=$(basename "$dot")
    dot -Tpng $dot -o "./test/dot/$name.png"
  done
  gio open ./test/dot/cfgmain*.png
fi
