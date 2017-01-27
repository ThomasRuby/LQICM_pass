if ! [ -d "./build" ] ; then
    mkdir build
fi
cd build
cmake -LLVM_ENABLE_FFI -DLLVM_DIR=$HOME/LLVM4/llvm_build/lib/cmake/llvm cmake ..
make
cd ..
