message(STATUS "LLVM_DIR before: ${LLVM_DIR}")

cmake_minimum_required(VERSION 3.1)

message(STATUS "LLVM_DIR before: ${LLVM_DIR}")

find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "LLVM_DIR after: ${LLVM_DIR}")

add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})

add_subdirectory(LQICM)  # Use your pass name here.
