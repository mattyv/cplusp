# The clang-tidy plugin of cplusp. One module: one generic check and the hand-written checks. See docs/decisions/0016.
# Build: cmake -S clang-tidy -B target/plugin -G Ninja && cmake --build target/plugin
cmake_minimum_required(VERSION 3.20)
project(cplusp_plugin CXX)

# Ubuntu keeps LLVM 18 in a versioned prefix that CMake does not search. Needs libclang-18-dev and llvm-18-dev.
if(NOT Clang_DIR)
  set(Clang_DIR /usr/lib/llvm-18/lib/cmake/clang)
endif()
find_package(Clang REQUIRED CONFIG)

# A plain build is a release build: the plugin runs inside every gate and prove run.
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release CACHE STRING "The build type." FORCE)
endif()

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

add_library(cplusp MODULE CplusPModule.cpp SyntaxChecks.cpp RawCopyChecks.cpp StateChecks.cpp TreeCheck.cpp)
# The clang-tidy headers have no CMake export. SYSTEM keeps the warnings of LLVM headers out of our build.
target_include_directories(cplusp SYSTEM PRIVATE ${CLANG_INCLUDE_DIRS} ${LLVM_INCLUDE_DIRS} /usr/lib/llvm-18/include/clang-tidy)
# LLVM is built without RTTI. A module with RTTI would not match.
target_compile_options(cplusp PRIVATE -fno-rtti -Wall -Wextra)
# clang-tidy exports libclang-cpp, so those symbols resolve when it loads the module.
# The dynamic matcher parser is the one part that libclang-cpp does not hold.
target_link_libraries(cplusp PRIVATE ${CLANG_INSTALL_PREFIX}/lib/libclangDynamicASTMatchers.a)
