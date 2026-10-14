// the llvm c api the backend uses, translated into the zig module `llvm_c` by build.zig
#include <llvm-c/Core.h>
#include <llvm-c/Analysis.h>
#include <llvm-c/Target.h>
#include <llvm-c/TargetMachine.h>
#include <llvm-c/Transforms/PassBuilder.h>

// the linker, see lld.cpp
#include <stdbool.h>
bool mond_lld_link(int argument_count, const char **arguments);
