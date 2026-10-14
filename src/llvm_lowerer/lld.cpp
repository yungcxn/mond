// lld has no c api: this is the one c++ function the backend calls to link
#include "lld/Common/Driver.h"

#if defined(MOND_LLD_macho)
LLD_HAS_DRIVER(macho)
static const lld::DriverDef drivers[] = {{lld::Darwin, &lld::macho::link}};
#else
LLD_HAS_DRIVER(elf)
static const lld::DriverDef drivers[] = {{lld::Gnu, &lld::elf::link}};
#endif

// the first argument names the flavor (`ld64.lld`, `ld.lld`), errors go to stderr
extern "C" bool mond_lld_link(int argument_count, const char **arguments) {
    llvm::ArrayRef<const char *> argument_list(arguments, argument_count);
    lld::Result result = lld::lldMain(argument_list, llvm::outs(), llvm::errs(), drivers);
    return result.retCode == 0;
}
