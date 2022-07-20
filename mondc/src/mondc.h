#ifndef MONDC_H
#define MONDC_H

#include "util/logger.h"

#define MONDC_VERSION "0.1"
#define STDLIBNAME "standard.mon"

//--- os section ---//

#ifndef _WIN64
#ifdef _WIN32
//double definition for only 32-bit architecture
#define MONDC_OS_FLAG "_OS_WIN32"
#define MONDLIB_LOC "C:\\include\\mondlibs\\"

#endif
#endif


#ifdef _WIN64

#define MONDC_OS_FLAG "_OS_WIN64"
#define c "C:/include/mondlibs/"

#endif


#ifdef __unix__

#define MONDC_OS_FLAG "_OS_UNIX"
#define MONDLIB_LOC "/usr/local/include/mondlibs/"

#endif

#ifdef __linux__

#define MONDC_OS_FLAG "_OS_LINUX"
#define MONDLIB_LOC "/usr/local/include/mondlibs/"

#endif


#ifdef __MACH__

#define MONDC_OS_FLAG "_OS_MAC"
#define MONDLIB_LOC "/usr/local/include/mondlibs/"

#endif

//--- cpu architecture section ---//


#endif