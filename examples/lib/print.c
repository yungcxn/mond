// `print` of examples/bc.mn: printf, flushed after each call, so a calculator in a pipe answers
// each line when it is read
#include <stdarg.h>
#include <stdio.h>

void print(const char *format, ...) {
    va_list arguments;
    va_start(arguments, format);
    vprintf(format, arguments);
    va_end(arguments);
    fflush(stdout);
}
