#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

typedef struct CompilerInfo {

    char *flags; //seperated by space
    double* fileends;

} CompilerInfo;

void pre_readfile(FILE* fp, char** contentout){
    fseek(fp, 0L, SEEK_END);
    int filesize = ftell(fp);
    fseek(fp, 0L, SEEK_SET);
    *contentout = malloc(filesize+1);
    size_t red = fread(*contentout, 1, filesize, fp);
    *contentout[red] = 0;
}

/*  removing macros after use   */
void removeCharAt(char** str, int position){
    *str[position] = ' ';
}

void include_macro(char* arg) {}
void flag_macro(char* arg) {}
void isset_macro(char* arg) {}
void filebegin_macro(char* arg) {}

void codegen_macro(char* macroname, char* arg, ...) {
    va_list vaptr;
    va_start(vaptr, arg);

    //do something

    va_end(vaptr);
}

CompilerInfo mondpre(FILE* fp){
    CompilerInfo compilerInfo;
    int macroleft = 0;
    while(!macroleft){
        char* filecontents;
        pre_readfile(fp, filecontents);

    }
    return compilerInfo;
}



