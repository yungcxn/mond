#ifndef LOGGER_H
#define LOGGER_H

#include <stdlib.h>

#define DBG_PRINT_PRE "[DEBUG] "
#define TCRED   "\x1B[31m"
#define TCGRN   "\x1B[32m"
#define TCYEL   "\x1B[33m"
#define TCBLU   "\x1B[34m"
#define TCMAG   "\x1B[35m"
#define TCCYN   "\x1B[36m"
#define TCWHT   "\x1B[37m"
#define TCRESET "\x1B[0m"

void logs(char* s){
    printf("%s", s);
}

void logn(){
    printf("\n");
}

void logline(char* s){
    puts(s);
}

void logi(int i){
    printf("%d", i);
}

void dbg_logpre(){
#ifdef _DEBUG
    printf(DBG_PRINT_PRE);
#endif
}

void dbg_logs(char* s){
#ifdef _DEBUG
    printf("%s", s);
#endif
}

void dbg_logn(){
#ifdef _DEBUG
    printf("\n");
#endif
}

void dbg_logline(char* s){
#ifdef _DEBUG
    dbg_logpre(); puts(s);
#endif
}

void dbg_logi(int i){
#ifdef _DEBUG
    printf("%d", i);
#endif

}

void dbg_logc(char i){
#ifdef _DEBUG
    printf("%c", i);
#endif

}

void reporterror(char* line, int code){
    printf(TCRED "[ERROR] %s\n" TCRESET, line);
    exit(code);
}

#endif