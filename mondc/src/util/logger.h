#ifndef LOGGER_H
#define LOGGER_H

#define DBG_PRINT_PRE "[DEBUG] "

void logs(char* s){
    printf("%s", s);
}

void logn(){
    printf("\n");
}

void logline(char* s){
    logs(s);logn();
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
    dbg_logpre(); dbg_logs(s);dbg_logn();
#endif
}

void dbg_logi(int i){
#ifdef _DEBUG
    printf("%d", i);
#endif

}

int errorlog(char* line, int code){
    printf("[ERROR] %s\n", line);
    return code;
}

#endif