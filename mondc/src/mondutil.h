#ifndef MONDC_MONDUTIL_H
#define MONDC_MONDUTIL_H

#include <stdlib.h>

#ifdef _WIN32
#define FILESEP '\\'
#define BUILD_FOLDER_NAME "build\\"
#else
#define FILESEP '/'
#define BUILD_FOLDER_NAME "build/"
#endif

#define PROCESSED_FILE_EXT "p"
#define PROCESSED_TEMPFILE_EXT "t"

#define TRUE_EXPR "true"
#define FALSE_EXPR "false"


typedef struct pstring {
    size_t memsize;
    char *string;
} pstring;


int pstrlen(const pstring pstr){
    return(strlen(pstr.string));
}

pstring create_pstring(const char* str){
    unsigned int v = strlen(str) + 1;

    v--;
    v |= v >> 1;
    v |= v >> 2;
    v |= v >> 4;
    v |= v >> 8;
    v |= v >> 16;
    v++;

    pstring pstr = {.memsize = v, .string = str};
    return pstr;
}
void safeset_pstring(pstring *pstr, const char *str){
    size_t reallen = strlen(str)+1;
    while(reallen > pstr->memsize){
        pstr->memsize *= 2;
    }
    pstr->string = (char*) malloc(pstr->memsize);
    printf("%d\n", strlen(str));
    printf("%d\n", pstr->memsize);
    strcpy(pstr->string, str);
}

void safeappend_pstring(pstring *pstr, const char *str){
    safeset_pstring(pstr, strcat(pstr->string, str));
}

void pstring_to_arr(const pstring mstr, char *buf[]){
    strcpy(buf, mstr.string);
}

typedef struct astring {
    size_t memsize;
    char string[];
} astring;

astring create_astring(const char* str){
    unsigned int v = strlen(str) + 1;

    v--;
    v |= v >> 1;
    v |= v >> 2;
    v |= v >> 4;
    v |= v >> 8;
    v |= v >> 16;
    v++;

    astring *astr = (astring*) malloc(sizeof(astring) + v);
    return *astr;
}

void safeset_astring(astring *astr, const char *str){
    size_t reallen = strlen(str)+1;
    while(reallen > astr->memsize){
        astr->memsize *= 2;
    }
    astr = (astring*) malloc(sizeof(astring) + astr->memsize);
    printf("%d\n", strlen(str));
    printf("%d\n", astr->memsize);
    strcpy(astr->string, str);
}

void safeappend_astring(astring *astr, const char *str){
    safeset_astring(astr, strcat(astr->string, str));
}

int astrlen(const astring astr){
    return(strlen(astr.string));
}

char* getfilename(const char* path){
    char buf[strlen(path) + 1];
    for(int i = 0; i<strlen(path); i++){
        char c = path[i];
        if(c == FILESEP){
            strcpy(buf, "");
            continue;
        }
        strncat(buf, c, 1);
    }
    return buf;
}

char* get_containing_dir(const char* path){
    int len = strlen(path);
    char* dir = malloc(len + 1);
    strcpy(dir, path);
    while (len > 0) {
        len--;
        if (dir[len] == FILESEP) {
            dir[len] = '\0';
            break;
        }
    }
    return dir;

}
/*
 * grows int array according to the next exponentiation of 2 to n
 */
void grow_intarr(int * buf[]){
    unsigned int v = sizeof(*buf);

    v--;
    v |= v >> 1;
    v |= v >> 2;
    v |= v >> 4;
    v |= v >> 8;
    v |= v >> 16;
    v++;

    int* copy = *buf;
    *buf = malloc(v);
    *buf = *copy;
}

/*
 * replaces next integer with value 0 in int array
 */
void safeappend_intarr(int *buf[], int val){
    int elems = sizeof(*buf) / sizeof(int);
    for(int i = 0; i<elems; i++){
        if(*buf[i] == 0){
            *buf[i] = val;
            return;
        }
    }
    grow_intarr(buf);
    *buf[elems] = val;
}

char* readfile(FILE* fp){
    fseek(fp, 0L, SEEK_END);
    int filesize = ftell(fp);
    fseek(fp, 0L, SEEK_SET);
    char *contentout = malloc(filesize+1);
    size_t red = fread(*contentout, 1, filesize, fp);
    contentout[red] = 0;
    return *contentout;
}

#endif
