#ifndef MONDC_MONDUTIL_H
#define MONDC_MONDUTIL_H

#include <stdlib.h>

#ifdef _WIN32
#define FILESEP '\\'
#define FILESEP_S "\\"
#define BUILD_FOLDER_NAME "build\\"
#else
#define FILESEP '/'
#define FILESEP_S "/"
#define BUILD_FOLDER_NAME "build/"
#endif

#define PROCESSED_FILE_EXT "p"
#define PROCESSED_TEMPFILE_EXT "t"

#define TRUE_EXPR "true"
#define FALSE_EXPR "false"

typedef struct astring {
    size_t memsize;
    char string[];
} astring;

typedef astring* astring_ptr;

astring_ptr create_astring(const char* str){
    unsigned int v = strlen(str) + 1;

    v--;
    v |= v >> 1;
    v |= v >> 2;
    v |= v >> 4;
    v |= v >> 8;
    v |= v >> 16;
    v++;

    astring_ptr astr = (astring_ptr) malloc(sizeof(astring) + v);
    astr->memsize = v;
    strcpy(astr->string, str);

    return astr;
}

void safeset_astring(astring_ptr* astr, const char *str){
    size_t reallen = strlen(str)+1;

    int i = 0;
    unsigned int fmemsize = (*astr)->memsize;

    while(reallen > fmemsize){
        fmemsize *= 2;
        if(!i){
            i = 1;
        }
    }

    if(i){

        *astr = (astring_ptr) realloc(*astr, sizeof(astring) + fmemsize);
    }

    (*astr)->memsize = fmemsize;

    strcpy((*astr)->string, str);
}

void free_astring(astring_ptr astr){
    free(astr);
}

void sfree_astring(astring_ptr astr){
    if(astr == NULL){
        return;
    }

    free_astring(astr);
}

void safeappend_astring(astring_ptr* astr, const char *str){
    char begin[strlen((*astr)->string)+1];
    strcpy(begin, (*astr)->string);
    size_t reallen = strlen(begin)+ strlen(str)+1;

    int i = 0;
    unsigned int fmemsize = (*astr)->memsize;

    while(reallen > fmemsize){
        fmemsize *= 2;
        if(!i){
            i = 1;
        }
    }

    if(i){

        *astr = (astring_ptr) realloc(*astr, sizeof(astring) + fmemsize);
    }

    (*astr)->memsize = fmemsize;
    strcpy((*astr)->string, begin);
    strcat((*astr)->string, str);
}

void safeappendc_astring(astring_ptr* astr, const char c){
    char begin[strlen((*astr)->string)+1];
    strcpy(begin, (*astr)->string);
    size_t reallen = strlen(begin)+2;

    int i = 0;
    unsigned int fmemsize = (*astr)->memsize;

    while(reallen > fmemsize){
        fmemsize *= 2;
        if(!i){
            i = 1;
        }
    }

    if(i){

        *astr = (astring_ptr) realloc(*astr, sizeof(astring) + fmemsize);
    }

    (*astr)->memsize = fmemsize;
    strcpy((*astr)->string, begin);
    (*astr)->string[reallen-1] = c;
}

int astrlen(const astring_ptr astr){
    return(strlen(astr->string));
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
