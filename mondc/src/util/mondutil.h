#ifndef MONDC_MONDUTIL_H
#define MONDC_MONDUTIL_H

#include <stdlib.h>
#include "../mondc.h"

char* getfilename(const char* path){
    int len = strlen(path);

    for(int i=len-1; i>0; i--)
    {
        if(path[i]=='\\' || path[i]=='//' || path[i]=='/' )
        {
            path = path+i+1;
            break;
        }
    }
    return path;
}

char* get_containing_dir(const char* path){
    int len = strlen(path);
    char* dir = malloc(len + 1);
    strcpy(dir, path);
    while (len > 0) {
        --len;
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
