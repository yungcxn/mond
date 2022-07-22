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

int fsize(FILE *fp){
    int prev=ftell(fp);
    fseek(fp, 0L, SEEK_END);
    int sz=ftell(fp);
    fseek(fp,prev,SEEK_SET); //go back to where we were
    return sz;
}


#endif
