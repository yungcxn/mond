#ifndef MONDC_MONDUTIL_H
#define MONDC_MONDUTIL_H

#include <stdlib.h>
#include <dirent.h>
#include <sys/stat.h>
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

/*
 * whenever this function gets called, save to pointer and free memory since char* dir is malloc'd
 */
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

int remove_directory(const char *path) {
    // These are data types defined in the "dirent" header
    DIR *theFolder = opendir(path);
    struct dirent *next_file;
    char filepath[256];

    while ( (next_file = readdir(theFolder)) != NULL )
    {
        // build the path for each file in the folder
        sprintf(filepath, "%s/%s", path, next_file->d_name);
        remove(filepath);
    }
    closedir(theFolder);
    return 0;
}

/*
 * UNIX fileshortening
 */
void shortenfile(FILE* fp, int len){
    fseeko(fp,-len,SEEK_END);
    off_t position = ftello(fp);
    ftruncate(fileno(fp), position);
}


#endif
