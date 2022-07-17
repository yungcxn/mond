#include <stdio.h>
#include "mondpre.c"
#include "mondutil.h"
#include <unistd.h>
#include <limits.h>

int main(int argc, char *argv[]) {
    if(argc >= 2){
        char cwd[PATH_MAX];
        if (getcwd(cwd, sizeof(cwd)) == NULL) {
            return 5; // I/O
        }

        char* relativepath = *argv[2];
        char filename[FILENAME_MAX];
        strcpy(filename, getfilename(relativepath));

        char absolutepath[PATH_MAX];

        strcpy(absolutepath, cwd);
        strcat(absolutepath, FILESEP);
        strcat(absolutepath, relativepath);

        char buildpath[PATH_MAX];

        strcpy(buildpath, cwd);
        strcat(buildpath, FILESEP);
        strcat(buildpath, BUILD_FOLDER_NAME);

        char processedpath[PATH_MAX];

        strcpy(processedpath, buildpath);
        strcat(processedpath, filename);
        strcat(processedpath, PROCESSED_FILE_EXT);

        FILE *targetfile = fopen(absolutepath, "r");
        FILE *processedfile = fopen(processedpath, "wr");
        CompilerInfo ppInfo = mondpre(targetfile, processedfile, argc, argv);
        fclose(targetfile);
    }
    return 0;
}
