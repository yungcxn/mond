#include <stdio.h>
#include "mondpre.c"
#include "mondutil.h"
#include <unistd.h>
#include <limits.h>

int main(int argc, char *argv[]) {

    printf("\nstarting mondc...\n");
    if(argc == 1){
        printf("no arguments given.\n");
        return 0;
    }

    printf("first arg: %s\n", argv[1]);


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
        strcat(absolutepath, FILESEP_S);
        strcat(absolutepath, relativepath);

        char absolutepath_folder[PATH_MAX];

        strcpy(absolutepath_folder, get_containing_dir(absolutepath));

        char buildpath[PATH_MAX];

        strcpy(buildpath, cwd);
        strcat(buildpath, FILESEP_S);
        strcat(buildpath, BUILD_FOLDER_NAME);

        char processedpath[PATH_MAX];

        strcpy(processedpath, buildpath);
        strcat(processedpath, filename);
        strcat(processedpath, PROCESSED_FILE_EXT);

        char temppath[PATH_MAX];

        strcat(processedpath, PROCESSED_TEMPFILE_EXT);

        FILE *targetfile = fopen(absolutepath, "r");
        FILE *processedfile = fopen(processedpath, "w+");
        FILE *tempfile = fopen(temppath, "w+");

        CompilerInfo ppInfo = mondpre(targetfile, processedfile, tempfile, absolutepath_folder, buildpath, argc, argv);
        fclose(targetfile);
        fclose(processedfile);
        fclose(tempfile);
    }
    return 0;
}
