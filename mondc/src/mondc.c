#include <stdio.h>
#include <unistd.h>
#include <limits.h>
#include "util/logger.h"
#include "mondpre.c"
#include "util/mondutil.h"
#include "mondc.h"

void print_usage(){
    logl("usage:");
    logl("  $ mondc file.mon");
    logl("  $ mondc dir/file.mon");
    logl("  $ mondc \"file.mon\"");
    logn();
}

/*
 * if this returns 1 (FAILURE), program exists
 */
int usage_handler(int argc, char *argv[]){

    if(argc == 1){
        logn();
        logl("no arguments given...");
        print_usage();
        return 1;
    }

    if(argc > 2){
        logn();
        logs("all arguments after \"");
        logs(argv[2]);
        logs("\" are unused");
    }

    return 0;
}


int main(int argc, char *argv[]) {

    logn();
    logs("starting mondc <");
    logs(MONDC_VERSION);
    logs(">...");
    logn();

    if(usage_handler(argc, argv)){
        return EXIT_SUCCESS;
    }

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
