#include <stdio.h>
#include <unistd.h>
#include <limits.h>
#include "util/logger.h"
#include "mondpre.c"
#include "util/mondutil.h"
#include "mondc.h"
#include <sys/types.h>
#include <sys/stat.h>

void print_usage(){
    logn();
    logline("usage:");
    logline("  $ mondc file.mon");
    logline("  $ mondc dir/file.mon");
    logline("  $ mondc \"file.mon\"");
    logn();
}

/*
 * if this returns 1 (FAILURE), main should exit
 */
int usage_handler(int argc, char *argv[]){

    if(argc == 1){
        logn();
        logline("no arguments given...");
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

    dbg_logline("initiated");
    dbg_logn();

    dbg_logpre();dbg_logs("argcount = ");dbg_logi(argc);dbg_logn();
#ifdef _DEBUG
    for(int i = 0; i<sizeof(argv)/sizeof(char);i++){
        if(argv[i] == NULL){
            break;
        }
        dbg_logpre();dbg_logs("arg");dbg_logi(i);dbg_logs(" = ");
        dbg_logs(argv[i]);dbg_logn();

    }
    dbg_logn();
#endif

    if(usage_handler(argc, argv)){
        return EXIT_SUCCESS;
    }

    if(argc >= 2){
        char cwd[PATH_MAX];

        if (getcwd(cwd, sizeof(cwd)) == NULL) {
            return 5; // I/O
        }

        dbg_logpre();dbg_logs("cwd = ");dbg_logs(cwd);dbg_logn();

        char* relativepath = argv[1];

        char filename[FILENAME_MAX];
        strcpy(filename, getfilename(relativepath));

        dbg_logpre();dbg_logs("relativepath = ");dbg_logs(relativepath);dbg_logn();
        dbg_logpre();dbg_logs("filename = ");dbg_logs(filename);dbg_logn();

        char absolutepath[PATH_MAX];

        strcpy(absolutepath, cwd);
        strncat(absolutepath, &FILESEP,1);
        strcat(absolutepath, relativepath);

        dbg_logpre();dbg_logs("absolutepath = ");dbg_logs(absolutepath);dbg_logn();

        char absolutepath_folder[PATH_MAX];

        strcpy(absolutepath_folder, get_containing_dir(absolutepath));

        dbg_logpre();dbg_logs("absolutepath_folder = ");dbg_logs(absolutepath_folder);dbg_logn();

        char buildpath[PATH_MAX];

        strcpy(buildpath, cwd);
        strncat(buildpath, &FILESEP, 1);
        strcat(buildpath, get_containing_dir(relativepath));
        strncat(buildpath, &FILESEP, 1);
        strcat(buildpath, BUILD_FOLDER_NAME);

        /*
         * create build folder in buildpath if not existing
         */
        struct stat st = {0};
        if (stat(buildpath, &st) == -1) {
            mkdir(buildpath, 0700);
            dbg_logline("build folder was created!");
        }

        dbg_logpre();dbg_logs("buildpath = ");dbg_logs(buildpath);dbg_logn();

        char processedpath[PATH_MAX];

        strcpy(processedpath, buildpath);
        strncat(processedpath, &FILESEP, 1);
        strcat(processedpath, filename);
        strcat(processedpath, PROCESSED_FILE_EXT);

        dbg_logpre();dbg_logs("processedpath = ");dbg_logs(processedpath);dbg_logn();

        char temppath[PATH_MAX];

        strcpy(temppath, processedpath);
        strcat(temppath, PROCESSED_TEMPFILE_EXT);

        dbg_logpre();dbg_logs("temppath = ");dbg_logs(temppath);dbg_logn();

        FILE *targetfile = fopen(absolutepath, "r");
        FILE *processedfile = fopen(processedpath, "w+");
        FILE *tempfile = fopen(temppath, "w+");

        if(targetfile == NULL || processedfile == NULL || tempfile == NULL){
            return errorlog("cannot access files to be compiled", 5);
        }

        CompilerInfo ppInfo = mondpre(targetfile, processedfile, tempfile, absolutepath_folder, buildpath, argc, argv);

        logline("PREPROCESSOR (MONDPRE) is done!");

        fclose(targetfile);
        fclose(processedfile);
        fclose(tempfile);

    }
    return 0;
}
