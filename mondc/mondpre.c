#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "mondutil.h"
#include "mondpre.h"
#include "llist.h"
#include <unistd.h>

/*
 * TODO:
 * - cross include ????
 * - set os flags
 */

typedef struct CompilerInfo {

    int* fileends;

} CompilerInfo;


char* readfile(FILE* fp){
    fseek(fp, 0L, SEEK_END);
    int filesize = ftell(fp);
    fseek(fp, 0L, SEEK_SET);
    char *contentout = malloc(filesize+1);
    size_t red = fread(*contentout, 1, filesize, fp);
    contentout[red] = 0;
    return *contentout;
}

int pre_include_macro(int argc, char* arg, FILE* dest) {}
int pre_flag_macro(int argc, char* arg, FILE* dest) {}
int pre_isset_macro(int argc, char* arg, FILE* dest) {}
int pre_filebegin_macro(int argc, char* arg, FILE* dest) {}
int pre_getter_macro(int argc, char* arg, FILE* dest) {}
int pre_setter_macro(int argc, char* arg, FILE* dest) {}
int pre_xetter_macro(int argc, char* arg, FILE* dest) {}

void call_macro(const char* macroname, int argc, char* argwordlist,
                FILE* dest){

    int worked = 0;

    if(!strcmp(macroname, MACRO_INCLUDE)){
        worked = pre_include_macro(argc, argwordlist, dest);
    }else if(!strcmp(macroname, MACRO_NOSTANDARD)){
        worked = 1;
    }else if(!strcmp(macroname, MACRO_FLAG)){
        worked = pre_flag_macro(argc, argwordlist, dest);
    }else if(!strcmp(macroname, MACRO_ISSET)){
        worked = pre_isset_macro(argc, argwordlist, dest);
    }else if(!strcmp(macroname, MACRO_FILEBEGIN)){
        worked = pre_filebegin_macro(argc, argwordlist, dest);
    }else if(!strcmp(macroname, MACRO_GETTER)){
        worked = pre_getter_macro(argc, argwordlist, dest);
    }else if(!strcmp(macroname, MACRO_SETTER)){
        worked = pre_setter_macro(argc, argwordlist, dest);
    }else if(!strcmp(macroname, MACRO_XETTER)){
        worked = pre_xetter_macro(argc, argwordlist, dest);
    }else{
        macro_not_found_err(macroname);
    }

}

void shortenfile(FILE* fp, int len){
    fseeko(fp,-len,SEEK_END);
    off_t position = ftello(fp);
    ftruncate(fileno(fp), position);
}

void preprocess_file(FILE* src, FILE* dst){
    char c;
    char c0;

    int scan_macroname_mode = 0;
    int scan_macroargs_mode = 0;
    int string_mode = 0;
    int char_mode = 0;

    int single_comment_mode = 0;
    int multi_comment_mode = 0;

    int chardeletecount = 0;
    astring macroname = create_astring("");
    astring macroargs = create_astring(""); //seperated by space
    int lastargc = 0;

    while ((c = fgetc(src)) != EOF)
    {
        if(!single_comment_mode || !multi_comment_mode){
            if(c == '"'){
                if(!char_mode && c0 != '\\'){
                    string_mode = !string_mode;
                }
            }

            if(c == '\''){
                if(!string_mode){
                    char_mode = !char_mode;
                }
            }
        }

        if(!char_mode || !string_mode){
            if(c == COMMENT_SINGLE){
                single_comment_mode = 1;
            }

            if(single_comment_mode && c == '\n'){
                single_comment_mode = 0;
            }

            if(c == COMMENT_MULTI_BEGIN_1){
                char c1 = fgetc(src);
                if(c1 == COMMENT_MULTI_BEGIN_2){
                    single_comment_mode = 0;
                    multi_comment_mode = 1;
                }
                fseek(src, -1, SEEK_CUR);
            }

            if(c == COMMENT_MULTI_END_2){
                if(c0 == COMMENT_MULTI_END_1){
                    multi_comment_mode = 0;
                }
            }
        }

        if(!single_comment_mode || !multi_comment_mode){
            fputc(c,dst);
        }

        if(!single_comment_mode || !multi_comment_mode || !string_mode || !char_mode){

            if(scan_macroname_mode || scan_macroargs_mode){
                ++chardeletecount;
                if(c == MACRO_END){
                    scan_macroargs_mode = 0;
                    scan_macroname_mode = 0;
                    shortenfile(dst, chardeletecount);
                    call_macro(macroname.string, lastargc, macroargs.string, dst);
                    chardeletecount = 0;
                    macroname = create_astring("");
                    macroargs = create_astring("");
                    lastargc = 0;
                }

                if(scan_macroname_mode){
                    if(c == ' '){
                        scan_macroargs_mode = 1;
                        scan_macroname_mode = 0;
                        ++lastargc;
                    }else{
                        safeappend_astring(&macroname, c);
                    }
                }else if(scan_macroargs_mode){
                    if(c == ','){
                        safeappend_astring(&macroargs, " ");
                        ++lastargc;
                    }else{
                        safeappend_astring(&macroargs, c);
                    }
                }

            }
            if(c == MACRO_OP){
                if(!scan_macroname_mode){
                    ++chardeletecount;
                }
                scan_macroname_mode = 1;
            }
        }




        c0 = c;
    }
}

void insert_standard_lib(FILE* realfile, FILE* tempfile){

}


/*
 * FILE* fp: file pointer to the target.mon file which will be preprocessed/ compiled
 * FILE* processedfp: file pointer to the target.monp where the processed version is stored
 * FILE* tempfile: file pointer to target.monpt where subparts during processing are stored
 */

CompilerInfo mondpre(FILE* fp, FILE* processedfp, FILE *tempfile, int argc, char *argv[]){

    int include_macroleft = 0;
    int nostandard_macroleft = 0;

    /*
     * only detects macros which are recognized
     */
    int nomacro_left = 0;

    int *builtfileends[MAX_FILEENDS];

    CompilerInfo compilerInfo = {
        .fileends = builtfileends
    };
    free(builtfileends);
    return compilerInfo;
}



