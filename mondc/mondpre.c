#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "mondutil.h"
#include "mondpre.h"

/*
 * TODO:
 * 1. stop using pstring / char* for file saving
 * 2. cross include ????
 * 3. set os flags
 */

typedef struct CompilerInfo {

    FILE* newfile;
    int* fileends;

} CompilerInfo;

astring initial_file;
int import_standard_lib = 1;

char* pre_readfile(FILE* fp){
    fseek(fp, 0L, SEEK_END);
    int filesize = ftell(fp);
    fseek(fp, 0L, SEEK_SET);
    char *contentout = malloc(filesize+1);
    size_t red = fread(*contentout, 1, filesize, fp);
    contentout[red] = 0;
    return *contentout;
}

/*  removing macros after use   */
void pre_delete_in_initial(int position){
    initial_file.string[position] = ' ';
}

void pre_delete_in_initial_ranged(int begin, int end){
    for(int i = begin; i <=end; i++){
        pre_delete_in_initial(i);
    }
}

void pre_delete_comments(){

    int singlecomment_mode = 0;
    int multicomment_mode = 0;
    int string_mode = 0;
    int char_mode = 0;

    for(int i = 0; i< astrlen(initial_file); i++){
        char c = initial_file.string[i];

        if(c == '"'){
            if(!char_mode && initial_file.string[i-1] != '\\'){
                string_mode = !string_mode;
            }
        }

        if(c == '\''){
            if(!string_mode){
                char_mode = !char_mode;
            }
        }

        if(string_mode || char_mode){
            continue;
        }

        if(c == COMMENT_SINGLE){
            singlecomment_mode = 1;
        }

        if(singlecomment_mode && c == '\n'){
            singlecomment_mode = 0;
        }

        if(c == COMMENT_MULTI_BEGIN_1){
            if(initial_file.string[i+1] == COMMENT_MULTI_BEGIN_2){
                singlecomment_mode = 0;
                multicomment_mode = 1;
            }
        }

        if(singlecomment_mode || multicomment_mode){
            pre_delete_in_initial(i);
        }

        if(c == COMMENT_MULTI_END_2){
            if(initial_file.string[i-1] == COMMENT_MULTI_END_1){
                multicomment_mode = 0;
            }
        }



    }
}

int pre_include_macro(const int argc, char* arg, const int execpos) {}
int pre_flag_macro(const int argc, char* arg, const int execpos) {}
int pre_isset_macro(const int argc, char* arg, const int execpos) {}
int pre_filebegin_macro(const int argc, char* arg, const int execpos) {}
int pre_getter_macro(const int argc, char* arg, const int execpos) {}
int pre_setter_macro(const int argc, char* arg, const int execpos) {}
int pre_xetter_macro(const int argc, char* arg, const int execpos) {}

void call_macro(const char* macroname, const int argc, const char* argwordlist,
                const size_t execbegin, const size_t execend){

    int worked = 0;

    if(!strcmp(macroname, MACRO_INCLUDE)){
        pre_delete_in_initial_ranged(execbegin, execend);
        worked = pre_include_macro(argc, argwordlist, execbegin);
    }else if(!strcmp(macroname, MACRO_NOSTANDARD)){
        pre_delete_in_initial_ranged(execbegin, execend);
        import_standard_lib = 0;
        worked = 1;
    }else if(!strcmp(macroname, MACRO_FLAG)){
        pre_delete_in_initial_ranged(execbegin, execend);
        worked = pre_flag_macro(argc, argwordlist, execbegin);
    }else if(!strcmp(macroname, MACRO_ISSET)){
        pre_delete_in_initial_ranged(execbegin, execend);
        worked = pre_isset_macro(argc, argwordlist, execbegin);
    }else if(!strcmp(macroname, MACRO_FILEBEGIN)){
        pre_delete_in_initial_ranged(execbegin, execend);
        worked = pre_filebegin_macro(argc, argwordlist, execbegin);
    }else if(!strcmp(macroname, MACRO_GETTER)){
        pre_delete_in_initial_ranged(execbegin, execend);
        worked = pre_getter_macro(argc, argwordlist, execbegin);
    }else if(!strcmp(macroname, MACRO_SETTER)){
        pre_delete_in_initial_ranged(execbegin, execend);
        worked = pre_setter_macro(argc, argwordlist, execbegin);
    }else if(!strcmp(macroname, MACRO_XETTER)){
        pre_delete_in_initial_ranged(execbegin, execend);
        worked = pre_xetter_macro(argc, argwordlist, execbegin);
    }else{
        macro_not_found_err(macroname);
    }

}

/*
 * returns boolean if macro successfully found and processed
 * executes only the given macro nametosearch, not multiple
 */
int pre_scanfor_macro(const char* nametosearch){
    int scanmacro_mode = 0;
    size_t scanmacro_charpos = -1;
    size_t scanmacro_endpos;
    int parsingargs_mode = 0;
    int string_mode = 0;
    int char_mode = 0;

    int macro_argc;
    pstring macro_argstr;
    pstring macroname;

    for(size_t i = 0; i<strlen(initial_file.string); i++){
        char c = initial_file.string[i];

        if(c == '"'){
            if(!char_mode && initial_file.string[i-1] != '\\'){
                string_mode = !string_mode;
            }
        }

        if(c == '\''){
            if(!string_mode){
                char_mode = !char_mode;
            }
        }

        if(string_mode || char_mode){
            continue;
        }

        if(parsingargs_mode){
            macro_argstr = create_pstring("");
            if(c != ';' && c != '\n'){
                if(c == ','){
                    safeappend_pstring(&macro_argstr, ' ');
                    ++macro_argc;
                }else{
                    safeappend_pstring(&macro_argstr, c);
                }
            }else {
                parsingargs_mode = 0;

                if(pstrlen(macro_argstr) != 0){ //if there is an argument
                    ++macro_argc;
                }

                call_macro(macroname.string, macro_argc, macro_argstr.string, scanmacro_charpos-1, i);

                return 1;
            }
        }

        if(scanmacro_mode){
            if(scanmacro_charpos == -1){
                if(c == " "){
                    scanmacro_mode = 0;
                    continue;
                }
                scanmacro_charpos = i;
            }

            if(c == ' ' || c == ';'){
                scanmacro_endpos = i-1;

                macroname = create_pstring("");
                for(int a = 0; a < scanmacro_endpos - scanmacro_charpos; a++){
                    safeappend_pstring(&macroname,initial_file.string[scanmacro_charpos + a]);
                }

                if(strcmp(nametosearch, macroname.string)){
                    scanmacro_mode = 0;
                }else{
                    scanmacro_mode = 0;
                    scanmacro_charpos = -1;
                    scanmacro_endpos = 0;
                    parsingargs_mode = 1;
                }

            }
        }else if(c == '%'){
            scanmacro_mode = 1;
        }
    }
    return 0;


}
/*
 * FILE* fp: file pointer to the target.mon file which will be preprocessed/ compiled
 * FILE* processedfp: file pointer to the target.monp where the processed version is stored
 */

CompilerInfo mondpre(FILE* fp, const FILE* processedfp, int argc, char *argv[]){

    int include_macroleft = 0;
    int nostandard_macroleft = 0;

    int *builtfileends[MAX_FILEENDS];

    initial_file = create_astring(pre_readfile(fp));

    pre_delete_comments();

    while(!nostandard_macroleft) {
        nostandard_macroleft = pre_scanfor_macro(MACRO_NOSTANDARD);
    }

    while(!include_macroleft) {
        include_macroleft = pre_scanfor_macro(MACRO_INCLUDE);
    }

    CompilerInfo compilerInfo = {
        .fileends = builtfileends
    };

    fclose(newfile);
    free(builtfileends);
    return compilerInfo;
}



