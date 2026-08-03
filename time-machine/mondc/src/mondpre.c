#include <stdio.h>
#include <string.h>
#include "util/mondutil.h"
#include "mondpre.h"
#include "util/llist.h"
#include "macrogen.h"
#include <limits.h>
#include "util/astring.h"
#include "mondc.h"

astring_ptr pp_flags = NULL;

/*
 * is called before preprocessing begins. works the same way a common c compiler uses macro defs for giving info about the
 * os or cpu architecture
 */
void add_sysdefined_flags(astring_ptr* flags){
    safeappend_astring(flags, MONDC_OS_FLAG);
    safeappendc_astring(flags, ' ');

}

/*
 * this only checks if a given string matches a macro that doesn't include files
 */
int is_macro(char* ptr){

    if(!strcmp(ptr, MACRO_FLAG)){
        return 1;
    }
    if(!strcmp(ptr, MACRO_ISSET)){
        return 1;
    }
    if(!strcmp(ptr, MACRO_GETTER)){
        return 1;
    }
    if(!strcmp(ptr, MACRO_SETTER)){
        return 1;
    }
    if(!strcmp(ptr, MACRO_XETTER)){
        return 1;
    }
    return 0;
}

/*
 * macrofunctions are writing via dest filepointer at the current position the mondpre stopped at
 * therefore: parsing arguments for get/set/xet macro since args are given in space-separated list
 */
void parse_get_set_macro_args(int argc, char* argwordlist, astring_ptr* accessmod, astring_ptr* typename, astring_ptr* fieldname){

    if(argc == 3){
        int nextarg = 1;
        for(int i = 0; i< strlen(argwordlist);i++){
            char c = argwordlist[i];
            if(c == ' '){
                ++nextarg;
                continue;
            }
            if(nextarg == 1){
                safeappendc_astring(accessmod, c);
            }else if(nextarg == 2){
                safeappendc_astring(typename, c);
            }else if(nextarg == 3){
                safeappendc_astring(fieldname, c);
            }

        }
    }else if(argc == 2){
        int nextarg = 1;
        for(int i = 0; i< strlen(argwordlist);i++){
            char c = argwordlist[i];
            if(c == ' '){
                ++nextarg;
                continue;
            }

            else if(nextarg == 1){
                safeappendc_astring(typename, c);
            }else if(nextarg == 2){
                safeappendc_astring(fieldname, c);
            }

        }
    }else if(argc == 1){
        for(int i = 0; i< strlen(argwordlist);i++){
            char c = argwordlist[i];
            safeappendc_astring(fieldname, c);
        }
    }

    if(astrlen(*typename) == 0){
        safeset_astring(typename, "(typeof ");
        safeappend_astring(typename, (*fieldname)->string);
        safeappend_astring(typename, ")");
    }

}

/*
 * defines all flags given in argwordlist separated by space
 */
int pre_flag_macro(int argc, char* argwordlist, FILE* dest) { //dest unused

    /*
     * this called with multiple args is okay with the format of pp_flags;
     */

    if(astrlen(pp_flags) == 0){
        safeset_astring(&pp_flags, argwordlist);
    }else{
        safeappend_astring(&pp_flags, " ");
        safeappend_astring(&pp_flags, argwordlist);
    }

    return 1;
}

/*
 * produces boolean in mond syntax, true or false
 */
int pre_isset_macro(int argc, char* argwordlist, FILE* dest) {
    if(argc != 1){
        return 0;
    }

    char* result = FALSE_EXPR; //since > TRUE_EXPR for bigger buffer length
    if(strstr(pp_flags->string, argwordlist) != NULL){
        result = TRUE_EXPR;
    }

    fputc(' ', dest); //padding for lexing
    for(int i = 0; i<strlen(result);i++){
        fputc(result[i], dest);
    }
    fputc(' ', dest); //padding for lexing

    return 1;
}

/*
 * produces getter method
 */
int pre_getter_macro(int argc, char* argwordlist, FILE* dest) {

    astring_ptr typename = create_astring("");
    astring_ptr fieldname = create_astring("");
    astring_ptr accessmod = create_astring("");

    parse_get_set_macro_args(argc, argwordlist, &accessmod, &typename, &fieldname);

    /*
     * file writing manually with macros in macrogen.h
     */
    if(astrlen(accessmod) != 0){
        fputs(accessmod->string, dest);
    }

    fputc(' ', dest);
    fputs(typename->string, dest);
    fputs(GETTER1, dest);
    fputs(fieldname->string, dest);
    fputs(GETTER2, dest);
    fputs(fieldname->string, dest);
    fputs(GETTER3, dest);

    sfree_astring(accessmod);
    sfree_astring(typename);
    sfree_astring(fieldname);

    return 1;
}

/*
 * produces setter method
 */
int pre_setter_macro(int argc, char* argwordlist, FILE* dest) {
    astring_ptr typename = create_astring("");
    astring_ptr fieldname = create_astring("");
    astring_ptr accessmod = create_astring("");

    parse_get_set_macro_args(argc, argwordlist, &accessmod, &typename, &fieldname);

    /*
     * file writing manually with macros in macrogen.h
     */
    if(astrlen(accessmod) != 0){
        fputs(accessmod->string, dest);
    }

    fputs(SETTER1, dest);
    fputs(fieldname->string, dest);
    fputs(SETTER2, dest);
    fputs(typename->string, dest);
    fputs(SETTER3, dest);
    fputs(fieldname->string, dest);
    fputs(SETTER4, dest);

    sfree_astring(accessmod);
    sfree_astring(typename);
    sfree_astring(fieldname);

    return 1;
}

/*
 * produces both getter and setter methods
 */
int pre_xetter_macro(int argc, char* argwordlist, FILE* dest) {
    pre_getter_macro(argc, argwordlist, dest);
    pre_setter_macro(argc, argwordlist, dest);

    return 1;
}


/*
 * argwordlist are strings separated by a space, not parsed, passed directly onto macrofunction
 */
void call_macro(const char* macroname, int argc, char* argwordlist,
                FILE* dest){

    int worked = 0;

    if(!strcmp(macroname, MACRO_FLAG)){
        worked = pre_flag_macro(argc, argwordlist, dest);
    }else if(!strcmp(macroname, MACRO_ISSET)){
        worked = pre_isset_macro(argc, argwordlist, dest);
    }else if(!strcmp(macroname, MACRO_GETTER)){
        worked = pre_getter_macro(argc, argwordlist, dest);
    }else if(!strcmp(macroname, MACRO_SETTER)){
        worked = pre_setter_macro(argc, argwordlist, dest);
    }else if(!strcmp(macroname, MACRO_XETTER)){
        worked = pre_xetter_macro(argc, argwordlist, dest);
    }

    if(!worked){
        char errmsg[100];
        sprintf(errmsg, "encountered error during %s with (%s)", macroname, argwordlist);
        reporterror(errmsg, 0);
    }

}

/*
 * linkedlist to keep track of already imported files
 */
ll_string* included_list = NULL;

/*
 * keeps track of lines in the processedfile
 */
int overall_linecount = 1;

/*
 * recursive function which always writes to FILE* dst, but changes the cwd according to the next file
 * that needs to be imported and starts to write at the same place but reads from the new file.
 * recursion allows the preprocessor to write the end of the file after the inclusion is done,
 * inclusions after inclusions in the right order aswell
 */
void recursive_incl_pp_file(FILE* src, FILE* dst, char* cwdpath){

    char c;
    char c0 = '\0';
    char c00 = '\0';

    int scan_macroname_mode = 0;
    int scan_macroargs_mode = 0;
    int macroargs_string_mode = 0;
    int string_mode = 0;
    int char_mode = 0;

    int single_comment_mode = 0;
    int multi_comment_mode = 0;

    int chardeletecount = 0;
    astring_ptr macroname = create_astring("");
    astring_ptr macroargs = create_astring(""); //seperated by space
    int lastargc = 0;

    /*
     * keeps track of the current line red in FILE* src
     */
    int templinecount = 1;

    while ((c = fgetc(src)) != EOF) //NOLINT
    {
        if(!single_comment_mode || !multi_comment_mode){
            if(c == '"'){
                if(!char_mode && c0 != '\\'){
                    string_mode = !string_mode;
                }
            }

            if(c == '\''){
                if(!string_mode && c0 != '\\'){
                    char_mode = !char_mode;
                }
            }
        }

        if(!char_mode && !string_mode){
            if(c == COMMENT_SINGLE){
                single_comment_mode = 1;
            }

            if(single_comment_mode && c == '\n'){
                single_comment_mode = 0;
            }

            if(c == COMMENT_MULTI_BEGIN_1){
                char c1 = fgetc(src); //NOLINT
                if(c1 == COMMENT_MULTI_BEGIN_2){
                    single_comment_mode = 0;
                    multi_comment_mode = 1;
                }
                fseek(src, -1, SEEK_CUR);
            }
            if(c0 == COMMENT_MULTI_END_2 && multi_comment_mode){
                if(c00 == COMMENT_MULTI_END_1){
                    multi_comment_mode = 0;
                }
            }
        }

        if(!single_comment_mode && !multi_comment_mode){
            fputc(c,dst);
        }

        if(!single_comment_mode && !multi_comment_mode && !string_mode && !char_mode){
            if(scan_macroname_mode || scan_macroargs_mode){
                ++chardeletecount;
                if(c == MACRO_END && !macroargs_string_mode){

                    scan_macroname_mode = 0;
                    scan_macroargs_mode = 0;

                    if(!strcmp(macroname->string, MACRO_INCLUDE)){
                        shortenfile(dst, chardeletecount);

                        char newpath[PATH_MAX] = {0};

                        /*
                         * the following line indicates the syntax for lib includes
                         * if no MOND_FILE_EXT is given; search in MONDLIB_LOC, not cwdpath
                         */
                        if(strstr(macroargs->string, MOND_FILE_EXT) == NULL){
                            strcpy(newpath, MONDLIB_LOC);
                            strcat(newpath, macroargs->string);
                            strcat(newpath, MOND_FILE_EXT);
                        }else{
                            strcpy(newpath, cwdpath);
                            strncat(newpath, &FILESEP, 1);
                            strcat(newpath,macroargs->string);
                        }

                        if(!ll_string_contains(included_list, newpath)){

                            FILE* newf = fopen(newpath, "r");

                            included_list = ll_string_insert(included_list, newpath);

                            if(newf == NULL){
                                char msg[PATH_MAX];
                                sprintf(msg, "Error during preprocessing in %s, line %d", newpath, templinecount);
                                reporterror(msg, 5);
                            }

                            if(fsize(newf) == 0){
                                dbg_logline("file to be preprocessed empty; skipped!");
                            }else{
                                char* containingdir = get_containing_dir(newpath);
                                recursive_incl_pp_file(newf, dst, containingdir);
                                free(containingdir);
                            }

                            fclose(newf);
                        }else{
                            dbg_logline("already included file skipped!");
                        }

                    }else if(is_macro(macroname->string)){
                        shortenfile(dst, chardeletecount);
                        call_macro(macroname->string, lastargc, macroargs->string, dst);
                    }

                    chardeletecount = 0;
                    safeset_astring(&macroname, "");
                    safeset_astring(&macroargs, "");
                    lastargc = 0;
                }

                if(scan_macroname_mode){
                    if(c == ' '){
                        scan_macroargs_mode = 1;
                        scan_macroname_mode = 0;
                        macroargs_string_mode = 0;
                        ++lastargc;
                    }else{
                        safeappendc_astring(&macroname, c);
                    }
                }else if(scan_macroargs_mode){
                    if(c == '"'){
                        macroargs_string_mode = !macroargs_string_mode;
                    }
                    else if(c == ',' && !macroargs_string_mode){
                        safeappendc_astring(&macroargs, ' ');
                        ++lastargc;
                    }else{
                        if(macroargs_string_mode){
                            safeappendc_astring(&macroargs, c);
                        }else if(c != ' '){
                            safeappendc_astring(&macroargs, c);
                        }

                    }
                }

            }
            if(c == MACRO_OP && !macroargs_string_mode){
                if(!scan_macroargs_mode){
                    chardeletecount = 1;
                    scan_macroname_mode = 1;
                    scan_macroargs_mode = 0;
                    macroargs_string_mode = 0;
                    safeset_astring(&macroname, "");
                    safeset_astring(&macroargs, "");
                }
            }
        }

        if(c == '\n'){
            overall_linecount++;
            templinecount++;
        }

        c00 = c0;
        c0 = c;

    }

    sfree_astring(macroname);
    sfree_astring(macroargs);

}

/*
 * FILE* fp: file pointer to the target.mon file which will be preprocessed/ compiled
 * FILE* processedfp: file pointer to the target.monp where the processed version is stored
 * FILE* tempfile: file pointer to target.monpt where subparts during processing are stored
 * char* absolutepath: the path to FILE* fp
 * char* temppath: the path to FILE* tempfile
 */
void mondpre(FILE* fp, FILE* processedfile,
             char* absolutepath, char* buildpath, int argc, char *argv[]){
    pp_flags = create_astring("");
    add_sysdefined_flags(&pp_flags);

    dbg_logpre();dbg_logs("current ppflags: ");dbg_logs(pp_flags->string);dbg_logn();

    /*
     * resetting both values for safety reasons
     */
    included_list = NULL;
    overall_linecount = 1;

    recursive_incl_pp_file(fp, processedfile, absolutepath);

    sfree_astring(pp_flags);
}
