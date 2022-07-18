
/*
 * TODO:
 * - cross include ????
 * - set os flags
 */

#include <stdio.h>
#include <string.h>
#include "mondutil.h"
#include "mondpre.h"
#include "llist.h"
#include "macrogen.h"
#include <unistd.h>
#include <limits.h>

typedef struct CompilerInfo {

    int* fileends;
    astring flags;

} CompilerInfo;

/*
 *
 */
astring pp_flags;


/*
 * macrofunctions are writing via dest filepointer at the current position the preprocessor stopped at
 */

void parse_get_set_macro_args(int argc, char* argwordlist, pstring* accessmod, pstring* typename, pstring* fieldname){
    if(argc == 3){
        int nextarg = 1;
        for(int i = 0; i< strlen(argwordlist);i++){
            char c = argwordlist[i];
            if(c == ' '){
                ++nextarg;
                continue;
            }
            if(nextarg == 1){
                safeappend_pstring(accessmod, c);
            }else if(nextarg == 2){
                safeappend_pstring(typename, c);
            }else if(nextarg == 3){
                safeappend_pstring(fieldname, c);
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
                safeappend_pstring(typename, c);
            }else if(nextarg == 2){
                safeappend_pstring(fieldname, c);
            }

        }
    }else if(argc == 1){
        for(int i = 0; i< strlen(argwordlist);i++){
            char c = argwordlist[i];
            safeappend_pstring(fieldname, c);
        }
    }

    if(pstrlen(*typename) == 0){
        safeset_pstring(typename, "(typeof ");
        safeappend_pstring(typename, fieldname->string);
        safeappend_pstring(typename, ")");
    }

}

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
    if(strstr(pp_flags.string, argwordlist) != NULL){
        result = TRUE_EXPR;
    }

    fputc(' ', dest); //padding for lexing
    for(int i = 0; i<strlen(result);i++){
        fputc(result[i], dest);
    }
    fputc(' ', dest); //padding for lexing
}

int pre_getter_macro(int argc, char* argwordlist, FILE* dest) {

    pstring typename = create_pstring("");
    pstring fieldname = create_pstring("");
    pstring accessmod = create_pstring("");

    parse_get_set_macro_args(argc, argwordlist, &accessmod, &typename, &fieldname);

    /*
     * file writing manually with macros in macrogen.h
     */
    if(pstrlen(accessmod) != 0){
        fputs(accessmod.string, dest);
    }

    fputc(' ', dest);
    fputs(typename.string, dest);
    fputs(GETTER1, dest);
    fputs(fieldname.string, dest);
    fputs(GETTER2, dest);
    fputs(fieldname.string, dest);
    fputs(GETTER3, dest);

}

int pre_setter_macro(int argc, char* argwordlist, FILE* dest) {
    pstring typename = create_pstring("");
    pstring fieldname = create_pstring("");
    pstring accessmod = create_pstring("");

    parse_get_set_macro_args(argc, argwordlist, &accessmod, &typename, &fieldname);

    /*
     * file writing manually with macros in macrogen.h
     */
    if(pstrlen(accessmod) != 0){
        fputs(accessmod.string, dest);
    }

    fputs(SETTER1, dest);
    fputs(fieldname.string, dest);
    fputs(SETTER2, dest);
    fputs(typename.string, dest);
    fputs(SETTER3, dest);
    fputs(fieldname.string, dest);
    fputs(SETTER4, dest);
}

int pre_xetter_macro(int argc, char* argwordlist, FILE* dest) {
    pre_getter_macro(argc, argwordlist, dest);
    pre_setter_macro(argc, argwordlist, dest);
}


/*
 * argwordlist are strings separated by a space, not parsed, passed directly onto macrofunction
 */
void call_macro(const char* macroname, int argc, char* argwordlist,
                FILE* dest){

    int worked = 0;

    if(!strcmp(macroname, MACRO_NOSTANDARD)){
        worked = 1;
    }else if(!strcmp(macroname, MACRO_FLAG)){
        worked = pre_flag_macro(argc, argwordlist, dest);
    }else if(!strcmp(macroname, MACRO_ISSET)){
        worked = pre_isset_macro(argc, argwordlist, dest);
    }else if(!strcmp(macroname, MACRO_GETTER)){
        worked = pre_getter_macro(argc, argwordlist, dest);
    }else if(!strcmp(macroname, MACRO_SETTER)){
        worked = pre_setter_macro(argc, argwordlist, dest);
    }else if(!strcmp(macroname, MACRO_XETTER)){
        worked = pre_xetter_macro(argc, argwordlist, dest);
    }else{

    }

}

void shortenfile(FILE* fp, int len){
    fseeko(fp,-len,SEEK_END);
    off_t position = ftello(fp);
    ftruncate(fileno(fp), position);
}

/*
 * returns whether an file-importing macro (e.g. %incl) was found
 */
int preprocess_file(FILE* src, FILE* dst){
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

    ll_string* inclusion_directives = NULL;

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
            }else if(c == COMMENT_MULTI_END_2){
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
                    if(!strcmp(macroname.string, MACRO_INCLUDE)){
                        inclusion_directives = ll_string_insert(inclusion_directives, macroargs.string);
                    }else{
                        call_macro(macroname.string, lastargc, macroargs.string, dst);
                    }

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
    return inclusion_directives;
}

void insert_standard_lib(FILE* realfile, FILE* realdest){

}

/*
 * FILE* fp: file pointer to the target.mon file which will be preprocessed/ compiled
 * FILE* processedfp: file pointer to the target.monp where the processed version is stored
 * FILE* tempfile: file pointer to target.monpt where subparts during processing are stored
 * char* absolutepath: the path to FILE* fp
 */

CompilerInfo mondpre(FILE* fp, FILE* processedfp, FILE *tempfile,
                     const char* absolutepath, const char* buildpath, int argc, char *argv[]){

    pp_flags = create_astring("");

    /*
     * boolean which is flipped when every file to include is in it's tempfile (every macro removed)
     */
    int file_scanning_to_temps = 0;

    FILE* current_processing_file = fp;
    FILE* current_temp_file = tempfile;
    char* current_processing_folder = absolutepath;

    ll_string* inclusion_dir_queue = NULL;

    /*
     * ordered list for merging files later, only file names: file.mon + pp-ext + temp-ext
     * beginning with latest inserted file
     */
    ll_string* all_files_to_include = NULL;

    while(!file_scanning_to_temps){

        if(inclusion_dir_queue != NULL){

            fclose(current_processing_file);
            fclose(current_temp_file);

            strcpy(current_processing_folder, get_containing_dir(inclusion_dir_queue->item));

            char nextbuildfile[PATH_MAX];
            strcpy(nextbuildfile, buildpath);
            strcat(nextbuildfile, getfilename(inclusion_dir_queue->item));
            strcat(nextbuildfile, PROCESSED_FILE_EXT);
            strcat(nextbuildfile, PROCESSED_TEMPFILE_EXT);

            current_processing_file = fopen(inclusion_dir_queue->item, "w+");
            current_temp_file = fopen(nextbuildfile, "w+");

            ll_string_delete0(&inclusion_dir_queue);
        }

        /*
         * relative filepaths to current_processing_files location
         */
        ll_string* inclusion_directives = preprocess_file(current_processing_file, current_temp_file);



        if(inclusion_directives == NULL && inclusion_dir_queue == NULL){
            file_scanning_to_temps = 1;
        }

        /*
         * inclusion_directives only got paths relative to current_processing_folder
         * this is for constructing them to absolute paths
         */
        ll_string* temp = NULL;
        for(temp = inclusion_directives; temp != NULL; temp = temp->next){
            char pathtobuild[PATH_MAX];

            strcpy(pathtobuild, current_processing_folder);
            strcat(pathtobuild, FILESEP);
            strcat(pathtobuild, temp->item);

            strcpy(temp->item, pathtobuild);
        }

        /*
         * last include is at front; reverse to be the last
         */
        ll_string_reverse(&inclusion_directives);
        ll_string_concat(&inclusion_dir_queue, inclusion_directives);

        ll_string* link = NULL;
        for(link = inclusion_directives; link != NULL; link = link->next){

            /*
             * does the same thing as down here...
             */
            if(ll_string_contains(inclusion_dir_queue, link->item)){
                inclusion_dir_queue = ll_string_delete(
                        inclusion_dir_queue,
                        ll_string_contains(inclusion_dir_queue, link->item));
            }

            char* inclusion_abspath = link->item;

            char tempppfilename[FILENAME_MAX];
            strcpy(tempppfilename, getfilename(inclusion_abspath));
            strcat(tempppfilename, PROCESSED_FILE_EXT);
            strcat(tempppfilename, PROCESSED_TEMPFILE_EXT);

            /*
             * if filename is already imported, delete the old one, then assign
             * since all_files_to_include is like a queue, this solves following problems:
             *
             *  1. already imported files being needed by newer processed files
             *  2. double imports
             */
            if(ll_string_contains(all_files_to_include, tempppfilename)){
                all_files_to_include = ll_string_delete(
                        all_files_to_include,
                        ll_string_contains(all_files_to_include, tempppfilename));
            }

            all_files_to_include = ll_string_insert(all_files_to_include, tempppfilename);
        }
    }

    /*
     * merging mode begins
     */

    //standard lib should be imported here

    /*
     * llist should begin with the first imported file, the more significant at the top of the list...
     */

    int linecount = 1;
    int builtfileends[2];

    ll_string_reverse(&all_files_to_include);
    ll_string* temp;
    for(temp = all_files_to_include; temp != NULL; temp = temp->next){
        char* tempfile_abspath[PATH_MAX];
        strcpy(tempfile_abspath, buildpath);
        strcat(tempfile_abspath, temp->item);
        FILE* tempfile = fopen(tempfile_abspath, "r");

        char c;
        if(linecount != 0){

            /*
             * insert padding after every file + putting the current linecount into builtfileends
             */
            fputc('\n',tempfile);
            safeappend_intarr(&builtfileends, ++linecount);
        }

        while ((c = fgetc(tempfile)) != EOF){
            if(c == '\n'){
                ++linecount;
            }
            fputc(c,processedfp);
        }

        fclose(tempfile);
    }

    CompilerInfo compilerInfo = {
        .fileends = builtfileends,
        .flags = pp_flags
    };

    fclose(current_processing_file);
    fclose(current_temp_file);

    return compilerInfo;
}
