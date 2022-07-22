
/*
 * TODO:
 * - cross include ????
 */

#include <stdio.h>
#include <string.h>
#include "util/mondutil.h"
#include "mondpre.h"
#include "util/llist.h"
#include "macrogen.h"
#include <unistd.h>
#include <limits.h>
#include "util/astring.h"
#include "mondc.h"

typedef struct CompilerInfo {
    int fileends[MAX_FILE_INCLUDES];
    astring_ptr flags;
} CompilerInfo;

astring_ptr pp_flags = NULL;

void add_sysdefined_flags(astring_ptr* flags){
    safeappend_astring(flags, MONDC_OS_FLAG);
    safeappendc_astring(flags, ' ');

}

/*
 * macrofunctions are writing via dest filepointer at the current position the mondpre stopped at
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
      //TODO
    }

}

void shortenfile(FILE* fp, int len){
    fseeko(fp,-len,SEEK_END);
    off_t position = ftello(fp);
    ftruncate(fileno(fp), position);
    dbg_logpre();dbg_logs("shortened file by -");dbg_logi(len);dbg_logn();
}

/*
 * returns whether a file-importing macro (e.g. %incl) was found
 * nostandard_called is 0 by default
 */
ll_string* preprocess_file(int only_includes, FILE* src, FILE* dst, int* nostandard_called){

    char c;
    char c0 = '\0';
    char c00 = '\0';

    int scan_macroname_mode = 0;
    int scan_macroargs_mode = 0;
    int string_mode = 0;
    int char_mode = 0;

    int single_comment_mode = 0;
    int multi_comment_mode = 0;

    int chardeletecount = 0;
    astring_ptr macroname = create_astring("");
    astring_ptr macroargs = create_astring(""); //seperated by space
    int lastargc = 0;

    ll_string* inclusion_directives = NULL;

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
            dbg_logc(c);
        }

        if(!single_comment_mode && !multi_comment_mode && !string_mode && !char_mode){
            if(scan_macroname_mode || scan_macroargs_mode){
                ++chardeletecount;
                if(c == MACRO_END){
                    dbg_logline("pp -> found endmacro character");
                    scan_macroname_mode = 0;
                    scan_macroargs_mode = 0;

                    if(!strcmp(macroname->string, MACRO_INCLUDE) && only_includes){
                        shortenfile(dst, chardeletecount);
                        inclusion_directives = ll_string_insert(inclusion_directives, macroargs->string);
                    }else if(!strcmp(macroname->string, MACRO_NOSTANDARD) && only_includes){
                        shortenfile(dst, chardeletecount);
                        *nostandard_called = 1;
                    }else{
                        if(!only_includes){
                            shortenfile(dst, chardeletecount);
                            call_macro(macroname->string, lastargc, macroargs->string, dst);
                        }
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
                        safeappendc_astring(&macroname, c);
                    }
                }else if(scan_macroargs_mode){
                    if(c == ','){
                        safeappendc_astring(&macroargs, ' ');
                        ++lastargc;
                    }else{
                        if(c != ' '){
                            safeappendc_astring(&macroargs, c);
                        }

                    }
                }

            }
            if(c == MACRO_OP){
                if(!scan_macroargs_mode){
                    ++chardeletecount;
                    scan_macroname_mode = 1;
                }
            }
        }

        c00 = c0;
        c0 = c;

    }

    sfree_astring(macroname);
    sfree_astring(macroargs);

    return inclusion_directives;
}

/*
 * FILE* fp: file pointer to the target.mon file which will be preprocessed/ compiled
 * FILE* processedfp: file pointer to the target.monp where the processed version is stored
 * FILE* tempfile: file pointer to target.monpt where subparts during processing are stored
 * char* absolutepath: the path to FILE* fp
 * char* temppath: the path to FILE* tempfile
 */

CompilerInfo mondpre(FILE* fp, FILE* processedfile, FILE *tempfile, FILE* joinedfile,
                     char* absolutepath, char* buildpath, char* temppath, int argc, char *argv[]){

    pp_flags = create_astring("");
    add_sysdefined_flags(&pp_flags);
    dbg_logpre();dbg_logs("added following flags: ");dbg_logs(pp_flags->string);dbg_logn();

    /*
     * boolean which is flipped when every file to include is in it's tempfile (every macro removed)
     */
    int file_scanning_to_temps = 0;

    FILE* current_processing_file = fp;
    dbg_logline("file being processed next is first file");
    FILE* current_temp_file = tempfile;
    dbg_logline("tempfile being filled next is first file");
    char* current_processing_folder = absolutepath;

    ll_string* inclusion_dir_queue = NULL;

    /*
     * ordered list for merging files later, only file names: file.mon + pp-ext + temp-ext
     * beginning with the latest inserted file
     */
    ll_string* all_files_to_include = NULL;

    while(!file_scanning_to_temps){

        if(inclusion_dir_queue != NULL){

            fclose(current_processing_file);
            fclose(current_temp_file);

            strcpy(current_processing_folder, get_containing_dir(inclusion_dir_queue->item));

            char nextbuildfile[PATH_MAX];
            strcpy(nextbuildfile, buildpath);
            strncat(nextbuildfile, &FILESEP,1);
            strcat(nextbuildfile, getfilename(inclusion_dir_queue->item));
            strcat(nextbuildfile, PROCESSED_FILE_EXT);
            strcat(nextbuildfile, PROCESSED_TEMPFILE_EXT);

            current_processing_file = fopen(inclusion_dir_queue->item, "w+");
            current_temp_file = fopen(nextbuildfile, "w+");

            dbg_logpre();dbg_logs("file being processed next is ");dbg_logs(inclusion_dir_queue->item);dbg_logn();
            dbg_logpre();dbg_logs("tempfile being filled next is ");dbg_logs(nextbuildfile);dbg_logn();

            ll_string_delete0(&inclusion_dir_queue);
        }

        /*
         * relative filepaths to current_processing_files location
         */
        int was_nostd_called = 0;
        ll_string* inclusion_directives = preprocess_file(1, current_processing_file, current_temp_file,
                                                          &was_nostd_called);
#ifdef _DEBUG
        if(inclusion_directives == NULL){
            dbg_logline("no inclusion directives!");
        }else{
            ll_string* current = NULL;
            for(current = inclusion_directives; current != NULL; current = current->next){
                dbg_logpre();dbg_logs("added inclusion directive: ");dbg_logs(inclusion_directives->item);dbg_logn();
            }
        }
        dbg_logn();
#endif
        /*
         * only include macros are resolved and merged together at the end into
         */

        if(inclusion_directives == NULL && inclusion_dir_queue == NULL){
            file_scanning_to_temps = 1;
        }

        /*
         * inclusion_directives only got paths relative to current_processing_folder
         * this is for constructing them to absolute paths
         */
        ll_string* temp = NULL;
        if(inclusion_directives != NULL){
            for(temp = inclusion_directives; temp != NULL; temp = temp->next){

                char pathtobuild[PATH_MAX];

                if(strstr(temp->item, MOND_FILE_EXT) != strlen(temp->item)-4){ //if it's not found

                    /*
                     * here are mondlibs handled
                     */
                    strcpy(pathtobuild, MONDLIB_LOC);
                    strcat(pathtobuild, temp->item);
                    strcat(pathtobuild, MOND_FILE_EXT);
                }

                strcpy(pathtobuild, current_processing_folder);
                strncat(pathtobuild, &FILESEP, 1);
                strcat(pathtobuild, temp->item);
                strcpy(temp->item, pathtobuild);

                dbg_logpre();dbg_logs("modded inclusion directive: ");dbg_logs(pathtobuild);dbg_logn();
            }

            //standard lib is imported here
            if(!was_nostd_called){
                char stdliblocation[PATH_MAX];
                strcpy(stdliblocation, MONDLIB_LOC);
                strcat(stdliblocation,STDLIBNAME);
                ll_string_insert(&inclusion_directives, stdliblocation);
                dbg_logpre();dbg_logs("standardlib added at: ");dbg_logs(stdliblocation);dbg_logn();
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
                    ll_string_delete(
                            &inclusion_dir_queue,
                            ll_string_at(inclusion_dir_queue, link->item));
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
                    ll_string_delete(
                            &all_files_to_include,
                            ll_string_at(all_files_to_include, tempppfilename));
                }

                if(all_files_to_include != NULL){
                    ll_string_reverse(&all_files_to_include);
                }
                /*
                 * the currently imported file is concatenated at the end of the queue
                 */
                all_files_to_include = ll_string_insert(all_files_to_include, tempppfilename);

                if(all_files_to_include != NULL){
                    ll_string_reverse(&all_files_to_include);
                }
            }
        }else{
            dbg_logline("no inclusion directives to modify!");dbg_logn();
        }

        fclose(current_processing_file);
        fclose(current_temp_file);

        ll_string_free(&inclusion_directives);
    }

    /*
     * merging mode begins
     */
    dbg_logline("file-merging to .monpj begins!");

    if(all_files_to_include != NULL){
        ll_string_reverse(&all_files_to_include);
    }

    /*
     * the main .monpt is added at the end of the list
     */
    all_files_to_include = ll_string_insert(all_files_to_include, temppath);

    if(all_files_to_include != NULL){
        ll_string_reverse(&all_files_to_include);
    }

    /*
     * llist should begin with the first imported file, the more significant at the top of the list...
     */
    int linecount = 1;
    ll_int* builtfileends = NULL;

    ll_string* temp;
    for(temp = all_files_to_include; temp != NULL; temp = temp->next){

        FILE* tfile = fopen(temp->item, "r");
        if(tfile == NULL){
            reporterror("couldn't open included file to join", 5);
        }

        dbg_logpre();dbg_logs("located to merge: ");dbg_logs(temp->item);dbg_logn();

        char c;
        if(linecount != 1){

            /*
             * insert padding after every file + putting the current linecount into builtfileends
             */
            fputc('\n',joinedfile);
            builtfileends = ll_int_insert(builtfileends, ++linecount);
            dbg_logpre();dbg_logs("file separator at ");dbg_logi(linecount);dbg_logn();
        }
        while ((c = fgetc(tfile)) != EOF){ //NOLINT
            dbg_logc(c);
            if(c == '\n'){
                ++linecount;
            }
            fputc(c,joinedfile);

        }

        fclose(tfile);
    }

    /*
     * file separating linebreaks are inserted in reversed order
     */
    ll_int_reverse(&builtfileends);
    ll_int* temp_ll_int = NULL;
    int builtfileendsarr[MAX_FILE_INCLUDES];
    int i = 0;
    for(temp_ll_int = builtfileends; temp_ll_int != NULL; temp_ll_int = temp_ll_int->next){
        if(i > MAX_FILE_INCLUDES-1){
            reporterror("more files included than allowed!", 0);
        }
        builtfileendsarr[i] = temp_ll_int->item;
        ++i;
    }

    /*
     * now a merged file without include or nostd macros is available at build/example.monpj
     * return and nostandard_called bools aren't needed
     */
    fseek(joinedfile, 0, SEEK_SET);
    preprocess_file(0, joinedfile, processedfile, NULL);

    CompilerInfo compilerInfo = {
        .fileends = builtfileendsarr,
        .flags = pp_flags
    };

    sfree_astring(pp_flags);

    ll_string_free(&inclusion_dir_queue);
    ll_string_free(&all_files_to_include);

    return compilerInfo;
}
