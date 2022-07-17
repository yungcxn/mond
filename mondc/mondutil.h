#ifndef MONDC_MONDUTIL_H
#define MONDC_MONDUTIL_H

#define FILESEP "//"

typedef struct pstring {
    size_t memsize;
    char *string;
} pstring;


int pstrlen(const pstring pstr){
    return(strlen(pstr.string));
}

pstring create_pstring(const char* str){
    unsigned int v = strlen(str) + 1;

    v--;
    v |= v >> 1;
    v |= v >> 2;
    v |= v >> 4;
    v |= v >> 8;
    v |= v >> 16;
    v++;

    pstring pstr = {.memsize = v, .string = str};
    return pstr;
}
void safeset_pstring(pstring *pstr, const char *str){
    size_t reallen = strlen(str)+1;
    while(reallen > pstr->memsize){
        pstr->memsize *= 2;
    }
    pstr->string = (char*) malloc(pstr->memsize);
    printf("%d\n", strlen(str));
    printf("%d\n", pstr->memsize);
    strcpy(pstr->string, str);
}

void safeappend_pstring(pstring *mstr, const char *str){
    safeset_pstring(mstr, strcat(mstr->string, str));
}

void pstring_to_arr(const pstring mstr, char *buf[]){
    strcpy(buf, mstr.string);
}

typedef struct astring {
    size_t memsize;
    char string[];
} astring;

astring create_astring(const char* str){
    unsigned int v = strlen(str) + 1;

    v--;
    v |= v >> 1;
    v |= v >> 2;
    v |= v >> 4;
    v |= v >> 8;
    v |= v >> 16;
    v++;

    astring *astr = (astring*) malloc(sizeof(astring) + v);
    return *astr;
}

void safeset_astring(astring *astr, const char *str){
    size_t reallen = strlen(str)+1;
    while(reallen > astr->memsize){
        astr->memsize *= 2;
    }
    astr = (astring*) malloc(sizeof(astring) + astr->memsize);
    printf("%d\n", strlen(str));
    printf("%d\n", astr->memsize);
    strcpy(astr->string, str);
}

void safeappend_astring(astring *astr, const char *str){
    safeset_astring(astr, strcat(astr->string, str));
}

int astrlen(const astring astr){
    return(strlen(astr.string));
}

void logerr(char* prefix, char* suffix){
    printf("%s %s\n", prefix, suffix);
}

void macro_not_found_err(char* name){
    logerr("[macro]", strcat(name, " not found!"));
}

char* getfilename(const char* path){
    char buf[FILENAME_MAX];
    for(int i = 0; i<strlen(path); i++){
        char c = path[i];
        if(c == FILESEP){
            strcpy(buf, "");
            continue;
        }
        strncat(buf, c, 1);
    }
    return buf;
}

#endif
