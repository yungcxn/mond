#ifndef ASTRING_H
#define ASTRING_H

typedef struct astring {
    size_t memsize;
    char string[];
} astring;

typedef astring* astring_ptr;

astring_ptr create_astring(const char* str){
    unsigned int v = strlen(str) + 1;

    v--;
    v |= v >> 1;
    v |= v >> 2;
    v |= v >> 4;
    v |= v >> 8;
    v |= v >> 16;
    v++;

    astring_ptr astr = (astring_ptr) malloc(sizeof(astring) + v);
    astr->memsize = v;
    strcpy(astr->string, str);

    return astr;
}

void safeset_astring(astring_ptr* astr, const char *str){
    size_t reallen = strlen(str)+1;

    int i = 0;
    unsigned int fmemsize = (*astr)->memsize;

    while(reallen > fmemsize){
        fmemsize *= 2;
        if(!i){
            i = 1;
        }
    }

    if(i){

        *astr = (astring_ptr) realloc(*astr, sizeof(astring) + fmemsize);
    }

    (*astr)->memsize = fmemsize;

    strcpy((*astr)->string, str);
}

void free_astring(astring_ptr astr){
    free(astr);
}

void sfree_astring(astring_ptr astr){
    if(astr == NULL){
        return;
    }

    free_astring(astr);
}

void safeappend_astring(astring_ptr* astr, const char *str){
    char begin[strlen((*astr)->string)+1];
    strcpy(begin, (*astr)->string);
    size_t reallen = strlen(begin)+ strlen(str)+1;

    int i = 0;
    unsigned int fmemsize = (*astr)->memsize;

    while(reallen > fmemsize){
        fmemsize *= 2;
        if(!i){
            i = 1;
        }
    }

    if(i){

        *astr = (astring_ptr) realloc(*astr, sizeof(astring) + fmemsize);
    }

    (*astr)->memsize = fmemsize;
    strcpy((*astr)->string, begin);
    strcat((*astr)->string, str);
}

void safeappendc_astring(astring_ptr* astr, const char c){
    char begin[strlen((*astr)->string)+1];
    strcpy(begin, (*astr)->string);
    size_t reallen = strlen(begin)+2;

    int i = 0;
    unsigned int fmemsize = (*astr)->memsize;

    while(reallen > fmemsize){
        fmemsize *= 2;
        if(!i){
            i = 1;
        }
    }

    if(i){

        *astr = (astring_ptr) realloc(*astr, sizeof(astring) + fmemsize);
    }

    (*astr)->memsize = fmemsize;
    strcpy((*astr)->string, begin);
    (*astr)->string[reallen-2] = c;
    (*astr)->string[reallen-1] = '\0';
}

int astrlen(const astring_ptr astr){
    return(strlen(astr->string));
}

#endif