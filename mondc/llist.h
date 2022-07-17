#ifndef LLIST_H
#define LLIST_H

#include <stdarg.h>
#include <string.h>
#include <stdlib.h>
#include "mondutil.h"


typedef struct ll_string{
    char item[1024];
    struct stringitem* next;
} ll_string;

ll_string* ll_string_insert(ll_string* head, char* ptr){
    ll_string* temp = malloc(sizeof(struct ll_string));
    strcpy(temp->item, ptr);
    temp->next = head;
    return temp;
}

int ll_string_hasnext(const ll_string* ll){
    return ll->next != NULL;
}

void ll_string_reverse(ll_string** ll){
    ll_string* prev = NULL;
    ll_string* current = *ll;
    ll_string* next = NULL;

    while(current != NULL){
        next = current->next;
        current->next = prev;
        prev = current;
        current = next;
    }

    *ll = prev;
}

void ll_string_iter(ll_string* toiter, void (*function)(void*)){
    ll_string* current = NULL;
    for(current = toiter; current != NULL; current = current->next){
        (*function)(current);
    }
}

void ll_string_print_single(ll_string* ll){
    printf("%s\n", ll->item);
}


/*
 * puts value at index before the neighbour
 */
void ll_string_pull_value(ll_string** ll, int index){
    if(index == 0){
        return;
    }
    ll_string* current = *ll;
    ll_string* before = NULL;
    for(int i = 0; i<index; i++){
        before = current;
        current = current->next;
        if(current == NULL){
            return;
        }
    }

    char* temp = malloc(sizeof(current->item));
    strcpy(temp, current->item);
    strcpy(current->item, before->item);
    strcpy(before->item, temp);
    free(temp);

}

#endif