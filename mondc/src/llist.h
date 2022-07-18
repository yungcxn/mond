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

ll_string* ll_string_delete0(ll_string* head){
    return head->next;
}
/*
 * returns boolean
 */
int ll_string_contains(ll_string* head, char* ptr){
    ll_string* current = NULL;
    for(current = head; current != NULL; current = current->next){
        if(!strcmp(head->item, ptr)){
            return 1;
        }
    }
    return 0;
}

int ll_string_at(ll_string* head, char* ptr){
    int i = 0;
    ll_string* current = NULL;
    for(current = head; current != NULL; current = current->next){
        if(!strcmp(head->item, ptr)){
            return i;
        }
        ++i;
    }
    return i;
}

ll_string* ll_string_delete(ll_string* head, int index){
    if(index == 0){
        return head->next;
    }

    int i = 0;
    ll_string* current = NULL;
    for(current = head; current != NULL; current = current->next){
        if(i-1 == index){
            ll_string* temp = head->next;
            head = temp->next;
        }
        ++i;
    }
    return head;

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

void ll_string_concat(ll_string **head, const ll_string* tocat){
    ll_string_reverse(*head);
    ll_string* current = NULL;
    for(current = tocat; current != NULL; current = current->next){
        *head = ll_string_insert(*head, current);
    }
    ll_string_reverse(*head);
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