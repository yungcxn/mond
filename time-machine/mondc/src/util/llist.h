#ifndef LLIST_H
#define LLIST_H

#include <stdarg.h>
#include <string.h>
#include <stdlib.h>
#include "mondutil.h"


typedef struct ll_string{
    char item[1024];
    struct ll_string* next;
} ll_string;

void ll_string_free(ll_string** head){
    ll_string* tmp;

    while (*head != NULL)
    {
        tmp = *head;
        *head = (*head)->next;
        free(tmp);
    }
}

ll_string* ll_string_insert(ll_string* head, char* ptr){
    ll_string* temp = malloc(sizeof(struct ll_string));
    strcpy(temp->item, ptr);
    temp->next = head;
    return temp;
}

void ll_string_delete0(ll_string** head){
    ll_string *ref = *head;
    *head = ref->next;
    free(ref);
}
/*
 * returns boolean
 */
int ll_string_contains(ll_string* head, char* ptr){
    ll_string* current = NULL;
    for(current = head; current != NULL; current = current->next){
        if(!strcmp(current->item, ptr)){
            return 1;
        }
    }
    return 0;
}

int ll_string_at(ll_string* head, char* ptr){
    int i = 0;
    ll_string* current = NULL;
    for(current = head; current != NULL; current = current->next){
        if(!strcmp(current->item, ptr)){
            return i;
        }
        ++i;
    }
    return i;
}

void ll_string_delete(ll_string** head, int index){

    if(index == 0){
        ll_string_delete0(head);
    }

    int i = 0;
    ll_string* current = *head;

    while(current != NULL){

        if(index-1 == i){
            ll_string* temp = current->next;
            current->next = temp->next;
            free(temp);
            return;
        }
        current = current->next;
        ++i;
    }
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
    ll_string_reverse(head);
    ll_string* current = tocat;
    ll_string_reverse(&current);
    while(current != NULL){
        *head = ll_string_insert(*head, current->item);
        current = current->next;
    }

    ll_string_reverse(head);
}

void ll_string_frontconcat(ll_string **head, const ll_string* tocat){
    ll_string* current = tocat;
    ll_string_reverse(&current);
    while(current != NULL){
        *head = ll_string_insert(*head, current->item);
        current = current->next;
    }

}


void ll_string_iter(ll_string* toiter, void (*function)(void*)){
    ll_string* current = NULL;
    for(current = toiter; current != NULL; current = current->next){
        (*function)(current);
    }
}

void ll_string_print(ll_string* ll){
    int first = 1;
    printf("[");
    ll_string* current = NULL;
    for(current = ll; current != NULL; current = current->next){
        if(!first){
            printf(", ");
        }
        printf("%s", current->item);
        first = 0;
    }
    printf("]");
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


typedef struct ll_int{
    int item;
    struct ll_int* next;
} ll_int;

void ll_int_free(ll_int** head){
    ll_int* tmp;

    while (*head != NULL)
    {
        tmp = *head;
        *head = (*head)->next;
        free(tmp);
    }
}

ll_int* ll_int_insert(ll_int* head, int x){
    ll_int* temp = malloc(sizeof(struct ll_int));
    temp->item = x;
    temp->next = head;
    return temp;
}

void ll_int_delete0(ll_int** head){
    ll_int *ref = *head;
    *head = ref->next;
    free(ref);
}
/*
 * returns boolean
 */
int ll_int_contains(ll_int* head, int x){
    ll_int* current = NULL;
    for(current = head; current != NULL; current = current->next){
        if(head->item == x){
            return 1;
        }
    }
    return 0;
}

int ll_int_at(ll_int* head, int x){
    int i = 0;
    ll_int* current = NULL;
    for(current = head; current != NULL; current = current->next){
        if(head->item == x){
            return i;
        }
        ++i;
    }
    return i;
}

void ll_int_delete(ll_int** head, int index){

    if(index == 0){
        ll_int_delete0(*head);
    }

    int i = 0;
    ll_int* current = *head;

    while(current != NULL){

        if(index-1 == i){
            ll_int* temp = current->next;
            current->next = temp->next;
            free(temp);
            return;
        }
        current = current->next;
        ++i;
    }
}

int ll_int_hasnext(const ll_int* ll){
    return ll->next != NULL;
}

void ll_int_reverse(ll_int** ll){
    ll_int* prev = NULL;
    ll_int* current = *ll;
    ll_int* next = NULL;

    while(current != NULL){
        next = current->next;
        current->next = prev;
        prev = current;
        current = next;
    }

    *ll = prev;
}

void ll_int_concat(ll_int **head, const ll_int* tocat){
    ll_int_reverse(head);
    ll_int* current = tocat;
    ll_int_reverse(&current);
    while(current != NULL){
        *head = ll_int_insert(*head, current->item);
        current = current->next;
    }

    ll_int_reverse(head);
}


void ll_int_iter(ll_int* toiter, void (*function)(void*)){
    ll_int* current = NULL;
    for(current = toiter; current != NULL; current = current->next){
        (*function)(current);
    }
}

void ll_int_print_single(ll_int* ll){
    printf("%d\n", ll->item);
}


/*
 * puts value at index before the neighbour
 */
void ll_int_pull_value(ll_int** ll, int index){
    if(index == 0){
        return;
    }
    ll_int* current = *ll;
    ll_int* before = NULL;
    for(int i = 0; i<index; i++){
        before = current;
        current = current->next;
        if(current == NULL){
            return;
        }
    }

    int temp = current->item;
    current->item = before->item;
    before->item = temp;

}

int ll_int_len(ll_int* i){
    ll_int* current = NULL;
    int a = 0;
    for(current = i; current != NULL; current = current->next){
        ++a;
    }
    return a;
}





#endif