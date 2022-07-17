#include <stdio.h>
#include "../llist.h"

int main(){

    ll_string* linkedlist = NULL;
    linkedlist = ll_string_insert(linkedlist, "yoo");
    linkedlist = ll_string_insert(linkedlist, "test");
    linkedlist = ll_string_insert(linkedlist, "chair");
    linkedlist = ll_string_insert(linkedlist, "table");

    ll_string_reverse(&linkedlist);
    ll_string_pull_value(&linkedlist, 2);

    ll_string_iter(linkedlist, ll_string_print_single);

    return 0;
}