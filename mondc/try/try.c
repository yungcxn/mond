#include <stdio.h>
#include "../src/llist.h"

int main(){

    /*
    ll_string* linkedlist = NULL;
    linkedlist = ll_string_insert(linkedlist, "yoo");
    linkedlist = ll_string_insert(linkedlist, "test");
    linkedlist = ll_string_insert(linkedlist, "chair");
    linkedlist = ll_string_insert(linkedlist, "table");

    ll_string_reverse(&linkedlist);
    ll_string_pull_value(&linkedlist, 2);

    ll_string_delete0(&linkedlist);
    //ll_string_delete(&linkedlist, 1);
    ll_string_free(&linkedlist);
    ll_string_iter(linkedlist, ll_string_print_single);
*/

    astring_ptr s = create_astring("yoodd");

    safeappend_astring(&s ,"dadsssdsddssdsdsd");
    printf("%s", s->string);

    return 0;
}