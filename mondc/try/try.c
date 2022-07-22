#include <stdio.h>
#include "../src/util/llist.h"
#include "../src/util/astring.h"

int main(){


    ll_string* inclusion_directives = NULL;
    inclusion_directives = ll_string_insert(inclusion_directives, "testdira");
    inclusion_directives = ll_string_insert(inclusion_directives, "testdirb");
    inclusion_directives = ll_string_insert(inclusion_directives, "testdirc");
    inclusion_directives = ll_string_insert(inclusion_directives, "testdird");

    ll_string* inclusion_dir_queue = NULL;
    inclusion_dir_queue = ll_string_insert(inclusion_dir_queue, "testdirq");
    inclusion_dir_queue = ll_string_insert(inclusion_dir_queue, "testdirb");
    inclusion_dir_queue = ll_string_insert(inclusion_dir_queue, "testdirx");

    ll_string* link = NULL;
    for(link = inclusion_directives; link != NULL; link = link->next){
        printf("searching for %s\n", link->item);

        if(ll_string_contains(inclusion_dir_queue, link->item)){
            printf("found\n");
            printf("%d\n", ll_string_at(inclusion_dir_queue, link->item));
            ll_string_delete(&inclusion_dir_queue, ll_string_at(inclusion_dir_queue, link->item));
        }
    }

    ll_string_iter(inclusion_dir_queue, ll_string_print_single);

    return 0;
}