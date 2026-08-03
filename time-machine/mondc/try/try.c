#include <stdio.h>
#include "../src/util/llist.h"
#include "../src/util/astring.h"

void f(void) {
    int *x = malloc(10 * sizeof(int));
    x[10] = 0;
}

int main(void) {
    f();
    return 0;
}