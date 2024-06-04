#include <stdio.h>
#include <stdlib.h>

int main(int argc, char** argv){

    char* ptr0 = malloc(30+argc);
    char* ptr1 = malloc(30+argc);
    char* ptr2 = malloc(30+argc);
    printf("ptr0 %p ptr1 %p ptr2 %p\n", ptr0, ptr1, ptr2);

    char buf16[64];
    char buf15[64];
    char buf14[128];
    printf("buf16 %p buf15 %p buf14 %p\n", buf16, buf15, buf14);

    free(ptr0);
    free(ptr1);
    free(ptr2);
    return 1;
}
