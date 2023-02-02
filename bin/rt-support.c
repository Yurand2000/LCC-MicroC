#include <stdio.h>
#include <stdlib.h>

void print(int value) {
    printf("%d\n", value);
}

int getint() {
    char buffer[32];
    if( fgets(buffer, 32, stdin) == NULL )
        return 0;
    return atoi(buffer);
}

void print_string(char *string) {
    printf("%s\n", string);
}

void *mem_alloc(int size) {
    return malloc((size_t size));
}

void mem_free(void *ptr) {
    free(ptr);
}