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