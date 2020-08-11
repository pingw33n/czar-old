#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

extern void __main();

void print_i32(int32_t v) {
    printf("%" PRId32 "\n", v);
}

int main() {
    __main();
    return 0;
}
