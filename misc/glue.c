#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

extern void __main();

void print_i32(int32_t v) {
    printf("%" PRId32 "\n", v);
}

void print_u32(uint32_t v) {
    printf("%" PRIu32 "\n", v);
}

void print_isize(intptr_t v) {
    printf("%" PRIdPTR "\n", v);
}

void print_usize(uintptr_t v) {
    printf("%" PRIuPTR "\n", v);
}

void print_bool(int8_t v) {
    char *s;
    switch (v) {
        case 0:
            s = "false";
            break;
        case 1:
            s = "true";
            break;
        default:
            s = "?";
    }
    printf("%s\n", s);
}

void println() {
    printf("\n");
}

int main() {
    setvbuf(stdout, NULL, _IONBF, 0);
    __main();
    return 0;
}
