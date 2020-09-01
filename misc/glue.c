#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

extern void __main();

void print_i8(int8_t v) {
    printf("%" PRId8 "\n", v);
}

void print_u8(uint8_t v) {
    printf("%" PRIu8 "\n", v);
}

void print_i16(int16_t v) {
    printf("%" PRId16 "\n", v);
}

void print_u16(uint16_t v) {
    printf("%" PRIu16 "\n", v);
}

void print_i32(int32_t v) {
    printf("%" PRId32 "\n", v);
}

void print_u32(uint32_t v) {
    printf("%" PRIu32 "\n", v);
}

void print_i64(int64_t v) {
    printf("%" PRId64 "\n", v);
}

void print_u64(uint64_t v) {
    printf("%" PRIu64 "\n", v);
}

void print_u128(__uint128_t v) {
    uint64_t hi = (uint64_t)(v >> 64);
    uint64_t lo = (uint64_t) v;
    if (hi > 0) {
        printf("0x%" PRIx64 "%016" PRIx64 "\n", hi, lo);
    } else {
        print_u64(lo);
    }
}

void print_i128(__int128_t v) {
    uint64_t hi = (uint64_t)(((__uint128_t) v) >> 64);
    uint64_t lo = (uint64_t) v;
    if (hi > 0) {
        printf("0x%" PRIx64 "%016" PRIx64 " // i128\n", hi, lo);
    } else {
        print_u64(lo);
    }
}

void print_isize(intptr_t v) {
    printf("%" PRIdPTR "\n", v);
}

void print_usize(uintptr_t v) {
    printf("%" PRIuPTR "\n", v);
}

void print_f64(double v) {
    printf("%.2f\n", v);
}

void print_f32(float v) {
    print_f64(v);
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

void print_sep() {
    printf("***************************************\n");
}

int main() {
    setvbuf(stdout, NULL, _IONBF, 0);
    __main();
    return 0;
}
