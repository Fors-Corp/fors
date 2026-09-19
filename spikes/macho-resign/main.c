#include <stdio.h>
#include <stdint.h>

/*
 * A distinctive 8-byte marker immediately followed by a 4-byte little-endian
 * int32 value. resign.py's test harness locates the marker bytes in the
 * compiled binary and patches the 4 bytes right after it -- this avoids any
 * dependency on instruction encoding or compiler codegen details.
 */
__attribute__((used, aligned(8)))
static const struct {
    uint64_t marker;
    int32_t value;
    int32_t pad;
} magic_block = { 0xC0FFEE1234567890ULL, 41, 0 };

__attribute__((used, noinline))
static int get_magic(void) {
    /* volatile pointer forces an actual memory load at runtime, so the
     * value can never be constant-folded into the instruction stream. */
    const volatile int32_t *p = &magic_block.value;
    return *p;
}

int main(void) {
    printf("%d\n", get_magic());
    return 0;
}
