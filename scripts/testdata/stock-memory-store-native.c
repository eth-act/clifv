#ifdef FV_STORE_FREESTANDING
typedef __UINT8_TYPE__ uint8_t;
typedef __UINT64_TYPE__ uint64_t;
#define UINT64_C(value) value##ULL
#define UINT64_MAX ((uint64_t)-1)
#else
#include <stdint.h>
#include <stdio.h>
#endif

#ifndef STORE_BYTES
#error STORE_BYTES must specify the emitted store width
#endif
#if STORE_BYTES < 1 || STORE_BYTES > 8
#error STORE_BYTES must be between one and eight
#endif

extern void memory_store0(uint8_t *, uint64_t);
extern void memory_store1(uint64_t, uint8_t *);
extern uint64_t memory_retained(uint64_t);

int main(void) {
  const uint64_t values[] = {
    0, 1, 37, 0xa5, 0x80, 0x8000, 0x80000000,
    UINT64_C(0x8000000000000000), UINT64_MAX,
    UINT64_C(0x0123456789abcdef), UINT64_C(0xfedcba9876543210)
  };
  uint8_t heap[32] __attribute__((aligned(16)));
  for (unsigned order = 0; order < 2; ++order) {
    for (unsigned k = 0; k < sizeof(values) / sizeof(values[0]); ++k) {
      for (unsigned i = 0; i < sizeof(heap); ++i) heap[i] = 0xa5;
      if (order == 0) memory_store0(heap + 8, values[k]);
      else memory_store1(values[k], heap + 8);
      for (unsigned i = 0; i < sizeof(heap); ++i) {
        const uint8_t expected = i >= 8 && i < 8 + STORE_BYTES
          ? (uint8_t)(values[k] >> (8 * (i - 8))) : 0xa5;
        if (heap[i] != expected) {
          #ifndef FV_STORE_FREESTANDING
          fprintf(stderr, "store mismatch order=%u case=%u byte=%u got=%u expected=%u\n",
            order, k, i, (unsigned)heap[i], (unsigned)expected);
          #endif
          return 1;
        }
      }
    }
  }
  if (memory_retained(UINT64_C(0x0123456789abcdef)) != UINT64_C(0x0123456789abcdef)) return 2;
  #ifndef FV_STORE_FREESTANDING
  printf("STOCK_STORE_NATIVE_PASS bytes=%u stores=%zu\n", (unsigned)STORE_BYTES,
    2 * sizeof(values) / sizeof(values[0]));
  #endif
  return 0;
}

#ifdef FV_STORE_FREESTANDING
__attribute__((noreturn)) void _start(void) {
  register long result __asm__("x0") = main();
  register long number __asm__("x8") = 93;
  __asm__ volatile("svc #0" : : "r"(result), "r"(number) : "memory");
  __builtin_unreachable();
}
#endif
