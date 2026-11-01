typedef __UINT8_TYPE__ uint8_t;
typedef __UINT64_TYPE__ uint64_t;
typedef __UINTPTR_TYPE__ uintptr_t;
#define UINT64_C(value) value##ULL
#define UINT64_MAX ((uint64_t)-1)

extern void memory_copy0(uint64_t *) __asm__("_RNxC7fv_demo12HezxnGHZarII");
extern void memory_copy1(uint64_t *);
extern uint64_t memory_retained(uint64_t);

int main(void) {
  const uint64_t values[] = {
    0, 1, 37, UINT64_MAX, UINT64_C(0x8000000000000000),
    UINT64_C(0x0123456789abcdef), UINT64_C(0xfedcba9876543210),
    UINT64_C(0xff00aa55807f0100)
  };
  uint64_t heap[6] __attribute__((aligned(16)));
  uint8_t before[sizeof(heap)];
  for (unsigned variant = 0; variant < 2; ++variant) {
    for (unsigned alias = 0; alias < 4; ++alias) {
      for (unsigned k = 0; k < sizeof(values) / sizeof(values[0]); ++k) {
        for (unsigned i = 0; i < 6; ++i) heap[i] = UINT64_C(0xa5a5a5a5a5a5a5a5) + i;
        uint64_t *base = heap + 1;
        uint64_t *target = heap + alias;
        base[0] = (uintptr_t)target;
        base[1] = values[k];
        for (unsigned i = 0; i < sizeof(heap); ++i) before[i] = ((uint8_t *)heap)[i];
        if (variant == 0) memory_copy0(base);
        else memory_copy1(base);
        unsigned start = alias * 8;
        for (unsigned i = 0; i < sizeof(heap); ++i) {
          uint8_t expected = i >= start && i < start + 8
            ? (uint8_t)(values[k] >> (8 * (i - start))) : before[i];
          if (((uint8_t *)heap)[i] != expected) return 1;
        }
      }
    }
  }
  if (memory_retained(UINT64_C(0x0123456789abcdef)) != UINT64_C(0x0123456789abcdef)) return 2;
  return 0;
}

__attribute__((noreturn)) void _start(void) {
  register long result __asm__("x0") = main();
  register long number __asm__("x8") = 93;
  __asm__ volatile("svc #0" : : "r"(result), "r"(number) : "memory");
  __builtin_unreachable();
}
