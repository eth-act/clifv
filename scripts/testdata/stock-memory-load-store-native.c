typedef __UINT8_TYPE__ uint8_t;
typedef __UINT64_TYPE__ uint64_t;
#define UINT64_C(value) value##ULL
#define UINT64_MAX ((uint64_t)-1)

#if LOAD_BYTES < 1 || LOAD_BYTES > 8 || STORE_BYTES < 1 || STORE_BYTES > 8
#error Invalid load or store width
#endif

extern uint64_t memory_store0(uint8_t *, uint64_t, uint8_t *);
extern uint64_t memory_store1(uint8_t *, uint64_t, uint8_t *);
extern uint64_t memory_retained(uint64_t);

int main(void) {
  const uint64_t values[] = {
    0, 1, 37, 0xa5, 0x80, 0x8000, 0x80000000,
    UINT64_C(0x8000000000000000), UINT64_MAX,
    UINT64_C(0x0123456789abcdef), UINT64_C(0xfedcba9876543210)
  };
  uint8_t heap[48] __attribute__((aligned(16)));
  for (unsigned order = 0; order < 2; ++order) {
    for (unsigned alias = 0; alias < 2; ++alias) {
      for (unsigned k = 0; k < sizeof(values) / sizeof(values[0]); ++k) {
        for (unsigned i = 0; i < sizeof(heap); ++i) heap[i] = (uint8_t)(0xa5 + i);
        uint64_t expected_load = 0;
        for (unsigned i = 0; i < LOAD_BYTES; ++i)
          expected_load |= (uint64_t)heap[8 + i] << (8 * i);
        unsigned target = order == 0 || alias ? 8 : 24;
        uint8_t *other = heap + (alias ? 8 : 24);
        uint64_t loaded = order == 0
          ? memory_store0(heap + 8, values[k], other)
          : memory_store1(heap + 8, values[k], other);
        /* The ABI permits arbitrary upper bits for narrow return values. */
        uint64_t mask = UINT64_MAX >> (8 * (8 - LOAD_BYTES));
        if ((loaded & mask) != expected_load) return 1;
        for (unsigned i = 0; i < sizeof(heap); ++i) {
          uint8_t expected = i >= target && i < target + STORE_BYTES
            ? (uint8_t)(values[k] >> (8 * (i - target))) : (uint8_t)(0xa5 + i);
          if (heap[i] != expected) return 2;
        }
      }
    }
  }
  if (memory_retained(UINT64_C(0x0123456789abcdef)) != UINT64_C(0x0123456789abcdef)) return 3;
  return 0;
}

__attribute__((noreturn)) void _start(void) {
  register long result __asm__("x0") = main();
  register long number __asm__("x8") = 93;
  __asm__ volatile("svc #0" : : "r"(result), "r"(number) : "memory");
  __builtin_unreachable();
}
