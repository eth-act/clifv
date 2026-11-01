typedef __UINT8_TYPE__ uint8_t;
typedef __UINT64_TYPE__ uint64_t;
#define UINT64_C(value) value##ULL
#define UINT64_MAX ((uint64_t)-1)

extern void memory_sret_copy0(uint64_t *, const uint64_t *);
extern void memory_sret_copy1(uint64_t *, const uint64_t *);

/* The original source takes its sret pointer in x8 and its source pointer in x0. */
__asm__(".text\n"
        ".globl memory_sret_copy0\n"
        "memory_sret_copy0:\n"
        "mov x8, x0\n"
        "mov x0, x1\n"
        "b _RNxC7fv_demo11HawPMC3YC2b\n"
        ".globl memory_sret_copy1\n"
        "memory_sret_copy1:\n"
        "mov x8, x0\n"
        "mov x0, x1\n"
        "b memory_sret_copy_variant\n");

int main(void) {
  const uint64_t values[] = {
    0, 1, 37, UINT64_MAX, UINT64_C(0x8000000000000000),
    UINT64_C(0x0123456789abcdef), UINT64_C(0xfedcba9876543210),
    UINT64_C(0xff00aa55807f0100)
  };
  const unsigned targets[] = {2, 1, 3, 5};
  uint64_t heap[8] __attribute__((aligned(16)));
  uint8_t before[sizeof(heap)];
  for (unsigned variant = 0; variant < 2; ++variant) {
    for (unsigned alias = 0; alias < 4; ++alias) {
      for (unsigned first = 0; first < 8; ++first) {
        for (unsigned second = 0; second < 8; ++second) {
          for (unsigned i = 0; i < 8; ++i) heap[i] = UINT64_C(0xa5a5a5a5a5a5a5a5) + i;
          uint64_t *source = heap + 2;
          uint64_t *target = heap + targets[alias];
          source[0] = values[first];
          source[1] = values[second];
          for (unsigned i = 0; i < sizeof(heap); ++i) before[i] = ((uint8_t *)heap)[i];
          if (variant == 0) memory_sret_copy0(target, source);
          else memory_sret_copy1(target, source);
          unsigned start = targets[alias] * 8;
          for (unsigned i = 0; i < sizeof(heap); ++i) {
            uint8_t expected = before[i];
            if (i >= start && i < start + 16) expected = before[16 + i - start];
            if (((uint8_t *)heap)[i] != expected) return 1;
          }
        }
      }
    }
  }
  return 0;
}

__attribute__((noreturn)) void _start(void) {
  register long result __asm__("x0") = main();
  register long number __asm__("x8") = 93;
  __asm__ volatile("svc #0" : : "r"(result), "r"(number) : "memory");
  __builtin_unreachable();
}
