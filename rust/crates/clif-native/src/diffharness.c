/* Freestanding aarch64 Linux harness of `clif-native --diff` (differential testing of two
 * compilations of the same CLIF file, docs/contracts/drivers.md).
 *
 * The same harness object is linked with each engine's object (the Lean backend's, and
 * Cranelift's), so both executables generate the same inputs and report the same record
 * format. clif-native generates `clifdiff_tables.h`, which defines
 *   CLIFDIFF_NFNS, CLIFDIFF_NDATA, CLIFDIFF_SEED, CLIFDIFF_TIMEOUT_US,
 *   static const struct clifdiff_fn clifdiff_fns[];     (every function of the file)
 *   static const u8 *const clifdiff_data[];             (every `; data:` object)
 *
 * Usage: `exe F0 F1 V0 V1 VSTART`: for functions F0..F1-1 (the first one from vector VSTART,
 * after a restart), vectors V0..V1-1 and stack configurations 0 and 1, generate the
 * vector's inputs, call the function's CLIF trampoline on a harness-owned stack and write
 * one little-endian record to stdout:
 *   {u32 fn, vector, config, kind; u64 x[4]; u64 heap_used; u32 nmem, truncated; u64 hash}
 *   followed by nmem entries {u64 address, initial, final}
 * kind 0 = returned (x = the first 32 result bytes, 16 per result),
 *      1 = signal (x = {signo, pc, fault address, 0}), 2 = timeout, 3 = stack overflow.
 * The entries are every observable memory word a call can write: the changed words of the
 * argument arena and of the writable data objects, and every word of the bump heap
 * (initial = 0). `hash` covers the same memory (the fallback when more than MAX_ENTRIES
 * words changed: `truncated`). Values in results and memory are canonicalised: a word equal
 * to a function's address becomes `CODE_TOKEN | index` (code addresses differ between the
 * two executables), a word inside the call stack becomes STACK_TOKEN (frame layouts differ).
 *
 * Inputs, from a PRNG seeded with (seed, fn, vector): the 64 KiB arena at a fixed address
 * is filled with a mix of pointers into itself, small integers, zeros, random words and
 * pointers to data objects / to fixed-address thunks of the file's functions; each
 * parameter gets a value by its kind (pointer parameters, as inferred by clif-native, mostly
 * point into the arena; `sret` points at a reserved arena tail). Both configurations use the
 * same inputs; they differ in the stack base and in the fill pattern of the stack and of
 * fresh heap blocks, so bits that depend on uninitialised memory differ between the two
 * configurations of one engine: clif-native compares only the bits that are stable in both
 * engines.
 */

typedef unsigned long u64;
typedef unsigned int u32;
typedef unsigned char u8;

struct clifdiff_fn {
  void (*tramp)(void *); /* CLIF trampoline: loads 16-byte argument slots, stores results */
  const u8 *code;        /* the function itself (for code-address canonicalisation) */
  u32 nparams;
  u32 nret;
  const u8 *pdesc;       /* per parameter: {size in bytes, kind: 0 int, 1 pointer, 2 sret} */
};

#include "clifdiff_tables.h"

#define SYS_sigaltstack 132
#define SYS_rt_sigaction 134
#define SYS_write 64
#define SYS_exit_group 94
#define SYS_mmap 222
#define SYS_setitimer 103

#define SA_SIGINFO 0x4UL
#define SA_ONSTACK 0x08000000UL
#define SA_RESTORER 0x04000000UL
#define SA_NODEFER 0x40000000UL

#define ARENA ((u8 *)0x7e0000000UL)
#define ARENA_SIZE (64UL << 10)
#define ARENA_PTR_SPAN (48UL << 10) /* pointers into the arena point below this */
#define SRET_OFF (60UL << 10)
#define HEAP ((u8 *)0x7f0000000UL)
#define HEAP_SIZE (4UL << 20)
#define STACK_BASE 0x7d0000000UL    /* [BASE, BASE + GUARD) is left unmapped */
#define STACK_GUARD (1UL << 20)
#define STACK_SIZE (32UL << 20)
#define STACK_FILL (32UL << 10)
#define SNAP ((u8 *)0x7c0000000UL)  /* pristine copy of the writable data objects */
#define ARENA_INIT ((u8 *)0x7b0000000UL) /* the arena as generated */
#define CODE_TOKEN 0xc0de000000000000UL
#define STACK_TOKEN 0x57ac000000000000UL
#define MAX_ENTRIES 8192

static long sys6(long n, long a, long b, long c, long d, long e, long f) {
  register long x8 __asm__("x8") = n;
  register long x0 __asm__("x0") = a;
  register long x1 __asm__("x1") = b;
  register long x2 __asm__("x2") = c;
  register long x3 __asm__("x3") = d;
  register long x4 __asm__("x4") = e;
  register long x5 __asm__("x5") = f;
  __asm__ volatile("svc #0" : "+r"(x0) : "r"(x8), "r"(x1), "r"(x2), "r"(x3), "r"(x4), "r"(x5) : "memory");
  return x0;
}

static void __attribute__((noreturn)) clifdiff_exit(int code) {
  for (;;) sys6(SYS_exit_group, code, 0, 0, 0, 0, 0);
}

static void clifdiff_out(const void *p, u64 n) {
  const u8 *q = p;
  while (n) {
    long r = sys6(SYS_write, 1, (long)q, (long)n, 0, 0, 0);
    if (r == -4) continue;
    if (r <= 0) clifdiff_exit(3);
    q += r;
    n -= (u64)r;
  }
}

/* The writable data objects (a dedicated section at a fixed address, see clif-native). */
extern u8 __start_clifd_rw[] __attribute__((weak));
extern u8 __stop_clifd_rw[] __attribute__((weak));
/* One 16-byte thunk per function (`clifdiff_thunks + 16 * k` jumps to function k), at a fixed
 * address: function pointers placed in the arena are the same in both executables. */
extern const u8 clifdiff_thunks[];
static u64 rw_size(void) { return __start_clifd_rw ? (u64)(__stop_clifd_rw - __start_clifd_rw) : 0; }

/* ---- PRNG (splitmix64) ---- */
static u64 rng;
static u64 mix64(u64 z) {
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9UL;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebUL;
  return z ^ (z >> 31);
}
static u64 next(void) {
  rng += 0x9e3779b97f4a7c15UL;
  return mix64(rng);
}

/* ---- code addresses, sorted, for canonicalisation ---- */
static u64 code_addr[CLIFDIFF_NFNS];
static u32 code_idx[CLIFDIFF_NFNS];
static u64 code_lo, code_hi;

static u64 canon(u64 w) {
  if (w >= STACK_BASE && w < STACK_BASE + STACK_SIZE) return STACK_TOKEN;
  if (w < code_lo || w > code_hi) return w;
  u32 lo = 0, hi = CLIFDIFF_NFNS;
  while (lo < hi) {
    u32 mid = (lo + hi) / 2;
    if (code_addr[mid] < w) lo = mid + 1;
    else hi = mid;
  }
  if (lo < CLIFDIFF_NFNS && code_addr[lo] == w) return CODE_TOKEN | code_idx[lo];
  return w;
}

/* ---- the bump heap behind the Rust allocator entry points ---- */
static u64 heap_used;
static u32 cur_f, cur_v, cur_c;

/* The fill pattern of fresh stack/heap bytes: configuration 1 is the bitwise complement of
 * configuration 0, so every bit copied from uninitialised memory differs between them. */
static u64 fill_word(u64 salt, u64 i) {
  u64 w = mix64((salt << 40) ^ i ^ 0x5bd1e995UL);
  return cur_c ? ~w : w;
}

void *clifdiff_rust_alloc(u64 size, u64 align) {
  if (align == 0) align = 1;
  u64 at = (heap_used + align - 1) & ~(align - 1);
  if (align > 4096 || at + size > HEAP_SIZE || at + size < at) return 0;
  heap_used = at + size;
  u8 *p = HEAP + at;
  for (u64 k = 0; k < size; k++) p[k] = (u8)fill_word(1, at + k);
  return p;
}
void *clifdiff_rust_alloc_zeroed(u64 size, u64 align) {
  u8 *p = clifdiff_rust_alloc(size, align);
  if (p)
    for (u64 k = 0; k < size; k++) p[k] = 0;
  return p;
}
void clifdiff_rust_dealloc(void *p, u64 size, u64 align) { (void)p, (void)size, (void)align; }
void *clifdiff_rust_realloc(u8 *p, u64 old, u64 align, u64 size) {
  u8 *q = clifdiff_rust_alloc(size, align);
  if (q)
    for (u64 k = 0; k < old && k < size; k++) q[k] = p[k];
  return q;
}
void clifdiff_rust_noop(void) {}

/* compiler-builtins' `__rust_u128_mulo(a, b, &mut overflow) -> a * b` (u128
 * `overflowing_mul`), written with 64-bit pieces only. */
static void umul64(u64 a, u64 b, u64 *lo, u64 *hi) {
  u64 a0 = a & 0xffffffffUL, a1 = a >> 32, b0 = b & 0xffffffffUL, b1 = b >> 32;
  u64 p00 = a0 * b0, p01 = a0 * b1, p10 = a1 * b0, p11 = a1 * b1;
  u64 mid = (p00 >> 32) + (p01 & 0xffffffffUL) + (p10 & 0xffffffffUL);
  *lo = (p00 & 0xffffffffUL) | (mid << 32);
  *hi = p11 + (p01 >> 32) + (p10 >> 32) + (mid >> 32);
}
unsigned __int128 __rust_u128_mulo(unsigned __int128 a, unsigned __int128 b, int *overflow) {
  u64 al = (u64)a, ah = (u64)(a >> 64), bl = (u64)b, bh = (u64)(b >> 64);
  u64 l0, h0, l1, h1, l2, h2, l3, h3;
  umul64(al, bl, &l0, &h0);
  umul64(al, bh, &l1, &h1);
  umul64(ah, bl, &l2, &h2);
  umul64(ah, bh, &l3, &h3);
  u64 r1 = h0, carry = 0;
  r1 += l1; carry += r1 < l1;
  r1 += l2; carry += r1 < l2;
  /* the product's bits 128..255 are h1 + h2 + l3 + h3 * 2^64 + carry (all non-negative) */
  *overflow = (h1 | h2 | l3 | h3 | carry) != 0;
  return ((unsigned __int128)r1 << 64) | l0;
}

/* ---- inputs ---- */
static const u64 boundary[] = {0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 0x7f, 0x80, 0xff, 0x100, 0x7fff, 0x8000,
                               0xffff, 0x7fffffffUL, 0x80000000UL, 0xffffffffUL, 0x100000000UL,
                               0x7fffffffffffffffUL, 0x8000000000000000UL, ~0UL, ~0UL - 1, 0x8000000000000001UL};

static u64 arena_ptr(void) { return (u64)ARENA + 8 * (next() % (ARENA_PTR_SPAN / 8)); }

static u64 gen_int(u32 size) {
  u64 r = next() % 100;
  if (r < 20) return next() % 17;
  if (r < 30) return (u64)(-(long)(next() % 8 + 1));
  if (r < 50) return boundary[next() % (sizeof boundary / sizeof boundary[0])];
  if (r < 85 || size < 8) return next();
  return arena_ptr();
}

static u64 gen_ptr(void) {
  u64 r = next() % 100;
  if (r < 88) return arena_ptr();
  if (r < 92) return 0;
  if (r < 96) return next() % 17;
  return next();
}

static void fill_arena(void) {
  u64 *w = (u64 *)ARENA;
  for (u64 k = 0; k < ARENA_SIZE / 8; k++) {
    u64 r = next() & 15;
    if (r < 4) w[k] = arena_ptr();
    else if (r < 8) w[k] = next() % 17;
    else if (r < 10) w[k] = 0;
    else if (r < 14) w[k] = next();
    else if (r == 14 && CLIFDIFF_NDATA > 0) w[k] = (u64)clifdiff_data[next() % (CLIFDIFF_NDATA ? CLIFDIFF_NDATA : 1)];
    else w[k] = (u64)clifdiff_thunks + 16 * (next() % CLIFDIFF_NFNS);
  }
  for (u64 k = 0; k < ARENA_SIZE / 8; k++) ((u64 *)ARENA_INIT)[k] = w[k];
}

static u8 buf[256] __attribute__((aligned(16)));

static void gen_args(const struct clifdiff_fn *fd) {
  for (u32 k = 0; k < sizeof buf; k++) buf[k] = 0;
  for (u32 i = 0; i < fd->nparams; i++) {
    u32 size = fd->pdesc[2 * i], kind = fd->pdesc[2 * i + 1];
    u64 lo, hi = 0;
    if (kind == 2) lo = (u64)ARENA + SRET_OFF;
    else if (kind == 1) lo = gen_ptr();
    else lo = gen_int(size);
    if (size == 16) {
      u64 r = next() & 3;
      hi = r == 0 ? (u64)((long)lo >> 63) : r == 1 ? 0 : r == 2 ? ~0UL : next();
    }
    u8 *s = buf + 16 * i;
    for (u32 b = 0; b < 8 && b < size; b++) s[b] = (u8)(lo >> (8 * b));
    for (u32 b = 8; b < size; b++) s[b] = (u8)(hi >> (8 * (b - 8)));
  }
}

/* ---- the observable memory ---- */
static u64 hash;
static u32 nmem, truncated;
static u64 entries[3 * MAX_ENTRIES];

static void note(const u8 *at, u64 init, u64 fin) {
  hash = (hash ^ (u64)at) * 0x100000001b3UL;
  hash = (hash ^ fin) * 0x100000001b3UL;
  if (nmem == MAX_ENTRIES) {
    truncated = 1;
    return;
  }
  entries[3 * nmem] = (u64)at;
  entries[3 * nmem + 1] = init;
  entries[3 * nmem + 2] = fin;
  nmem++;
}
static void diff_words(const u8 *now, const u8 *before, u64 n) {
  for (u64 k = 0; k < n / 8; k++) {
    u64 a = ((const u64 *)before)[k], b = ((const u64 *)now)[k];
    if (a != b) note(now + 8 * k, canon(a), canon(b));
  }
  for (u64 k = n & ~7UL; k < n; k++)
    if (before[k] != now[k]) note(now + k, before[k], now[k]);
}
static void collect_memory(void) {
  hash = 0xcbf29ce484222325UL;
  nmem = truncated = 0;
  diff_words(ARENA, ARENA_INIT, ARENA_SIZE);
  diff_words(__start_clifd_rw, SNAP, rw_size());
  const u64 *hw = (const u64 *)HEAP;
  for (u64 k = 0; k < (heap_used + 7) / 8; k++) note((const u8 *)(hw + k), 0, canon(hw[k]));
}

/* ---- timer ---- */
static void set_timer(u64 us) {
  long it[4] = {0, 0, (long)(us / 1000000), (long)(us % 1000000)};
  sys6(SYS_setitimer, 1 /* ITIMER_VIRTUAL */, (long)it, 0, 0, 0, 0);
}

/* ---- records ---- */
struct rec { u32 f, v, c, kind; u64 x[4]; u64 heap; u32 nmem, truncated; u64 hash; };
_Static_assert(sizeof(struct rec) == 72, "record size");

static void emit(u32 kind, const u64 *x) {
  collect_memory();
  struct rec r = {cur_f, cur_v, cur_c, kind, {x[0], x[1], x[2], x[3]}, heap_used, nmem, truncated, hash};
  clifdiff_out(&r, sizeof r);
  clifdiff_out(entries, 24 * (u64)nmem);
}

/* x0 = function, x1 = argument, x2 = new stack pointer; returns on the harness stack. */
extern void clifdiff_call_on_stack(void (*fn)(void *), void *arg, u64 sp);
__asm__(".text\n.globl clifdiff_call_on_stack\nclifdiff_call_on_stack:\n"
        "  stp x29, x30, [sp, #-16]!\n  mov x29, sp\n  mov x3, sp\n  mov sp, x2\n"
        "  str x3, [sp, #-16]!\n  mov x9, x0\n  mov x0, x1\n  blr x9\n"
        "  ldr x3, [sp], #16\n  mov sp, x3\n  ldp x29, x30, [sp], #16\n  ret\n");

static u32 f1, v0, v1;
static u64 resume_sp;

static u64 stack_top(u32 c) { return STACK_BASE + STACK_SIZE - (c ? 4096 + 64 : 0); }

static void run_one(void) {
  const struct clifdiff_fn *fd = &clifdiff_fns[cur_f];
  rng = mix64(CLIFDIFF_SEED ^ mix64(((u64)cur_f << 32) | cur_v));
  fill_arena();
  gen_args(fd);
  heap_used = 0;
  for (u64 k = 0; k < rw_size(); k++) __start_clifd_rw[k] = SNAP[k];
  u64 top = stack_top(cur_c);
  u64 *s = (u64 *)(top - STACK_FILL);
  for (u64 k = 0; k < STACK_FILL / 8; k++) s[k] = fill_word(2, k);
  set_timer(CLIFDIFF_TIMEOUT_US);
  clifdiff_call_on_stack(fd->tramp, buf, top);
  set_timer(0);
  u64 x[4];
  for (u32 k = 0; k < 4; k++) {
    u64 w = 0;
    for (u32 b = 0; b < 8; b++) w |= (u64)buf[8 * k + b] << (8 * b);
    x[k] = canon(w);
  }
  emit(0, x);
}

static int advance(void) {
  if (++cur_c < 2) return 1;
  cur_c = 0;
  if (++cur_v < v1) return 1;
  cur_v = v0;
  return ++cur_f < f1;
}

static void __attribute__((noreturn)) run_loop(int first) {
  if (!first && !advance()) clifdiff_exit(0);
  do run_one();
  while (advance());
  clifdiff_exit(0);
}

static void __attribute__((noreturn, used)) clifdiff_resume(void) { run_loop(0); }

static void on_signal(int sig, void *info, void *ucv) {
  set_timer(0);
  u8 *uc = ucv;
  u64 pc = *(u64 *)(uc + 176 + 264);
  u64 addr = *(u64 *)((u8 *)info + 16);
  u32 kind = 1;
  if (sig == 26) kind = 2;
  else if (sig == 11 && addr >= STACK_BASE && addr < STACK_BASE + STACK_GUARD) kind = 3;
  u64 x[4] = {(u64)sig, pc, addr, 0};
  if (kind != 1) x[1] = x[2] = 0;
  emit(kind, x);
  *(u64 *)(uc + 176 + 264) = (u64)&clifdiff_resume; /* pc */
  *(u64 *)(uc + 176 + 256) = resume_sp;             /* sp */
  *(u64 *)(uc + 176 + 8 + 29 * 8) = 0;
  *(u64 *)(uc + 176 + 8 + 30 * 8) = 0;
}

__attribute__((naked)) static void restorer(void) { __asm__ volatile("mov x8, #139\n\tsvc #0"); }

static u8 altstack[1 << 16] __attribute__((aligned(16)));

static u32 parse(const char *s) {
  u32 n = 0;
  for (; *s >= '0' && *s <= '9'; s++) n = n * 10 + (u32)(*s - '0');
  return n;
}

static void map_fixed(u64 at, u64 size) {
  long r = sys6(SYS_mmap, (long)at, (long)size, 3, 0x22 | 0x100000 /* MAP_FIXED_NOREPLACE */, -1, 0);
  if ((u64)r != at) clifdiff_exit(6);
}

void __attribute__((noreturn, used)) __clifdiff_main(u64 *sp) {
  u64 argc = sp[0];
  const char *const *argv = (const char *const *)(sp + 1);
  if (argc != 6) clifdiff_exit(7);
  cur_f = parse(argv[1]);
  f1 = parse(argv[2]);
  v0 = parse(argv[3]);
  v1 = parse(argv[4]);
  cur_v = parse(argv[5]);
  cur_c = 0;
  if (cur_f >= f1 || v0 >= v1 || cur_v >= v1 || f1 > CLIFDIFF_NFNS) clifdiff_exit(0);
  resume_sp = (u64)sp & ~15UL;

  map_fixed((u64)ARENA, ARENA_SIZE);
  map_fixed((u64)HEAP, HEAP_SIZE);
  map_fixed(STACK_BASE + STACK_GUARD, STACK_SIZE - STACK_GUARD);
  map_fixed((u64)ARENA_INIT, ARENA_SIZE);
  if (rw_size()) {
    map_fixed((u64)SNAP, (rw_size() + 4095) & ~4095UL);
    for (u64 k = 0; k < rw_size(); k++) SNAP[k] = __start_clifd_rw[k];
  }
  /* sorted code addresses */
  for (u32 i = 0; i < CLIFDIFF_NFNS; i++) {
    u64 a = (u64)clifdiff_fns[i].code;
    u32 j = i;
    while (j > 0 && code_addr[j - 1] > a) {
      code_addr[j] = code_addr[j - 1];
      code_idx[j] = code_idx[j - 1];
      j--;
    }
    code_addr[j] = a;
    code_idx[j] = i;
  }
  code_lo = code_addr[0];
  code_hi = code_addr[CLIFDIFF_NFNS - 1];

  struct { void *sp; int flags; u64 size; } ss = {altstack, 0, sizeof altstack};
  if (sys6(SYS_sigaltstack, (long)&ss, 0, 0, 0, 0, 0) != 0) clifdiff_exit(4);
  static const int sigs[] = {4, 5, 7, 8, 11, 26 /* SIGVTALRM */};
  for (u32 k = 0; k < sizeof sigs / sizeof sigs[0]; k++) {
    struct { void (*h)(int, void *, void *); u64 flags; void (*r)(void); u64 mask; } sa = {
        on_signal, SA_SIGINFO | SA_ONSTACK | SA_RESTORER | SA_NODEFER, restorer, 0};
    if (sys6(SYS_rt_sigaction, sigs[k], (long)&sa, 0, 8, 0, 0) != 0) clifdiff_exit(5);
  }
  run_loop(1);
}

__attribute__((naked, noreturn)) void _start(void) { __asm__ volatile("mov x0, sp\n\tbl __clifdiff_main"); }
