/* Freestanding aarch64 Linux test harness for clif-native.
 *
 * clif-native generates `clifnative_tables.h` (included below), which defines
 *   CLIFNATIVE_BUF_SIZE, CLIFNATIVE_NRUNS, CLIFNATIVE_NFNS,
 *   static const struct clifnative_run clifnative_runs[];  (one per runnable `; run` line)
 *   static const struct clifnative_fn  clifnative_fns[];   (every compiled function)
 * and links this file with the Cranelift object. Usage: `exe [START]`.
 *
 * For run lines START..NRUNS-1: copy the argument bytes into a 16-byte aligned buffer, call
 * the line's CLIF trampoline (which loads the arguments from the buffer, calls the function
 * under test per AAPCS64 and stores its results back), then write one little-endian record
 * to stdout:
 *   {u32 index; u32 kind = 0; u8 results[ret_len]}                  returned
 *   {u32 index; u32 kind = 1; u32 signo; u32 fn; u64 offset}        signal
 * For a signal, `fn` indexes clifnative_fns and `offset` is the faulting PC relative to that
 * function's start (fn = 0xffffffff: PC outside every function, `offset` = PC). The signal
 * handler then abandons the faulting computation (new PC and SP via the signal frame) and
 * continues with the next line. Exit status 0 after the last line.
 */

typedef unsigned long u64;
typedef unsigned int u32;
typedef unsigned char u8;

struct clifnative_run {
  void (*tramp)(void *); /* CLIF trampoline: (i64 buffer) */
  const u8 *args;        /* argument bytes, 16 bytes per argument (little-endian) */
  u32 args_len;
  u32 ret_len;           /* result bytes written back, 16 per result */
};
struct clifnative_fn {
  const void *start;
  u64 size;
};

#include "clifnative_tables.h"

#define SYS_sigaltstack 132
#define SYS_rt_sigaction 134
#define SYS_rt_sigreturn 139
#define SYS_write 64
#define SYS_exit_group 94

#define SA_SIGINFO 0x4UL
#define SA_ONSTACK 0x08000000UL
#define SA_RESTORER 0x04000000UL

static long clifnative_syscall(long n, long a, long b, long c, long d) {
  register long x8 __asm__("x8") = n;
  register long x0 __asm__("x0") = a;
  register long x1 __asm__("x1") = b;
  register long x2 __asm__("x2") = c;
  register long x3 __asm__("x3") = d;
  __asm__ volatile("svc #0" : "+r"(x0) : "r"(x8), "r"(x1), "r"(x2), "r"(x3) : "memory");
  return x0;
}

static void __attribute__((noreturn)) clifnative_exit(int code) {
  for (;;) clifnative_syscall(SYS_exit_group, code, 0, 0, 0);
}

static void clifnative_out(const void *p, u64 n) {
  const u8 *q = p;
  while (n) {
    long r = clifnative_syscall(SYS_write, 1, (long)q, (long)n, 0);
    if (r == -4) continue; /* EINTR */
    if (r <= 0) clifnative_exit(3);
    q += r;
    n -= (u64)r;
  }
}

/* Kernel signal ABI (arch/arm64/include/uapi/asm/{sigcontext,ucontext}.h). */
struct clifnative_sigaction {
  void (*handler)(int, void *, void *);
  u64 flags;
  void (*restorer)(void);
  u64 mask;
};
struct clifnative_stack { void *sp; int flags; u64 size; };
struct clifnative_sigcontext {
  u64 fault_address;
  u64 regs[31];
  u64 sp;
  u64 pc;
  u64 pstate;
  u8 reserved[4096] __attribute__((aligned(16)));
};
struct clifnative_ucontext {
  u64 flags;
  void *link;
  struct clifnative_stack stack;
  u64 sigmask;
  u8 unused[120];
  struct clifnative_sigcontext mcontext __attribute__((aligned(16)));
};
_Static_assert(__builtin_offsetof(struct clifnative_ucontext, mcontext) == 176, "ucontext layout");
_Static_assert(__builtin_offsetof(struct clifnative_sigcontext, pc) == 264, "sigcontext layout");

static u8 clifnative_buf[CLIFNATIVE_BUF_SIZE] __attribute__((aligned(16)));
static u8 clifnative_obuf[8 + CLIFNATIVE_BUF_SIZE] __attribute__((aligned(16)));
static u8 clifnative_altstack[1 << 16] __attribute__((aligned(16)));
static volatile u32 clifnative_current;
static u64 clifnative_resume_sp;

static void __attribute__((noreturn)) clifnative_run_from(u32 i) {
  for (; i < CLIFNATIVE_NRUNS; i++) {
    const struct clifnative_run *r = &clifnative_runs[i];
    clifnative_current = i;
    for (u32 k = 0; k < CLIFNATIVE_BUF_SIZE; k++) clifnative_buf[k] = 0;
    for (u32 k = 0; k < r->args_len; k++) clifnative_buf[k] = r->args[k];
    r->tramp(clifnative_buf);
    u32 hdr[2] = {i, 0};
    for (u32 k = 0; k < 8; k++) clifnative_obuf[k] = ((const u8 *)hdr)[k];
    for (u32 k = 0; k < r->ret_len; k++) clifnative_obuf[8 + k] = clifnative_buf[k];
    clifnative_out(clifnative_obuf, 8 + r->ret_len);
  }
  clifnative_exit(0);
}

/* Entered from the signal frame with a fresh stack (SP = the initial process SP). */
static void __attribute__((noreturn, used)) clifnative_resume(void) {
  clifnative_run_from(clifnative_current + 1);
}

static void clifnative_on_signal(int sig, void *info, void *ucv) {
  (void)info;
  struct clifnative_ucontext *uc = ucv;
  u64 pc = uc->mcontext.pc;
  struct { u32 index, kind, signo, fn; u64 offset; } rec = {clifnative_current, 1, (u32)sig, 0xffffffffu, pc};
  for (u32 k = 0; k < CLIFNATIVE_NFNS; k++) {
    u64 start = (u64)clifnative_fns[k].start;
    if (pc >= start && pc - start < clifnative_fns[k].size) {
      rec.fn = k;
      rec.offset = pc - start;
      break;
    }
  }
  clifnative_out(&rec, sizeof rec);
  uc->mcontext.pc = (u64)&clifnative_resume;
  uc->mcontext.sp = clifnative_resume_sp;
  uc->mcontext.regs[29] = 0;
  uc->mcontext.regs[30] = 0;
}

__attribute__((naked)) static void clifnative_restorer(void) {
  __asm__ volatile("mov x8, #139\n\tsvc #0");
}

void __attribute__((noreturn, used)) __clifnative_main(u64 *sp) {
  u64 argc = sp[0];
  const char *const *argv = (const char *const *)(sp + 1);
  u32 start = 0;
  if (argc > 1)
    for (const char *s = argv[1]; *s >= '0' && *s <= '9'; s++) start = start * 10 + (u32)(*s - '0');
  clifnative_resume_sp = (u64)sp & ~15UL;

  struct clifnative_stack ss = {clifnative_altstack, 0, sizeof clifnative_altstack};
  if (clifnative_syscall(SYS_sigaltstack, (long)&ss, 0, 0, 0) != 0) clifnative_exit(4);
  static const int sigs[] = {4 /* SIGILL */, 5 /* SIGTRAP */, 7 /* SIGBUS */, 8 /* SIGFPE */, 11 /* SIGSEGV */};
  for (u32 k = 0; k < sizeof sigs / sizeof sigs[0]; k++) {
    struct clifnative_sigaction sa = {clifnative_on_signal, SA_SIGINFO | SA_ONSTACK | SA_RESTORER,
                                      clifnative_restorer, 0};
    if (clifnative_syscall(SYS_rt_sigaction, sigs[k], (long)&sa, 0, 8) != 0) clifnative_exit(5);
  }
  clifnative_run_from(start);
}

__attribute__((naked, noreturn)) void _start(void) {
  __asm__ volatile("mov x0, sp\n\tbl __clifnative_main");
}
