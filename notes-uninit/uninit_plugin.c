/* QEMU TCG plugin (linux-user, aarch64): dynamic count of the accesses by Lean-compiled code
 * on which Clif.run is `stuck` for memory reasons (UninitSem, issue #537).
 *
 * Categories (one counter + per-site table each):
 *   stack_uninit   load by Lean code of stack bytes not written since the owning Lean
 *                  activation began (Clif: slot bytes start `none`, load `stuck`)
 *   stack_uninit_cp  the same, where the byte was copied uninitialised by a memcpy/memmove
 *                  called from Lean code (Clif's memcpy preserves `none`)
 *   heap_fresh     load/store by Lean code into a heap block allocated (malloc & co) during the
 *                  current outside call, i.e. after the outermost live Lean activation began
 *                  (with slots, BaseOk forbids extern allocations: out of bounds in Clif)
 *   heap_uninit    load by Lean code of bytes of an older heap block not written since its
 *                  allocation (Clif: depends on the entry memory)
 *   memcmp_uninit  memcmp/bcmp called from Lean code reading (up to the first difference) a
 *                  byte that is uninitialised in the above sense
 *
 * Model: Lean function entry (pc == start, funcs=FILE "start end name") pushes an activation
 * (S0 = sp, epoch = ++g). Every store stamps its bytes (tracked pages: [S0-1MiB, S0+64KiB] of
 * each activation and every heap block) with the current epoch. Owner of a stack address a
 * (sp <= a): innermost live activation with S0 > a; initialised iff stamp >= owner epoch.
 * Heap blocks come from hooks (syms=FILE "name addr") on malloc/calloc/realloc/aligned_alloc/
 * memalign/posix_memalign/free; returns are detected at the TB starting at the saved lr.
 *
 * Run: qemu-aarch64 -plugin ./uninit_plugin.so,funcs=F,syms=S,out=O EXE ARGS
 */
#include <glib.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <qemu-plugin.h>

QEMU_PLUGIN_EXPORT int qemu_plugin_version = QEMU_PLUGIN_VERSION;

enum { C_STACK, C_STACK_CP, C_HEAP_FRESH, C_HEAP_UNINIT, C_MEMCMP, NCAT };
static const char *catname[NCAT] = { "stack_uninit", "stack_uninit_cp", "heap_fresh",
                                     "heap_uninit", "memcmp_uninit" };
enum { H_MALLOC, H_CALLOC, H_REALLOC, H_ALIGNED, H_MEMALIGN, H_POSIX, H_FREE, H_MEMCPY,
       H_MEMMOVE, H_MEMCMP, H_BCMP, NHOOK };
static const char *hookname[NHOOK] = { "malloc", "calloc", "realloc", "aligned_alloc",
    "memalign", "posix_memalign", "free", "memcpy", "memmove", "memcmp", "bcmp" };
static uint64_t hookaddr[NHOOK];

typedef struct { uint64_t start, end; char *name; uint64_t calls; } Fn;
static Fn *fns; static size_t nfns;

typedef struct { uint64_t s0; uint32_t epoch; uint32_t fn; } Act;
typedef struct {
    int kind; uint64_t lr, sp, a0, a1, a2; int from_lean;
    uint8_t *status; size_t nstatus; /* memcpy src / realloc old block init status */
    uint64_t oldsize;
} Pend;
typedef struct {
    Act *a; size_t n, cap;
    Pend *p; size_t pn, pcap;
    uint32_t outer_epoch;
    struct qemu_plugin_register *reg[32];
    GByteArray *buf;
} Vcpu;
static Vcpu vcpus[256];

typedef struct { uint64_t start, size; uint32_t epoch; } Blk;
static GTree *heap;           /* start -> Blk* */
typedef struct { uint64_t pc; uint64_t count; int fn, cat; } Hit;
static GHashTable *hits;      /* (pc<<3|cat) -> Hit* */
static GHashTable *shadow;    /* page -> uint32_t[4096] */
static uint32_t gepoch = 2;   /* stamp 0: never written, 1: copied uninitialised */
static uint64_t nstat[6];
static uint64_t nloads, ncat[NCAT], nalloc, nmemcpy_lean;
static GMutex lock;
static char *outpath;

#define PAGE 4096ULL
#define BELOW (1ULL << 20)
#define ABOVE (64ULL << 10)

static gint cmp_u64(gconstpointer a, gconstpointer b, gpointer u) {
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b; return x < y ? -1 : x > y;
}

static long find_fn(uint64_t pc) {
    size_t lo = 0, hi = nfns;
    while (lo < hi) { size_t m = (lo + hi) / 2; if (fns[m].start <= pc) lo = m + 1; else hi = m; }
    if (lo == 0) return -1;
    return pc < fns[lo - 1].end ? (long)(lo - 1) : -1;
}

static uint64_t reg(unsigned vi, int r) { /* r: 0..30 = x0..x30, 31 = sp */
    Vcpu *v = &vcpus[vi];
    if (!v->buf) {
        GArray *regs = qemu_plugin_get_registers();
        for (guint i = 0; i < regs->len; i++) {
            qemu_plugin_reg_descriptor *d = &g_array_index(regs, qemu_plugin_reg_descriptor, i);
            if (strcmp(d->name, "sp") == 0) v->reg[31] = d->handle;
            else if (d->name[0] == 'x') {
                char *e; long k = strtol(d->name + 1, &e, 10);
                if (*e == 0 && k >= 0 && k <= 30) v->reg[k] = d->handle;
            }
        }
        g_array_free(regs, TRUE);
        v->buf = g_byte_array_new();
        if (!v->reg[31] || !v->reg[30]) { fprintf(stderr, "uninit_plugin: registers\n"); exit(3); }
    }
    g_byte_array_set_size(v->buf, 0);
    qemu_plugin_read_register(v->reg[r], v->buf);
    uint64_t x = 0; memcpy(&x, v->buf->data, 8);
    return x;
}

static uint32_t *page_of(uint64_t a, int create) {
    uint32_t *pg = g_hash_table_lookup(shadow, (gpointer)(uintptr_t)(a / PAGE));
    if (!pg && create) {
        pg = g_new0(uint32_t, PAGE);
        g_hash_table_insert(shadow, (gpointer)(uintptr_t)(a / PAGE), pg);
    }
    return pg;
}
static uint32_t stamp(uint64_t a) { uint32_t *pg = page_of(a, 0); return pg ? pg[a % PAGE] : 0; }
static void set_stamp(uint64_t a, uint32_t s) { uint32_t *pg = page_of(a, 0); if (pg) pg[a % PAGE] = s; }

static Blk *blk_of(uint64_t a) {
    GTreeNode *n = g_tree_upper_bound(heap, &a);
    n = n ? g_tree_node_previous(n) : g_tree_node_last(heap);
    if (!n) return NULL;
    Blk *b = g_tree_node_value(n);
    return a < b->start + b->size ? b : NULL;
}

/* Activations with S0 <= sp at a Lean entry (S0 < sp elsewhere: at an entry's first access
 * sp == S0 still) have returned. */
static void pop_dead(Vcpu *v, uint64_t sp) { while (v->n && v->a[v->n - 1].s0 <= sp) v->n--; }
static void pop_dead_lt(Vcpu *v, uint64_t sp) { while (v->n && v->a[v->n - 1].s0 < sp) v->n--; }

/* Byte status for Lean-visible accesses. 0: no claim (not stack/heap), 1: initialised,
 * 2: stack uninit, 3: stack copied-uninit, 4: heap block fresh in this run (any access),
 * 5: heap uninit (older block). */
static int status(Vcpu *v, uint64_t a, uint64_t sp) {
    Blk *b = blk_of(a);
    if (b) {
        if (v->n && b->epoch > v->outer_epoch) return 4;
        uint32_t s = stamp(a);
        return s >= b->epoch ? 1 : 5;
    }
    if (a < sp) return 0;
    for (long k = (long)v->n - 1; k >= 0; k--)
        if (v->a[k].s0 > a) {
            if (v->a[k].s0 - a > BELOW) return 0;
            uint32_t s = stamp(a);
            return s >= v->a[k].epoch ? 1 : (s == 1 ? 3 : 2);
        }
    return 0;
}

static void hit(uint64_t pc, int cat) {
    ncat[cat]++;
    uint64_t key = pc << 3 | (uint64_t)cat;
    Hit *h = g_hash_table_lookup(hits, (gpointer)(uintptr_t)key);
    if (!h) {
        h = g_new0(Hit, 1); *h = (Hit){ pc, 0, (int)find_fn(pc), cat };
        g_hash_table_insert(hits, (gpointer)(uintptr_t)key, h);
    }
    h->count++;
}

static void on_entry(unsigned int vi, void *udata) {
    uint32_t fi = (uint32_t)(uintptr_t)udata;
    uint64_t sp = reg(vi, 31);
    g_mutex_lock(&lock);
    Vcpu *v = &vcpus[vi];
    pop_dead(v, sp);
    if (v->n == v->cap) { v->cap = v->cap ? 2 * v->cap : 64; v->a = realloc(v->a, v->cap * sizeof(Act)); }
    uint32_t e = ++gepoch;
    if (v->n == 0) v->outer_epoch = e;
    v->a[v->n++] = (Act){ sp, e, fi };
    fns[fi].calls++;
    for (uint64_t p = (sp - BELOW) / PAGE; p <= (sp + ABOVE) / PAGE; p++) page_of(p * PAGE, 1);
    g_mutex_unlock(&lock);
}

static void on_store(unsigned int vi, qemu_plugin_meminfo_t info, uint64_t va, void *udata) {
    unsigned n = 1u << qemu_plugin_mem_size_shift(info);
    g_mutex_lock(&lock);
    for (unsigned i = 0; i < n; i++) set_stamp(va + i, gepoch);
    g_mutex_unlock(&lock);
}

static void on_lean_access(unsigned int vi, qemu_plugin_meminfo_t info, uint64_t va, void *udata) {
    int st = qemu_plugin_mem_is_store(info);
    unsigned n = 1u << qemu_plugin_mem_size_shift(info);
    uint64_t pc = (uint64_t)(uintptr_t)udata;
    uint64_t sp = reg(vi, 31);
    g_mutex_lock(&lock);
    Vcpu *v = &vcpus[vi];
    pop_dead_lt(v, sp);
    if (!st) nloads++;
    int worst = 1;
    for (unsigned i = 0; i < n; i++) {
        int s = status(v, va + i, sp);
        nstat[s]++;
        if (s == 4) { worst = 4; break; }
        if (!st && s > worst) worst = s;
    }
    if (worst == 4) hit(pc, C_HEAP_FRESH);
    else if (worst == 2) hit(pc, C_STACK);
    else if (worst == 3) hit(pc, C_STACK_CP);
    else if (worst == 5) hit(pc, C_HEAP_UNINIT);
    g_mutex_unlock(&lock);
}

static void add_blk(uint64_t p, uint64_t size) {
    if (!p) return;
    Blk *b = g_new0(Blk, 1); *b = (Blk){ p, size ? size : 1, ++gepoch };
    uint64_t *k = g_new(uint64_t, 1); *k = p;
    g_tree_replace(heap, k, b);
    for (uint64_t q = p / PAGE; q <= (p + b->size - 1) / PAGE; q++) page_of(q * PAGE, 1);
    nalloc++;
}

static void on_hook(unsigned int vi, void *udata) {
    int kind = (int)(uintptr_t)udata;
    uint64_t sp = reg(vi, 31), lr = reg(vi, 30), a0 = reg(vi, 0), a1 = reg(vi, 1), a2 = reg(vi, 2);
    g_mutex_lock(&lock);
    Vcpu *v = &vcpus[vi];
    int from_lean = find_fn(lr - 4) >= 0;
    pop_dead_lt(v, sp);
    if (kind == H_FREE) {
        Blk *b = a0 ? g_tree_lookup(heap, &a0) : NULL;
        if (b) g_tree_remove(heap, &a0);
        g_mutex_unlock(&lock);
        return;
    }
    Pend pd = { kind, lr, sp, a0, a1, a2, from_lean, NULL, 0, 0 };
    if ((kind == H_MEMCMP || kind == H_BCMP) && from_lean && a2) {
        uint8_t *x = g_malloc(a2), *y = g_malloc(a2);
        GByteArray *bx = g_byte_array_new(), *by = g_byte_array_new();
        int ok = qemu_plugin_read_memory_vaddr(a0, bx, a2) && qemu_plugin_read_memory_vaddr(a1, by, a2);
        uint64_t k = a2;
        if (ok) for (uint64_t i = 0; i < a2; i++) if (bx->data[i] != by->data[i]) { k = i + 1; break; }
        int bad = 0, fresh = 0;
        for (uint64_t i = 0; i < k && !bad; i++) {
            int s1 = status(v, a0 + i, sp), s2 = status(v, a1 + i, sp);
            if (s1 == 4 || s2 == 4) fresh = 1;
            else if (s1 >= 2 || s2 >= 2) bad = 1;
        }
        if (bad) hit(lr - 4, C_MEMCMP);
        else if (fresh) hit(lr - 4, C_HEAP_FRESH);
        g_byte_array_free(bx, TRUE); g_byte_array_free(by, TRUE); g_free(x); g_free(y);
        g_mutex_unlock(&lock);
        return;
    }
    if ((kind == H_MEMCPY || kind == H_MEMMOVE) && from_lean) {
        nmemcpy_lean++;
        pd.nstatus = a2; pd.status = g_malloc(a2 ? a2 : 1);
        int fresh = 0;
        for (uint64_t i = 0; i < a2; i++) {
            pd.status[i] = (uint8_t)status(v, a1 + i, sp);
            if (pd.status[i] == 4 || status(v, a0 + i, sp) == 4) fresh = 1;
        }
        if (fresh) hit(lr - 4, C_HEAP_FRESH);
    } else if (kind == H_MEMCPY || kind == H_MEMMOVE || kind == H_MEMCMP || kind == H_BCMP) {
        g_mutex_unlock(&lock);
        return;
    }
    if (kind == H_REALLOC && a0) {
        Blk *b = g_tree_lookup(heap, &a0);
        if (b) {
            pd.oldsize = b->size; pd.nstatus = b->size; pd.status = g_malloc(b->size);
            for (uint64_t i = 0; i < b->size; i++) {
                uint32_t s = stamp(a0 + i);
                pd.status[i] = s >= b->epoch ? 1 : 0;
            }
        }
    }
    if (v->pn == v->pcap) { v->pcap = v->pcap ? 2 * v->pcap : 16; v->p = realloc(v->p, v->pcap * sizeof(Pend)); }
    v->p[v->pn++] = pd;
    g_mutex_unlock(&lock);
}

static void finish(unsigned vi, Vcpu *v, Pend *pd) {
    uint64_t r = reg(vi, 0);
    switch (pd->kind) {
    case H_MALLOC: add_blk(r, pd->a0); break;
    case H_ALIGNED: case H_MEMALIGN: add_blk(r, pd->a1); break;
    case H_POSIX: {
        GByteArray *b = g_byte_array_new();
        if (r == 0 && qemu_plugin_read_memory_vaddr(pd->a0, b, 8)) {
            uint64_t p; memcpy(&p, b->data, 8); add_blk(p, pd->a2);
        }
        g_byte_array_free(b, TRUE);
        break;
    }
    case H_CALLOC:
        add_blk(r, pd->a0 * pd->a1);
        for (uint64_t i = 0; r && i < pd->a0 * pd->a1; i++) set_stamp(r + i, gepoch);
        break;
    case H_REALLOC:
        if (r) {
            add_blk(r, pd->a1);
            uint64_t keep = pd->oldsize < pd->a1 ? pd->oldsize : pd->a1;
            for (uint64_t i = 0; i < keep && pd->status; i++)
                set_stamp(r + i, pd->status[i] ? gepoch : 0);
        }
        break;
    case H_MEMCPY: case H_MEMMOVE:
        for (uint64_t i = 0; i < pd->nstatus; i++)
            if (pd->status[i] >= 2) set_stamp(pd->a0 + i, 1);
        break;
    }
    g_free(pd->status);
}

static void on_tb(unsigned int vi, void *udata) {
    Vcpu *v = &vcpus[vi];
    if (!v->pn) return;
    uint64_t pc = (uint64_t)(uintptr_t)udata;
    uint64_t sp = reg(vi, 31);
    g_mutex_lock(&lock);
    while (v->pn && v->p[v->pn - 1].sp < sp) { g_free(v->p[v->pn - 1].status); v->pn--; } /* unwound */
    while (v->pn && v->p[v->pn - 1].lr == pc && v->p[v->pn - 1].sp == sp) {
        Pend pd = v->p[--v->pn];
        finish(vi, v, &pd);
    }
    g_mutex_unlock(&lock);
}

static void tb_trans(qemu_plugin_id_t id, struct qemu_plugin_tb *tb) {
    size_t ni = qemu_plugin_tb_n_insns(tb);
    qemu_plugin_register_vcpu_tb_exec_cb(tb, on_tb, QEMU_PLUGIN_CB_R_REGS,
                                         (void *)(uintptr_t)qemu_plugin_tb_vaddr(tb));
    for (size_t i = 0; i < ni; i++) {
        struct qemu_plugin_insn *insn = qemu_plugin_tb_get_insn(tb, i);
        uint64_t pc = qemu_plugin_insn_vaddr(insn);
        for (int h = 0; h < NHOOK; h++)
            if (hookaddr[h] && pc == hookaddr[h])
                qemu_plugin_register_vcpu_insn_exec_cb(insn, on_hook, QEMU_PLUGIN_CB_R_REGS,
                                                       (void *)(uintptr_t)h);
        long f = find_fn(pc);
        if (f >= 0) {
            if (pc == fns[f].start)
                qemu_plugin_register_vcpu_insn_exec_cb(insn, on_entry, QEMU_PLUGIN_CB_R_REGS,
                                                       (void *)(uintptr_t)f);
            qemu_plugin_register_vcpu_mem_cb(insn, on_lean_access, QEMU_PLUGIN_CB_R_REGS,
                                             QEMU_PLUGIN_MEM_RW, (void *)(uintptr_t)pc);
        }
        qemu_plugin_register_vcpu_mem_cb(insn, on_store, QEMU_PLUGIN_CB_NO_REGS,
                                         QEMU_PLUGIN_MEM_W, NULL);
    }
}

static void at_exit(qemu_plugin_id_t id, void *p) {
    FILE *o = outpath ? fopen(outpath, "a") : stderr;
    if (!o) return;
    fprintf(o, "{\"loads\":%" PRIu64 ",\"allocs\":%" PRIu64 ",\"memcpy_from_lean\":%" PRIu64,
            nloads, nalloc, nmemcpy_lean);
    for (int c = 0; c < NCAT; c++) fprintf(o, ",\"%s\":%" PRIu64, catname[c], ncat[c]);
    fprintf(o, ",\"nstat\":[%lu,%lu,%lu,%lu,%lu,%lu]", nstat[0],nstat[1],nstat[2],nstat[3],nstat[4],nstat[5]);
    fprintf(o, ",\"hooks\":{");
    for (int h = 0; h < NHOOK; h++) fprintf(o, "%s\"%s\":%d", h ? "," : "", hookname[h], hookaddr[h] != 0);
    fprintf(o, "},\"calls\":{");
    int first = 1;
    for (size_t i = 0; i < nfns; i++) if (fns[i].calls) {
        fprintf(o, "%s\"%s\":%" PRIu64, first ? "" : ",", fns[i].name, fns[i].calls); first = 0;
    }
    fprintf(o, "},\"sites\":[");
    GHashTableIter it; gpointer k, val; first = 1;
    g_hash_table_iter_init(&it, hits);
    while (g_hash_table_iter_next(&it, &k, &val)) {
        Hit *h = val;
        fprintf(o, "%s{\"pc\":%" PRIu64 ",\"count\":%" PRIu64 ",\"cat\":\"%s\",\"fn\":\"%s\",\"pc_off\":%" PRIu64 "}",
                first ? "" : ",", h->pc, h->count, catname[h->cat], h->fn >= 0 ? fns[h->fn].name : "?",
                h->fn >= 0 ? h->pc - fns[h->fn].start : 0);
        first = 0;
    }
    fprintf(o, "]}\n");
    if (o != stderr) fclose(o);
}

static int cmp_fn(const void *a, const void *b) {
    const Fn *x = a, *y = b; return x->start < y->start ? -1 : x->start > y->start;
}

QEMU_PLUGIN_EXPORT int qemu_plugin_install(qemu_plugin_id_t id, const qemu_info_t *info,
                                           int argc, char **argv) {
    char *fpath = NULL, *spath = NULL;
    for (int i = 0; i < argc; i++) {
        if (g_str_has_prefix(argv[i], "funcs=")) fpath = argv[i] + 6;
        else if (g_str_has_prefix(argv[i], "syms=")) spath = argv[i] + 5;
        else if (g_str_has_prefix(argv[i], "out=")) outpath = g_strdup(argv[i] + 4);
    }
    if (!fpath) { fprintf(stderr, "uninit_plugin: funcs=FILE required\n"); return -1; }
    FILE *f = fopen(fpath, "r");
    if (!f) { perror(fpath); return -1; }
    size_t cap = 1024; fns = malloc(cap * sizeof(Fn));
    char name[4096]; uint64_t s, e;
    while (fscanf(f, "%" SCNx64 " %" SCNx64 " %4095s", &s, &e, name) == 3) {
        if (nfns == cap) { cap *= 2; fns = realloc(fns, cap * sizeof(Fn)); }
        fns[nfns++] = (Fn){ s, e, g_strdup(name), 0 };
    }
    fclose(f);
    qsort(fns, nfns, sizeof(Fn), cmp_fn);
    if (spath && (f = fopen(spath, "r"))) {
        while (fscanf(f, "%4095s %" SCNx64, name, &s) == 2)
            for (int h = 0; h < NHOOK; h++) if (strcmp(name, hookname[h]) == 0) hookaddr[h] = s;
        fclose(f);
    }
    hits = g_hash_table_new(g_direct_hash, g_direct_equal);
    shadow = g_hash_table_new(g_direct_hash, g_direct_equal);
    heap = g_tree_new_full(cmp_u64, NULL, g_free, g_free);
    qemu_plugin_register_vcpu_tb_trans_cb(id, tb_trans);
    qemu_plugin_register_atexit_cb(id, at_exit, NULL);
    return 0;
}
