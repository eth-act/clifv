/* QEMU TCG plugin (linux-user, aarch64): dynamic count of loads by Lean-compiled code that
 * read stack bytes not written since the activation owning them started -- the reads on which
 * Clif.run (FV/Clif/Mem.lean: slot bytes start `none`) is `stuck`.
 *
 * Model: every Lean-compiled function entry (pc == start, from funcs=FILE "start end name"
 * lines) pushes an activation (S0 = sp at entry, epoch = ++global). Every store anywhere stamps
 * its bytes with the current epoch (only on tracked pages: [S0 - 1 MiB, S0 + 64 KiB] of every
 * activation). A load executed by Lean-compiled code at address a with sp <= a is checked
 * against its owner, the innermost live activation with S0 > a: a byte is initialised iff its
 * stamp >= the owner's epoch. Activations with S0 <= sp are dead (popped lazily).
 * Under-approximation: bytes copied uninitialised by non-Lean code (memcpy) count as written.
 *
 * Build: gcc -shared -fPIC -O2 -I$QEMU/include/qemu $(pkg-config --cflags glib-2.0) ...
 * Run:   qemu-aarch64 -plugin ./uninit_plugin.so,funcs=F,out=O EXE ARGS
 */
#include <glib.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <qemu-plugin.h>

QEMU_PLUGIN_EXPORT int qemu_plugin_version = QEMU_PLUGIN_VERSION;

typedef struct { uint64_t start, end; char *name; uint64_t calls; } Fn;
static Fn *fns; static size_t nfns;

typedef struct { uint64_t s0; uint32_t epoch; uint32_t fn; } Act;
typedef struct { Act *a; size_t n, cap; struct qemu_plugin_register *sp; GByteArray *buf; } Vcpu;
static Vcpu vcpus[256];

typedef struct { uint64_t pc; uint64_t count; uint32_t fn, owner; int64_t off; unsigned size; } Hit;
static GHashTable *hits;      /* pc -> Hit* */
static GHashTable *shadow;    /* page -> uint32_t[4096] */
static uint32_t gepoch;
static uint64_t nloads, nchecked, nhits;
static GMutex lock;
static char *outpath;

#define PAGE 4096ULL
#define BELOW (1ULL << 20)
#define ABOVE (64ULL << 10)

static long find_fn(uint64_t pc) {
    size_t lo = 0, hi = nfns;
    while (lo < hi) { size_t m = (lo + hi) / 2; if (fns[m].start <= pc) lo = m + 1; else hi = m; }
    if (lo == 0) return -1;
    return pc < fns[lo - 1].end ? (long)(lo - 1) : -1;
}

static uint64_t read_sp(unsigned int vi) {
    Vcpu *v = &vcpus[vi];
    if (!v->sp) {
        GArray *regs = qemu_plugin_get_registers();
        for (guint i = 0; i < regs->len; i++) {
            qemu_plugin_reg_descriptor *d = &g_array_index(regs, qemu_plugin_reg_descriptor, i);
            if (strcmp(d->name, "sp") == 0) v->sp = d->handle;
        }
        g_array_free(regs, TRUE);
        v->buf = g_byte_array_new();
        if (!v->sp) { fprintf(stderr, "uninit_plugin: no sp register\n"); exit(3); }
    }
    g_byte_array_set_size(v->buf, 0);
    qemu_plugin_read_register(v->sp, v->buf);
    uint64_t sp = 0; memcpy(&sp, v->buf->data, 8);
    return sp;
}

static void pop_dead(Vcpu *v, uint64_t sp) { while (v->n && v->a[v->n - 1].s0 <= sp) v->n--; }

static void on_entry(unsigned int vi, void *udata) {
    uint32_t fi = (uint32_t)(uintptr_t)udata;
    uint64_t sp = read_sp(vi);
    g_mutex_lock(&lock);
    Vcpu *v = &vcpus[vi];
    pop_dead(v, sp);
    if (v->n == v->cap) { v->cap = v->cap ? 2 * v->cap : 64; v->a = realloc(v->a, v->cap * sizeof(Act)); }
    v->a[v->n++] = (Act){ sp, ++gepoch, fi };
    fns[fi].calls++;
    for (uint64_t p = (sp - BELOW) / PAGE; p <= (sp + ABOVE) / PAGE; p++)
        if (!g_hash_table_contains(shadow, (gpointer)(uintptr_t)p))
            g_hash_table_insert(shadow, (gpointer)(uintptr_t)p, g_new0(uint32_t, PAGE));
    g_mutex_unlock(&lock);
}

static void on_store(unsigned int vi, qemu_plugin_meminfo_t info, uint64_t va, void *udata) {
    unsigned n = 1u << qemu_plugin_mem_size_shift(info);
    g_mutex_lock(&lock);
    for (unsigned i = 0; i < n; i++) {
        uint64_t a = va + i;
        uint32_t *pg = g_hash_table_lookup(shadow, (gpointer)(uintptr_t)(a / PAGE));
        if (pg) pg[a % PAGE] = gepoch;
    }
    g_mutex_unlock(&lock);
}

static void on_lean_load(unsigned int vi, qemu_plugin_meminfo_t info, uint64_t va, void *udata) {
    if (qemu_plugin_mem_is_store(info)) return;
    unsigned n = 1u << qemu_plugin_mem_size_shift(info);
    uint64_t pc = (uint64_t)(uintptr_t)udata;
    uint64_t sp = read_sp(vi);
    g_mutex_lock(&lock);
    nloads++;
    Vcpu *v = &vcpus[vi];
    pop_dead(v, sp);
    if (va >= sp) {
        long owner = -1;
        for (long k = (long)v->n - 1; k >= 0; k--) if (v->a[k].s0 > va) { owner = k; break; }
        if (owner >= 0 && v->a[owner].s0 - va <= BELOW) {
            nchecked++;
            int bad = 0;
            for (unsigned i = 0; i < n; i++) {
                uint64_t a = va + i;
                uint32_t *pg = g_hash_table_lookup(shadow, (gpointer)(uintptr_t)(a / PAGE));
                if (!pg || pg[a % PAGE] < v->a[owner].epoch) bad = 1;
            }
            if (bad) {
                nhits++;
                Hit *h = g_hash_table_lookup(hits, (gpointer)(uintptr_t)pc);
                if (!h) {
                    h = g_new0(Hit, 1);
                    *h = (Hit){ pc, 0, (uint32_t)find_fn(pc), v->a[owner].fn,
                                (int64_t)(va - v->a[owner].s0), n };
                    g_hash_table_insert(hits, (gpointer)(uintptr_t)pc, h);
                }
                h->count++;
            }
        }
    }
    g_mutex_unlock(&lock);
}

static void tb_trans(qemu_plugin_id_t id, struct qemu_plugin_tb *tb) {
    size_t ni = qemu_plugin_tb_n_insns(tb);
    for (size_t i = 0; i < ni; i++) {
        struct qemu_plugin_insn *insn = qemu_plugin_tb_get_insn(tb, i);
        uint64_t pc = qemu_plugin_insn_vaddr(insn);
        long f = find_fn(pc);
        if (f >= 0) {
            if (pc == fns[f].start)
                qemu_plugin_register_vcpu_insn_exec_cb(insn, on_entry, QEMU_PLUGIN_CB_R_REGS,
                                                       (void *)(uintptr_t)f);
            qemu_plugin_register_vcpu_mem_cb(insn, on_lean_load, QEMU_PLUGIN_CB_R_REGS,
                                             QEMU_PLUGIN_MEM_R, (void *)(uintptr_t)pc);
        }
        qemu_plugin_register_vcpu_mem_cb(insn, on_store, QEMU_PLUGIN_CB_NO_REGS,
                                         QEMU_PLUGIN_MEM_W, NULL);
    }
}

static void at_exit(qemu_plugin_id_t id, void *p) {
    FILE *o = outpath ? fopen(outpath, "a") : stderr;
    if (!o) return;
    fprintf(o, "{\"loads\":%" PRIu64 ",\"checked\":%" PRIu64 ",\"hits\":%" PRIu64 ",\"calls\":{", nloads, nchecked, nhits);
    int first = 1;
    for (size_t i = 0; i < nfns; i++) if (fns[i].calls) {
        fprintf(o, "%s\"%s\":%" PRIu64, first ? "" : ",", fns[i].name, fns[i].calls); first = 0;
    }
    fprintf(o, "},\"sites\":[");
    GHashTableIter it; gpointer k, val; first = 1;
    g_hash_table_iter_init(&it, hits);
    while (g_hash_table_iter_next(&it, &k, &val)) {
        Hit *h = val;
        fprintf(o, "%s{\"pc\":%" PRIu64 ",\"count\":%" PRIu64 ",\"fn\":\"%s\",\"pc_off\":%" PRIu64 ",\"owner\":\"%s\",\"off\":%" PRId64 ",\"size\":%u}",
                first ? "" : ",", h->pc, h->count, fns[h->fn].name, h->pc - fns[h->fn].start,
                fns[h->owner].name, h->off, h->size);
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
    char *fpath = NULL;
    for (int i = 0; i < argc; i++) {
        if (g_str_has_prefix(argv[i], "funcs=")) fpath = argv[i] + 6;
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
    hits = g_hash_table_new(g_direct_hash, g_direct_equal);
    shadow = g_hash_table_new(g_direct_hash, g_direct_equal);
    qemu_plugin_register_vcpu_tb_trans_cb(id, tb_trans);
    qemu_plugin_register_atexit_cb(id, at_exit, NULL);
    return 0;
}
