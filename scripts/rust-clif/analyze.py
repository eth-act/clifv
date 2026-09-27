#!/usr/bin/env python3
"""Aggregate the CLIF dumped by scripts/rust-clif/dump.sh.

usage: analyze.py [OUT_DIR] [--json FILE] [--extra NAME=CLIF_DIR]...
       (default OUT_DIR /tmp/rust-clif-survey/out; --extra adds e.g. core.sh's core/alloc dirs)

Reads OUT_DIR/<profile>/<crate>/<crate>.clif/*.{unopt,opt}.clif and prints markdown tables:
opcode histograms (per profile, per category), E/S/neither classification, types, memory
flags, trap codes, callees, stack slots, globals, signatures. `--json` also writes the raw
counters. E and S are clif-subset-v1 (docs/contracts/clif-subset.md).
"""

import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

E = set("""iconst iadd isub ineg imul umulhi smulhi udiv urem sdiv srem band bor bxor bnot
ishl ushr sshr rotl rotr clz ctz popcnt icmp uextend sextend ireduce load store uload8 uload16
uload32 sload8 sload16 sload32 istore8 istore16 istore32 stack_addr jump brif br_table return
call trap""".split())
S_ONLY = set("""select trapz trapnz uadd_overflow_trap uadd_overflow sadd_overflow usub_overflow
ssub_overflow umul_overflow smul_overflow bitrev bswap cls iabs smin smax umin umax uadd_sat
sadd_sat usub_sat ssub_sat bmask iconcat isplit nop select_spectre_guard bitselect
uadd_overflow_cin sadd_overflow_cin usub_overflow_bin ssub_overflow_bin atomic_rmw atomic_cas
atomic_load atomic_store fence bitcast return_call""".split())

MEM_OPS = {"load", "store", "uload8", "uload16", "uload32", "sload8", "sload16", "sload32",
           "istore8", "istore16", "istore32", "atomic_load", "atomic_store", "atomic_rmw",
           "atomic_cas"}
FLAG_WORDS = {"notrap", "aligned", "readonly", "little", "big", "can_move", "checked",
              "heap_oob", "int_ovf", "int_divz", "stk_ovf", "bad_toint"}
CATEGORY = {
    "a_arith": "(a) arith", "b_slices": "(b) slices", "c_structs_enums": "(c) structs/enums",
    "d_loops_iters": "(d) loops/iters", "e_option_result": "(e) Option/Result",
    "f_crypto": "(f) crypto", "g_u128": "(g) u128", "h_dyn_generic": "(h) generic/dyn",
    "i_alloc": "(i) alloc",
}
PROFILES = ["debug", "release", "release-oc"]
TYPE_RE = re.compile(r"\b(i8|i16|i32|i64|i128|f16|f32|f64|f128|i\d+x\d+|f\d+x\d+)\b")
RES_RE = re.compile(r"^(v\d+(?:\s*,\s*v\d+)*)\s*=\s*(.*)$")
ALIAS_RE = re.compile(r"^v\d+\s*->\s*v\d+$")
BLOCK_RE = re.compile(r"^(block\d+)(\((.*)\))?(\s+cold)?:$")
DECL_RE = re.compile(r"^(ss|gv|sig|fn|jt|dss|const)(\d+)\s*=\s*(.*)$")


def classify(op):
    if op in E:
        return "E"
    if op in S_ONLY:
        return "S\\E"
    return "neither"


def callee_kind(decl, comment):
    """Classify a `fnN = …` declaration by the symbol cg_clif records in its comment."""
    text = decl + " " + comment
    if re.search(r"=\s*(colocated\s+)?%[A-Z]", "=" + decl) or re.match(r"(colocated\s+)?%[A-Z]", decl):
        return "cranelift libcall (" + re.search(r"%(\w+)", decl).group(1) + ")"
    if "panic" in text or "unwrap_failed" in text or "expect_failed" in text \
            or "slice_index_fail" in text or "slice_end_index" in text \
            or "slice_start_index" in text or "copy_from_slice_len_mismatch" in text \
            or "len_mismatch_fail" in text or "unreachable" in text:
        return "panic path"
    m = re.search(r'"(__\w+)"', comment) or re.search(r"::(__rust_\w+)\)", comment)
    if m:
        return "runtime symbol " + m.group(1)
    if "Instance" in comment:
        return "Rust fn (colocated)" if decl.startswith("colocated") else "Rust fn (upstream)"
    m = re.search(r'"([^"]+)"', comment)
    if m:
        return "Rust fn (by symbol)" if m.group(1).startswith("_R") else "external symbol " + m.group(1)
    return "other"


class Func:
    def __init__(self, path, profile, crate, stage):
        self.path, self.profile, self.crate, self.stage = path, profile, crate, stage
        self.ops = Counter()
        self.types = Counter()
        self.memflags = Counter()
        self.traps = Counter()
        self.icmp = Counter()
        self.callees = Counter()
        self.slots = []
        self.globals = Counter()
        self.sig_cc = Counter()
        self.abi_attrs = Counter()
        self.blocks = 0
        self.cold_blocks = 0
        self.insts = 0
        self.user = False
        self.name = ""
        self.features = set()
        self.i128ops = Counter()


def parse(path, profile, crate, stage):
    f = Func(path, profile, crate, stage)
    fndecls = {}
    lines = path.read_text().splitlines()
    for raw in lines:
        if raw.startswith("; instance"):
            f.user = f" ~ {crate}[" in raw
            m = re.search(r"~ ([^)]+)\)", raw)
            f.name = m.group(1) if m else ""
            break
    in_fn = False
    used = set()
    for raw in lines:
        line = raw.strip()
        if line.startswith("function "):
            in_fn = True
            m = re.match(r"function\s+\S+\((.*)\)(\s*->\s*(.*?))?\s+(\w+)\s*\{$", line)
            if m:
                f.sig_cc[m.group(4)] += 1
                for t in TYPE_RE.findall(m.group(1) + " " + (m.group(3) or "")):
                    f.types[t] += 1
                for a in re.findall(r"\b(uext|sext|sret|sarg\(\d+\))", line):
                    f.abi_attrs[a] += 1
                    f.features.add(f"`{a}` param/return attribute")
                if m.group(3) and "," in m.group(3):
                    f.features.add("multiple return values")
            prev = None
            continue
        if not in_fn or not line or line.startswith(";") or line == "}":
            continue
        code, _, comment = line.partition(";")
        code, comment = code.strip(), comment.strip()
        if not code:
            continue
        m = DECL_RE.match(code)
        if m:
            kind, num, rest = m.groups()
            if kind == "ss":
                sm = re.match(r"(\w+)\s+(\d+)(?:,\s*align\s*=\s*(\d+))?", rest)
                f.slots.append((sm.group(1), int(sm.group(2)), int(sm.group(3) or 0)))
                f.features.add("stack slots")
            elif kind == "gv":
                gk = re.sub(r"userextname\d+", "userextnameN", rest)
                gk = re.sub(r"[+-]\d+$", "+off", gk)
                note = "static item" if comment.startswith("DefId(") else re.sub(r"\d+", "N", comment)
                f.globals[gk + (" ; " + note if comment else "")] += 1
            elif kind == "sig":
                cc = rest.split()[-1]
                f.sig_cc[cc] += 1
                for a in re.findall(r"\b(uext|sext|sret|sarg\(\d+\))", rest):
                    f.abi_attrs[a] += 1
                for t in TYPE_RE.findall(rest):
                    f.types[t] += 1
            elif kind == "fn":
                fndecls["fn" + num] = callee_kind(rest, comment)
                f.features.add("`sigN` + `fnN = u0:N sigN` declarations")
            continue
        m = BLOCK_RE.match(code)
        if m:
            f.blocks += 1
            if m.group(4):
                f.cold_blocks += 1
                f.features.add("`cold` blocks")
            prev = "block start"
            for t in TYPE_RE.findall(m.group(3) or ""):
                f.types[t] += 1
            continue
        if ALIAS_RE.match(code):
            f.features.add("value aliases `vA -> vB`")
            if code.split()[0] in used:
                f.features.add("alias `vA -> vB` placed after a use of vA")
            continue
        m = RES_RE.match(code)
        rest = m.group(2) if m else code
        used.update(re.findall(r"\bv\d+\b", rest))
        toks = rest.replace(",", " ").split()
        opty = toks[0]
        op, _, ty = opty.partition(".")
        f.ops[op] += 1
        f.insts += 1
        if ty:
            f.types[ty] += 1
        for t in TYPE_RE.findall(rest[len(opty):]):
            f.types[t] += 1
        if "i128" in rest:
            f.i128ops[op] += 1
            f.features.add("`i128` values")
        if op in ("symbol_value", "func_addr", "call_indirect", "select", "br_table", "iconcat",
                  "nop"):
            f.features.add(f"`{op}`")
        if op in MEM_OPS:
            flags = [t for t in toks[1:] if t in FLAG_WORDS or re.fullmatch(r"user\d+", t)]
            f.memflags[op + ": " + (" ".join(flags) or "(none)")] += 1
        if op in ("trap", "trapz", "trapnz"):
            f.traps[op + " " + toks[-1]] += 1
            f.traps[f"{op} {toks[-1]} after " + ("a call" if prev == "call" else prev or "?")] += 1
        if op == "icmp":
            f.icmp[toks[1]] += 1
        if op in ("call", "return_call"):
            fnref = re.match(r"(fn\d+)", toks[1]).group(1)
            f.callees[fndecls.get(fnref, "?")] += 1
            k = fndecls.get(fnref, "?")
            f.features.add("call: " + (k if k.startswith(("panic", "cranelift", "runtime", "external")) else "other"))
        if op != "nop":
            prev = op
    return f


def load(out):
    funcs = []
    for prof in PROFILES:
        for crate in CATEGORY:
            d = out / prof / crate / f"{crate}.clif"
            if not d.is_dir():
                continue
            for p in sorted(d.iterdir()):
                for stage in ("unopt", "opt"):
                    if p.name.endswith(f".{stage}.clif"):
                        funcs.append(parse(p, prof, crate, stage))
    return funcs


def total(funcs, attr):
    c = Counter()
    for f in funcs:
        c.update(getattr(f, attr))
    return c


def table(headers, rows):
    out = ["| " + " | ".join(headers) + " |", "| " + " | ".join("---" for _ in headers) + " |"]
    out += ["| " + " | ".join(str(x) for x in r) + " |" for r in rows]
    return "\n".join(out)


def counter_table(title, c, n=None):
    rows = [(f"`{k}`", v) for k, v in c.most_common(n)]
    return f"#### {title}\n\n" + table(["item", "count"], rows) + "\n"


def report(funcs, profs, detail, per_category):
    """Markdown sections for the functions of profiles `profs` (`detail`: profiles that get
    the per-feature detail tables; `per_category`: add the corpus per-category table)."""
    funcs = [f for f in funcs if f.profile in profs]
    un = [f for f in funcs if f.stage == "unopt"]
    md = []

    rows = []
    for prof in profs:
        fs = [f for f in un if f.profile == prof]
        rows.append((prof, len(fs), sum(f.user for f in fs), sum(f.insts for f in fs),
                     sum(f.blocks for f in fs), sum(f.cold_blocks for f in fs)))
    md.append("### Size (unopt CLIF)\n\n" + table(
        ["profile", "functions", "of which the crate's own items", "instructions", "blocks", "cold blocks"], rows))

    # Opcode histogram with classes, per profile, unopt and opt.
    ops_by = {(p, s): total([f for f in funcs if f.profile == p and f.stage == s], "ops")
              for p in profs for s in ("unopt", "opt")}
    allops = sorted(set().union(*ops_by.values()), key=lambda o: (-ops_by[(profs[0], "unopt")][o], o))
    rows = [(f"`{o}`", classify(o)) + tuple(ops_by[(p, s)][o] for s in ("unopt", "opt") for p in profs)
            for o in allops]
    md.append("### Opcode histogram (all functions)\n\n" + table(
        ["opcode", "class"] + [f"{p} {s}" for s in ("unopt", "opt") for p in profs], rows))

    rows = []
    for p in profs:
        for s in ("unopt", "opt"):
            c = ops_by[(p, s)]
            by = Counter()
            ob = Counter()
            for o, n in c.items():
                by[classify(o)] += n
                ob[classify(o)] += 1
            tot = sum(c.values())
            rows.append((p, s, tot) + tuple(f"{ob[k]} ops / {by[k]} ({100 * by[k] / tot:.1f}%)"
                                             for k in ("E", "S\\E", "neither")))
    md.append("### E / S / neither (distinct opcodes / instruction count)\n\n" + table(
        ["profile", "stage", "instructions", "E", "S\\E", "neither"], rows))

    if per_category:
        rows = []
        for crate, cat in CATEGORY.items():
            cells = []
            for p in ("debug", "release"):
                c = total([f for f in un if f.profile == p and f.crate == crate], "ops")
                cells.append(", ".join(f"`{o}`×{n}" for o, n in c.most_common() if o not in E) or "—")
            rows.append((cat,) + tuple(cells))
        md.append("### Non-E opcodes per category (unopt)\n\n" + table(["category", "debug", "release"], rows))

    # Functions fully inside E / S (opcodes only; non-opcode features are listed separately).
    rows = []
    for p in profs:
        fs = [f for f in un if f.profile == p]
        inE = sum(all(o in E for o in f.ops) for f in fs)
        inE_nop = sum(all(o in E or o == "nop" for o in f.ops) for f in fs)
        inS = sum(all(o in E or o in S_ONLY for o in f.ops) for f in fs)
        rows.append((p, len(fs), inE, inE_nop, inS))
    md.append("### Functions whose opcodes all lie in a subset (unopt)\n\n" + table(
        ["profile", "functions", "only E", "only E + nop", "only S"], rows))

    feats = sorted(set().union(*(f.features for f in un)))
    rows = [(f,) + tuple(sum(f in g.features for g in un if g.profile == p) for p in profs)
            for f in feats]
    md.append("### Features: functions using each (unopt)\n\n" + table(["feature"] + profs, rows))

    i128 = {p: total([f for f in un if f.profile == p], "i128ops") for p in profs}
    ops128 = sorted(set().union(*i128.values()))
    md.append("### Instructions mentioning `i128` (unopt)\n\n" + table(
        ["opcode"] + profs, [(f"`{o}`",) + tuple(i128[p][o] for p in profs) for o in ops128]))

    for p in detail:
        fs = [f for f in un if f.profile == p]
        md.append(f"### {p}: detail (unopt)\n")
        md.append(counter_table("Types (suffixes, signatures, block params)", total(fs, "types")))
        md.append(counter_table("Memory ops and flags", total(fs, "memflags")))
        md.append(counter_table("Traps", total(fs, "traps")))
        md.append(counter_table("icmp condition codes", total(fs, "icmp")))
        md.append(counter_table("Direct call targets (by kind)", total(fs, "callees"), 25))
        md.append(counter_table("Calling conventions (function + sigN)", total(fs, "sig_cc")))
        md.append(counter_table("ABI attributes on params/returns", total(fs, "abi_attrs")))
        md.append(counter_table("Global value declarations", total(fs, "globals")))
        slots = [s for f in fs for s in f.slots]
        sizes = Counter(s[1] for s in slots)
        md.append(f"#### Stack slots\n\n{len(slots)} slots in {sum(bool(f.slots) for f in fs)} of "
                  f"{len(fs)} functions; kinds {dict(Counter(s[0] for s in slots))}; aligns "
                  f"{dict(sorted(Counter(s[2] for s in slots).items()))}; largest {max(sizes) if sizes else 0} bytes; "
                  f"sizes {dict(sorted(sizes.items()))}\n")
    return md


def main():
    args = sys.argv[1:]
    jpath = None
    extras = []
    while "--json" in args or "--extra" in args:
        i = args.index("--json") if "--json" in args else args.index("--extra")
        if args[i] == "--json":
            jpath = args[i + 1]
        else:
            extras.append(args[i + 1].split("=", 1))
        del args[i:i + 2]
    out = Path(args[0] if args else "/tmp/rust-clif-survey/out")
    funcs = load(out)
    md = ["## Corpus"] + report(funcs, PROFILES, ["debug", "release"], True)
    if extras:
        for name, d in extras:
            for p in sorted(Path(d).iterdir()):
                for stage in ("unopt", "opt"):
                    if p.name.endswith(f".{stage}.clif"):
                        funcs.append(parse(p, name, name, stage))
        names = [n for n, _ in extras]
        md += ["## Extra directories: " + ", ".join(names)] + report(funcs, names, names, False)
    print("\n\n".join(md))
    if jpath:
        data = [{"file": str(f.path), "profile": f.profile, "crate": f.crate, "stage": f.stage,
                 "user": f.user, "name": f.name, "ops": f.ops, "types": f.types,
                 "memflags": f.memflags, "traps": f.traps, "callees": f.callees,
                 "slots": f.slots, "globals": f.globals, "sig_cc": f.sig_cc} for f in funcs]
        Path(jpath).write_text(json.dumps(data, indent=0))


if __name__ == "__main__":
    main()
