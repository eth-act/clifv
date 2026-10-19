#!/usr/bin/env python3
"""Float fallbacks of a `cargo fv` run (S11g, #35): classify the functions of a
`target/fv-report.json` that fall back to cg_clif, and compare two runs function by function.

usage: scripts/float-fallbacks.py REPORT [--before REPORT] [--list]

REPORT is a `target/fv-report.json` written by `cargo fv` (rust/crates/cargo-fv/src/report.rs).
Each function's cg_clif dump `<dir of the unit's artifact>/<unit>.clif/<symbol>.unopt.clif` must
still be on disk (the target directory of that run).

Output:
  * totals (functions / verified / unverified / fallback) and the fallback reasons in buckets:
    `float` (`unsupported: type f32|f64`, `opcode f32const|f64const`), `simd` (vector types),
    `budget` (validation budget), `other`;
  * the float fallbacks classified by the float constructs of their `.unopt.clif` (one count per
    function): data movement only (no float arithmetic opcode) vs with float arithmetic; of the
    movement-only ones, those with a float in their own or a callee's signature, those with only
    float loads/stores, those with only float constants;
  * per float operation, the functions using it (among the float fallbacks);
  * per package, the float fallbacks.
With --before: the same function population is matched by identity (package, unit crate, symbol;
else package, unit crate, instance) and every function whose status changed is counted
(`fallback -> verified` …); the float fallbacks of BEFORE are followed into the new run.
--list prints each float fallback (package, symbol, class, operations).
"""
import argparse, collections, json, os, re, sys

FLOAT_ARITH = {
    "fadd", "fsub", "fmul", "fdiv", "fma", "fneg", "fabs", "sqrt", "fmin", "fmax", "fcopysign",
    "ceil", "floor", "trunc", "nearest", "fcmp", "fpromote", "fdemote", "fcvt_from_uint",
    "fcvt_from_sint", "fcvt_to_uint", "fcvt_to_sint", "fcvt_to_uint_sat", "fcvt_to_sint_sat",
    "fvdemote", "fvpromote_low",
}
# Opcodes whose result is a float when their operands are (CLIF infers the controlling type).
FLOAT_RESULT_SAME = {"fadd", "fsub", "fmul", "fdiv", "fma", "fneg", "fabs", "sqrt", "fmin",
                     "fmax", "fcopysign", "ceil", "floor", "trunc", "nearest", "select", "copy"}
FTY = re.compile(r"\b(f32|f64)\b")
DEF = re.compile(r"^\s*(v\d+(?:\s*,\s*v\d+)*)\s*=\s*([a-z_0-9]+)(?:\.([a-z0-9]+))?\s*(.*)$")
STMT = re.compile(r"^\s*([a-z_0-9]+)(?:\.([a-z0-9]+))?\s+(.*)$")
BLOCK = re.compile(r"^\s*block\d+\((.*)\):")
DECL = re.compile(r"^\s*(sig\d+|fn\d+)\s*=\s*(.*)$")
VAL = re.compile(r"\bv\d+\b")


_scans = {}


def float_scan(u, f):
    """(ops, flags) of the function's dump, None without a dump (memoised)."""
    k = (u.get("artifact", ""), u["unit"], f["symbol"])
    if k not in _scans:
        p = dump_of(u, f["symbol"])
        _scans[k] = scan(p) if p else None
    return _scans[k]


def bucket(u, f):
    """`float` (the dump has an f32/f64 value, parameter, signature or constant; without a dump,
    a float reason), `simd` (vector types), `budget` (validation budget) or `other`."""
    r = f.get("reason") or ""
    if re.search(r"type [a-z0-9]+x\d+", r):
        return "simd"
    if "validation budget" in r:
        return "budget"
    s = float_scan(u, f)
    if s is not None:
        return "float" if (s[0] or s[1]) else "other"
    return "float" if re.search(r"\bf(32|64)\b", r) else "other"


def norm(reason):
    return re.sub(r"\bv\d+\b", "vN", reason or "")


def scan(path):
    """Float constructs of one `.unopt.clif` function: (ops, flags)."""
    ops = collections.Counter()
    flags = set()
    fty = {}  # value -> float type
    sigs = {}  # sigN -> list of return float types (None for int)
    fnsig = {}
    text = open(path).read()
    for line in text.splitlines():
        if line.startswith(";") or line.startswith("set ") or line.startswith("target "):
            continue
        s = re.sub(r"^\s*@[0-9a-f]+\s+", "", line.split(";", 1)[0].rstrip())
        if not s.strip():
            continue
        if s.startswith("function "):
            if FTY.search(s):
                flags.add("sig")
            continue
        m = DECL.match(s)
        if m:
            name, rhs = m.groups()
            if name.startswith("sig"):
                if FTY.search(rhs):
                    flags.add("callee_sig")
                rets = rhs.split("->", 1)[1] if "->" in rhs else ""
                sigs[name] = [t if t in ("f32", "f64") else None
                              for t in re.findall(r"\b([if]\d+|i128|[a-z0-9]+x\d+)\b", rets)]
            else:
                sm = re.search(r"\b(sig\d+)\b", rhs)
                if sm:
                    fnsig[name] = sm.group(1)
            continue
        m = BLOCK.match(s)
        if m:
            for v, t in re.findall(r"(v\d+)\s*:\s*([a-z0-9]+)", m.group(1)):
                if t in ("f32", "f64"):
                    fty[v] = t
                    flags.add("block_param")
            continue
        m = DEF.match(s)
        if m:
            vs, op, ty, rest = m.groups()
            vs = [v.strip() for v in vs.split(",")]
            args = VAL.findall(rest)
            rt = None
            if op == "fcmp" or op.startswith("fcvt_to_"):
                rt = None  # the suffix is the operand type; the result is an integer
            elif ty in ("f32", "f64"):
                rt = ty
            elif op in ("f32const", "f64const"):
                rt = op[:3]
            elif op in ("fcvt_from_uint", "fcvt_from_sint", "fpromote", "fdemote"):
                rt = ty
            elif op in FLOAT_RESULT_SAME:
                ft = [fty[a] for a in args if a in fty]
                rt = ft[-1] if ft else None
            if op in ("call", "call_indirect"):
                callee = re.match(r"\s*(fn\d+|sig\d+)", rest)
                sig = None
                if callee:
                    c = callee.group(1)
                    sig = sigs.get(fnsig.get(c, c))
                for v, t in zip(vs, sig or []):
                    if t:
                        fty[v] = t
                        ops[f"call ret {t}"] += 1
                rt = None
            elif rt:
                for v in vs:
                    fty[v] = rt
            used_float = any(a in fty for a in args)
            if op in FLOAT_ARITH:
                ops[op if op not in ("fcvt_to_uint_sat", "fcvt_to_sint_sat") or not ty
                    else f"{op}.{ty}"] += 1
            elif op in ("call", "call_indirect") and used_float:
                ops["call arg (float)"] += 1
            elif rt or used_float:
                if op in ("load", "f32const", "f64const", "bitcast", "select"):
                    ops[f"{op}.{rt}" if op in ("load", "bitcast") and rt else op] += 1
                else:
                    ops[f"{op} (float operand)"] += 1
            continue
        m = STMT.match(s)
        if m:
            op, ty, rest = m.groups()
            args = VAL.findall(rest)
            if op == "store" and args and args[0] in fty:
                ops[f"store.{fty[args[0]]}"] += 1
            elif op in ("return", "jump", "brif", "br_table") and any(a in fty for a in args):
                ops[f"{op} (float operand)"] += 1
            elif op in ("call", "call_indirect", "try_call", "try_call_indirect") and any(
                    a in fty for a in args):
                ops["call arg (float)"] += 1
    return ops, flags


def classify(ops, flags):
    names = {o.split(".")[0].split(" ")[0] for o in ops}
    if names & FLOAT_ARITH:
        return "arith"
    return "move"


def dump_of(unit, sym):
    d = os.path.dirname(unit.get("artifact", ""))
    p = os.path.join(d, f"{unit['unit']}.clif", f"{sym}.unopt.clif")
    return p if os.path.exists(p) else None


def records(report):
    for u in report["units"]:
        for f in u["functions"]:
            yield u, f


def ident(u, f):
    return (u["package"], u["crate_name"], f["symbol"]), (u["package"], u["crate_name"],
                                                          f.get("instance", ""))


def analyse(report, show_list):
    t = report["totals"]
    print(f"totals: functions {t['functions']}, verified {t['verified']}, unverified "
          f"{t['unverified']}, fallback {t['fallback']}  (mode {report.get('mode')}, profile "
          f"{report.get('profile')})")
    fbs = [(u, f) for u, f in records(report) if f["status"] == "fallback"]
    b = collections.Counter(bucket(u, f) for u, f in fbs)
    print("fallback buckets: " + ", ".join(f"{k} {b[k]}" for k in ("float", "simd", "budget",
                                                                    "other")))
    print("reasons of the float fallbacks (value numbers as vN):")
    reasons = collections.Counter(norm(f.get("reason")) for u, f in fbs if bucket(u, f) == "float")
    for r, n in reasons.most_common():
        print(f"  {n:5d}  {r}")
    cls = collections.Counter()
    sub = collections.Counter()
    perop = collections.Counter()
    pkg = collections.Counter()
    missing = 0
    rows = []
    for u, f in fbs:
        if bucket(u, f) != "float":
            continue
        pkg[u["package"]] += 1
        s = float_scan(u, f)
        if s is None:
            missing += 1
            rows.append((u["package"], f["symbol"], "no dump", ""))
            continue
        ops, flags = s
        c = classify(ops, flags)
        cls[c] += 1
        for o in ops:
            perop[o] += 1
        if c == "move":
            if flags & {"sig", "callee_sig"}:
                sub["float parameters/returns of the function or of a callee"] += 1
            names = {o.split(".")[0].split(" ")[0] for o in ops}
            if not flags & {"sig", "callee_sig", "block_param"} and names <= {"load", "store"}:
                sub["only float load/store"] += 1
            if not flags & {"sig", "callee_sig", "block_param"} and names <= {"f32const", "f64const"}:
                sub["only float constants"] += 1
        rows.append((u["package"], f["symbol"], c, " ".join(sorted(flags) + sorted(ops))))
    n = sum(cls.values())
    print(f"float fallbacks: {n + missing} (dumps found {n}, missing {missing}): data movement "
          f"only {cls['move']}, with float arithmetic {cls['arith']}")
    for k, v in sub.items():
        print(f"  movement-only, {k}: {v}")
    print("per operation (functions using it, among the float fallbacks):")
    for o, v in sorted(perop.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"  {v:5d}  {o}")
    print("per package: " + ", ".join(f"{k} {v}" for k, v in pkg.most_common()))
    if show_list:
        for r in sorted(rows):
            print("  " + "\t".join(r))
    return fbs


def compare(before, after):
    def index(rep):
        a, b = {}, {}
        for u, f in records(rep):
            k1, k2 = ident(u, f)
            a[k1] = (u, f)
            b.setdefault(k2, (u, f))
        return a, b
    a1, a2 = index(after)
    trans = collections.Counter()
    float_trans = collections.Counter()
    unmatched = 0
    for u, f in records(before):
        k1, k2 = ident(u, f)
        hit = a1.get(k1) or a2.get(k2)
        if not hit:
            unmatched += 1
            continue
        s0, s1 = f["status"], hit[1]["status"]
        if s0 != s1:
            trans[f"{s0} -> {s1}"] += 1
        if s0 == "fallback" and bucket(u, f) == "float":
            float_trans[s1 if s1 != "fallback" else
                        f"fallback ({bucket(*hit)})"] += 1
    print(f"before -> after, by function identity (unmatched in after: {unmatched}):")
    for k, v in trans.most_common():
        print(f"  {v:5d}  {k}")
    print("float fallbacks of before, now: " + ", ".join(f"{k} {v}" for k, v in
                                                         float_trans.most_common()))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("report")
    ap.add_argument("--before")
    ap.add_argument("--list", action="store_true")
    a = ap.parse_args()
    after = json.load(open(a.report))
    if a.before:
        before = json.load(open(a.before))
        print(f"== before: {a.before}")
        analyse(before, a.list)
        print(f"== after: {a.report}")
    analyse(after, a.list)
    if a.before:
        compare(before, after)


if __name__ == "__main__":
    sys.exit(main())
