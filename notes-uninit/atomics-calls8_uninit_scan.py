#!/usr/bin/env python3
"""Static scan of cg_clif CLIF dumps for reads of uninitialised explicit stack-slot
bytes (issue #473, eth-act/clifv).

Per function: forward must-initialised dataflow over the CFG on the bytes of each
explicit slot.  Slot-derived values (stack_addr results, iadd chains with iconst)
are tracked SSA-globally.  Loads from slot-derived addresses touching a byte that
is not must-initialised are findings.  Escaped slots (slot-derived value used as
anything but a load/store address or iadd base) are exempt from findings and
counted separately.
"""
import json, os, re, sys, time
from collections import defaultdict

ROOT = "/home/kev/work/fv-compiler-rust"
GROUPS = {
    "fv-demo": os.path.join(ROOT, "examples/fv-demo/target/fv"),
    "survey":  os.path.join(ROOT, "examples/survey/target/fv"),
    "deps":    os.path.join(ROOT, "examples/deps/target/fv"),
}
OUT_PATH = "/tmp/atomics-calls8_uninit_result.json"
MAX_FINDINGS_LIST = 5000

FUNC_RE = re.compile(r"^function %(\S+?)\(")
SLOT_RE = re.compile(r"^\s*(ss\d+)\s*=\s*(explicit_slot|sized_stack_slot|explicit_dynamic_slot|dynamic_stack_slot)\s*(\d+)")
BLOCK_RE = re.compile(r"^\s*block(\d+)?\s*(?:\(([^)]*)\))?\s*(cold)?:")
ALIAS_RE = re.compile(r"^\s*v(\d+)\s*->\s*v(\d+)\s*(?:;.*)?$")
INS_RE = re.compile(r"^\s*(?:(v\d+(?:\s*,\s*v\d+)*)\s*=\s*)?([a-z_][a-z_0-9]*)((?:\.[a-z0-9_]+)?)\s*([^;]*?)\s*(?:;\s*(.*))?\s*$")
FNDECL_RE = re.compile(r"^\s*(fn\d+|sig\d+)\s*=\s*(.*)$")
VALTOK_RE = re.compile(r"v(\d+)(?:([+-])(0x[0-9a-fA-F]+|\d+))?")
BLOCKREF_RE = re.compile(r"block(\d+)")
PARAM_RE = re.compile(r"v(\d+)\s*:\s*([a-z0-9_x]+)")
CONST_RE = re.compile(r"v(\d+)\s*=\s*(-?\d+)")

SCALAR = {"i8":1,"i16":2,"i32":4,"i64":8,"i128":16,"f16":2,"f32":4,"f64":8,"f128":16,"r64":8,"r128":16}
LOAD_OPS = {"load", "uload", "sload"}
STORE_OPS = {"store"}
TERMINATORS = {"jump", "brif", "br_table", "try_call"}

def type_size(ty):
    if not ty: return None
    ty = ty.strip()
    if ty in SCALAR: return SCALAR[ty]
    if re.fullmatch(r"[a-z0-9]+x\d+", ty):  # cranelift vector types are 128-bit
        return 16
    return None

def parse_ops(operands):
    """Extract (vN, offset) tokens from an operand string (finditer-based so
    call-argument lists like fn0(v2, v3) are captured)."""
    out = []
    for m in VALTOK_RE.finditer(operands):
        off = 0
        if m.group(2):
            off = int(m.group(3), 0) * (1 if m.group(2) == "+" else -1)
        out.append((int(m.group(1)), off))
    return out

def parse_function(lines, start, end):
    """Parse one function section (lines[start:end])."""
    name = None
    slots = {}
    tys = {}   # fnN/sigN -> list of return types
    blocks = []
    cur = None
    for i in range(start, end):
        line = lines[i]
        if name is None:
            m = FUNC_RE.match(line)
            if m:
                name = m.group(1)
            continue
        m = SLOT_RE.match(line)
        if m:
            slots[m.group(1)] = int(m.group(3))
            continue
        m = FNDECL_RE.match(line)
        if m and cur is None:
            m2 = re.search(r"->\s*([a-z0-9_]+(?:\s+(?:uext|sext))?(?:\s*,\s*[a-z0-9_]+(?:\s+(?:uext|sext))?)*)", m.group(2))
            if m2:
                tys[m.group(1)] = [t.split()[0] for t in m2.group(1).split(",")]
            continue
        m = BLOCK_RE.match(line)
        if m:
            label = int(m.group(1)) if m.group(1) else len(blocks)
            params = {int(a): t.strip() for a, t in PARAM_RE.findall(m.group(2) or "")}
            cur = {"label": label, "params": params, "instrs": []}
            blocks.append(cur)
            continue
        if cur is None:
            continue
        m = ALIAS_RE.match(line)
        if m:
            cur["instrs"].append({"kind": "alias", "va": int(m.group(1)),
                                  "vb": int(m.group(2)), "line": i})
            continue
        m = INS_RE.match(line)
        if m:
            reslist = ([int(x) for x in re.findall(r"v(\d+)", m.group(1))]
                       if m.group(1) else [])
            cur["instrs"].append({
                "kind": "ins", "res": reslist,
                "op": m.group(2), "ty": (m.group(3)[1:] if m.group(3) else None),
                "ops": m.group(4) or "", "comment": m.group(5), "line": i})
            continue
    return {"name": name, "slots": slots, "blocks": blocks, "tys": tys}

def analyze(fn, path_lines, base_dir_len):
    """Dataflow over one function. Returns (escaped_slots_sorted, findings)."""
    slots = {s: sz for s, sz in fn["slots"].items() if s.startswith("ss") and sz > 0}
    if not slots:
        return [], [], 0
    blocks = fn["blocks"]
    if not blocks:
        return [], [], 0

    # ---- successors / predecessors ----
    succs = {}
    for b in blocks:
        ss = []
        for ins in b["instrs"]:
            if ins["kind"] == "ins" and ins["op"] in TERMINATORS:
                ss.extend(int(x) for x in BLOCKREF_RE.findall(ins["ops"]))
        succs[b["label"]] = sorted(set(ss))
    preds = defaultdict(list)
    for bl, ss in succs.items():
        for s in ss:
            preds[s].append(bl)
    block_by_label = {b["label"]: b for b in blocks}
    entry = blocks[0]["label"]

    # ---- value types ----
    vtype = {}
    for b in blocks:
        for v, t in b["params"].items():
            vtype.setdefault(v, t)
    for b in blocks:
        for ins in b["instrs"]:
            if ins["kind"] == "alias":
                if ins["vb"] in vtype:
                    vtype.setdefault(ins["va"], vtype[ins["vb"]])
                continue
            if ins["ty"]:
                for v in ins["res"]:
                    vtype.setdefault(v, ins["ty"])
            op, ops_txt = ins["op"], ins["ops"]
            if op in ("call", "return_call") and ins["res"]:
                m = re.search(r"\bfn(\d+)\b", ops_txt)
                tys = fn["tys"].get("fn" + m.group(1)) if m else None
                if tys:
                    for v, t in zip(ins["res"], tys):
                        vtype.setdefault(v, t)
            elif op in ("try_call", "return_call_indirect") and ins["res"]:
                m = re.search(r"\bsig(\d+)\b", ops_txt)
                tys = fn["tys"].get("sig" + m.group(1)) if m else None
                if tys:
                    for v, t in zip(ins["res"], tys):
                        vtype.setdefault(v, t)
            elif op == "call_indirect" and ins["res"]:
                m = re.search(r"\bsig(\d+)\b", ops_txt)
                tys = fn["tys"].get("sig" + m.group(1)) if m else None
                if tys:
                    for v, t in zip(ins["res"], tys):
                        vtype.setdefault(v, t)
    # inference: unsuffixed value ops take the (unique) type of their operands
    BOOL_OPS = {"icmp", "icmp_imm", "fcmp"}
    for _ in range(8):
        changed = False
        for b in blocks:
            for ins in b["instrs"]:
                if ins["kind"] != "ins" or ins["ty"] or not ins["res"]:
                    continue
                op, ops_txt = ins["op"], ins["ops"]
                if op in TERMINATORS or op in STORE_OPS:
                    continue
                if op in BOOL_OPS:
                    for v in ins["res"]:
                        if vtype.get(v) is None:
                            vtype[v] = "i8"
                            changed = True
                    continue
                ots = [vtype.get(v) for v, off in parse_ops(ops_txt)]
                ots = [t for t in ots if t]
                if op == "select" and len(ots) >= 2:
                    ots = ots[1:]  # drop the i8 condition
                uniq = set(ots)
                if len(uniq) == 1:
                    t = next(iter(uniq))
                    for v in ins["res"]:
                        if vtype.get(v) is None:
                            vtype[v] = t
                            changed = True
        if not changed:
            break

    # ---- pass 1: SSA slot-derived map + escapes ----
    # A) defs sweep (stack_addr / iconst / iadd chains), B) aliases (may point
    # forward to later defs -> fixpoint), C) block-param derived-ness from jump
    # args, D) escape sweep (any use of a slot-derived value outside a
    # load/store address or iadd base escapes the slot).
    derived = {}   # vN -> (slot_label, offset)
    escaped = set()
    iconst = {}    # vN -> int
    defs_op = {}   # vN -> defining opcode

    def add_esc(slot):
        escaped.add(slot)

    # A) defs
    for b in blocks:
        for ins in b["instrs"]:
            if ins["kind"] != "ins":
                continue
            op, ops_txt = ins["op"], ins["ops"]
            res = ins["res"][0] if len(ins["res"]) == 1 else None
            for v in ins["res"]:
                defs_op.setdefault(v, op)
            if op == "stack_addr":
                if res is not None:
                    m = re.search(r"(ss\d+)(?:([+-])(\d+))?", ops_txt)
                    if m and m.group(1) in fn["slots"]:
                        off = int(m.group(3)) if m.group(3) else 0
                        val = (m.group(1), off)
                        if res in derived and derived[res] != val:
                            del derived[res]
                        else:
                            derived[res] = val
                continue
            if op == "iconst" and res is not None:
                m = re.search(r"(-?(?:0x[0-9a-fA-F]+|\d+))\s*$", ops_txt)
                if m:
                    s = m.group(1)
                    iconst[res] = int(s, 16) if s.lower().startswith(("0x", "-0x")) else int(s)
                continue
            if ins["comment"]:
                for mm in CONST_RE.finditer(ins["comment"]):
                    iconst.setdefault(int(mm.group(1)), int(mm.group(2)))
            if op in ("iadd", "iadd_imm") and res is not None:
                if op == "iadd_imm":
                    vals = parse_ops(ops_txt)
                    m = re.search(r"(-?\d+)\s*$", ops_txt)
                    imm = int(m.group(1)) if m else None
                    if vals:
                        v = vals[0][0]
                        if v in derived and imm is not None:
                            derived[res] = (derived[v][0], derived[v][1] + imm)
                        elif v in derived:
                            add_esc(derived[v][0])
                else:
                    vals = parse_ops(ops_txt)
                    dsrc, cval, bad = None, None, False
                    for v, off in vals:
                        if v in derived:
                            if dsrc is None:
                                dsrc = v
                            else:
                                bad = True
                        elif v in iconst:
                            if cval is None:
                                cval = iconst[v]
                            else:
                                cval, bad = None, True
                        else:
                            bad = True
                    if dsrc is not None and cval is not None and not bad:
                        derived[res] = (derived[dsrc][0], derived[dsrc][1] + cval)
                    elif dsrc is not None:
                        add_esc(derived[dsrc][0])
                continue

    # B) aliases (vA -> vB means vA gets vB's value); iterate to fixpoint since
    # the right side may be defined later or be a block param
    for _ in range(20):
        changed = False
        for b in blocks:
            for ins in b["instrs"]:
                if ins["kind"] != "alias":
                    continue
                va, vb = ins["va"], ins["vb"]
                old = derived.get(va)
                if vb in derived:
                    nv = derived[vb]
                    if va in derived and derived[va] != nv:
                        if va in derived:
                            del derived[va]
                            changed = True
                    else:
                        if old != nv:
                            derived[va] = nv
                            changed = True
                elif va in derived and old is not None:
                    del derived[va]
                    changed = True
        if not changed:
            break

    # C) block params: derived iff every incoming edge passes the same
    # slot-derived value at that parameter position
    BLOCKARG_RE = re.compile(r"block(\d+)\s*\(([^)]*)\)")
    edge_args = []  # (succ_label, [ (v,off) ... ])
    for b in blocks:
        for ins in b["instrs"]:
            if ins["kind"] == "ins" and ins["op"] == "jump":
                for m in BLOCKARG_RE.finditer(ins["ops"]):
                    edge_args.append((int(m.group(1)), parse_ops(m.group(2))))
    cand = {}  # (label, param_index) -> value or None
    for lbl, args in edge_args:
        blk = block_by_label.get(lbl)
        if not blk:
            continue
        plist = list(blk["params"])
        for i, (v, off) in enumerate(args):
            if i >= len(plist):
                break
            key = (lbl, i)
            dv = derived.get(v)
            if key in cand and cand[key] != dv:
                cand[key] = None
            else:
                cand[key] = dv
    for (lbl, i), dv in cand.items():
        if dv is not None:
            derived[list(block_by_label[lbl]["params"])[i]] = dv

    # D) escape sweep
    for b in blocks:
        for ins in b["instrs"]:
            if ins["kind"] != "ins":
                continue
            op, ops_txt = ins["op"], ins["ops"]
            if op == "stack_addr" or op == "iconst":
                continue
            if op in ("iadd", "iadd_imm"):
                continue  # handled in sweep A
            if op in LOAD_OPS:
                continue  # reading through the pointer is the point of the scan
            vals = parse_ops(ops_txt)
            if op in STORE_OPS:
                if len(vals) >= 2:
                    d = derived.get(vals[-2][0])
                    if d:
                        add_esc(d[0])
                continue
            if op == "jump":
                # successor args are internal SSA flow, not escapes
                masked = BLOCKARG_RE.sub(" ", ops_txt)
                for v, off in parse_ops(masked):
                    d = derived.get(v)
                    if d:
                        add_esc(d[0])
                continue
            # generic: any use of a slot-derived value is an escape
            for v, off in vals:
                d = derived.get(v)
                if d:
                    add_esc(d[0])

    # ---- dataflow state helpers ----
    # ---- static per-slot store metadata (for classification) ----
    slot_sizes = slots  # label -> size
    untyped_store = set()      # slots with a store of unknown size
    static_cov = {s: set() for s in slot_sizes}
    srcload = {s: False for s in slot_sizes}
    for b in blocks:
        for ins in b["instrs"]:
            if ins["kind"] != "ins" or ins["op"] not in STORE_OPS:
                continue
            vals = parse_ops(ins["ops"])
            if len(vals) < 2:
                continue
            d = derived.get(vals[-1][0])
            if not d or d[0] not in static_cov:
                continue
            slotl, soff = d
            base = soff + vals[-1][1]
            tsz = type_size(ins["ty"]) or type_size(vtype.get(vals[-2][0]))
            if tsz is None:
                untyped_store.add(slotl)
            else:
                static_cov[slotl] |= set(range(base, base + tsz))
                vv = vals[-2][0]
                if defs_op.get(vv) in LOAD_OPS:
                    srcload[slotl] = True

    # ---- dataflow state helpers ----
    slot_sizes = slots  # label -> size

    def top_state():
        return {s: set(range(sz)) for s, sz in slot_sizes.items()}

    def copy_state(st):
        return {s: set(st.get(s, ())) for s in slot_sizes}

    def intersect(a, b):
        return {s: (a[s] & b[s]) if (s in a and s in b) else set()
                for s in slot_sizes}

    def transfer(b, instate, record, findings, file_lines):
        st = copy_state(instate)
        for ins in b["instrs"]:
            if ins["kind"] == "alias":
                continue
            op, ty, ops_txt = ins["op"], ins["ty"], ins["ops"]
            res = ins["res"][0] if len(ins["res"]) == 1 else None
            if op in ("iconst", "iadd", "iadd_imm", "stack_addr"):
                continue
            vals = parse_ops(ops_txt)
            if op in LOAD_OPS:
                if vals:
                    v, aoff = vals[-1]
                    d = derived.get(v)
                    if d and d[0] in st and d[0] not in escaped:
                        slot, soff = d
                        base = soff + aoff
                        tsz = type_size(ty)
                        if tsz is None:
                            continue
                        missing = [x for x in range(base, base + tsz) if x not in st[slot]]
                        if missing and record:
                            findings.append({
                                "file": None, "function": fn["name"], "slot": slot,
                                "offset": base, "size": tsz, "missing": len(missing),
                                "untyped_store": slot in untyped_store,
                                "outside_static": bool(set(range(base, base + tsz)) - static_cov[slot]),
                                "copy": srcload.get(slot, False),
                                "line": path_lines[ins["line"]].strip(),
                                "context": [path_lines[j].rstrip("\n")
                                            for j in range(max(0, ins["line"] - 5), ins["line"])],
                            })
                continue
            if op in STORE_OPS:
                if len(vals) >= 2:
                    vaddr = vals[-1]
                    d = derived.get(vaddr[0])
                    if d and d[0] in st and d[0] not in escaped:
                        slot, soff = d
                        base = soff + vaddr[1]
                        tsz = type_size(ty)
                        if tsz is None:
                            # resolve from the stored value's type
                            vv = vals[-2][0]
                            tsz = type_size(vtype.get(vv))
                        if tsz is None:
                            continue
                        st[slot] |= set(range(base, base + tsz))
                continue
            # any other op: nothing changes byte state
        return st

    # ---- fixpoint ----
    top = top_state()
    IN = {bl: ({} if bl == entry else copy_state(top)) for bl in succs}
    OUT = {}
    for _ in range(200):
        changed = False
        for b in blocks:
            bl = b["label"]
            if bl == entry:
                inst = {}
            else:
                ps = preds.get(bl)
                if not ps:
                    inst = copy_state(top)  # unreachable block: assume init
                else:
                    ps2 = [p for p in ps if p in OUT]
                    if not ps2:
                        inst = copy_state(top)
                    else:
                        inst = OUT[ps2[0]]
                        for p in ps2[1:]:
                            inst = intersect(inst, OUT[p])
            IN[bl] = inst
            out = transfer(b, inst, False, None, None)
            if bl not in OUT or out != OUT[bl]:
                changed = True
            OUT[bl] = out
        if not changed:
            break

    # ---- final pass: record findings with fixed in-states ----
    findings = []
    for b in blocks:
        transfer(b, IN[b["label"]], True, findings, path_lines)
    return sorted(escaped), findings, len(escaped)

def collect(group, gdir):
    files = []
    for dirpath, dirnames, filenames in os.walk(gdir):
        if os.path.basename(dirpath) == "fns":
            files += [os.path.join(dirpath, f) for f in filenames if f.endswith(".clif")]
    files.sort()
    return files

def main():
    t0 = time.time()
    result = {}
    for group, gdir in GROUPS.items():
        stats = {"functions_scanned": 0, "functions_with_slots": 0,
                 "escaped_slot_count": 0, "findings_count": 0}
        findings = []
        escaped_total = 0
        files = collect(group, gdir) if os.path.isdir(gdir) else []
        for path in files:
            try:
                with open(path, encoding="utf-8", errors="replace") as f:
                    text = f.read()
            except OSError:
                continue
            if "stack_addr" not in text and "explicit_slot" not in text:
                # still counts as scanned only if it has a function
                if "function %" in text:
                    stats["functions_scanned"] += 1
                continue
            lines = text.splitlines(keepends=True)
            # find function sections
            starts = [i for i, l in enumerate(lines) if FUNC_RE.match(l)]
            if not starts:
                continue
            for si, s in enumerate(starts):
                e = starts[si + 1] if si + 1 < len(starts) else len(lines)
                fn = parse_function(lines, s, e)
                if not fn["name"]:
                    continue
                stats["functions_scanned"] += 1
                if not fn["slots"]:
                    continue
                stats["functions_with_slots"] += 1
                esc, fnd, nesc = analyze(fn, lines, 0)
                escaped_total += nesc
                for fd in fnd:
                    fd["file"] = os.path.relpath(path, ROOT)
                findings.extend(fnd)
        stats["escaped_slot_count"] = escaped_total
        stats["findings_count"] = len(findings)
        result[group] = {"stats": stats,
                         "findings": findings[:MAX_FINDINGS_LIST],
                         "findings_truncated": len(findings) > MAX_FINDINGS_LIST}
        print(f"[{group}] scanned={stats['functions_scanned']} "
              f"with_slots={stats['functions_with_slots']} "
              f"escaped={stats['escaped_slot_count']} "
              f"findings={stats['findings_count']} "
              f"({time.time()-t0:.1f}s elapsed)", file=sys.stderr)
    with open(OUT_PATH, "w") as f:
        json.dump(result, f, indent=2)
    print(f"done in {time.time()-t0:.1f}s -> {OUT_PATH}", file=sys.stderr)

if __name__ == "__main__":
    main()
