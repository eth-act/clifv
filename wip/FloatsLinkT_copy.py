#!/usr/bin/env python3
"""Typed-copy generator (FloatsLinkT): copies the declarations of the link/exec chain that
depend on the integer link contract into *T modules, renaming them.  Throwaway tool."""
import re, os, sys, json, collections

root = '/home/kev/work/clifv-wt/floats-c8l'
deps_file = '/tmp/FloatsLinkT_deps.tsv'

MODS = [l.strip().strip('`,') for l in """
FV.E2E.LinkArm FV.E2E.LinkGood FV.E2E.LinkCheck FV.E2E.PipelineCheck FV.E2E.DeadCleanupLinkCheck
FV.E2E.StackBound FV.E2E.DeadCleanupStackBound FV.E2E.BinCheck FV.E2E.DeadCleanupBinCheck
FV.E2E.Binary FV.E2E.DeadCleanupBinary FV.E2E.BinaryGood FV.E2E.DeadCleanupBinaryGood
FV.E2E.ExecWords FV.E2E.ExecBytes FV.E2E.DeadCleanupExecBytes FV.E2E.CodeMap FV.E2E.ExecStatic
FV.E2E.DeadCleanupExecStatic FV.E2E.ExecFrameSim FV.E2E.DeadCleanupExecFrameSim FV.E2E.ExecRunN
FV.E2E.DeadCleanupExecRunN FV.E2E.ExecGoodRun FV.E2E.DeadCleanupExecGoodRun FV.E2E.ExecGoodReads
FV.E2E.DeadCleanupExecGoodReads FV.E2E.ExecGot FV.E2E.DeadCleanupExecGot FV.E2E.ExecProven
FV.E2E.DeadCleanupExecProven""".split()]

SEEDS = json.loads(sys.argv[1]) if len(sys.argv) > 1 else []
TARGETS = json.loads(sys.argv[2]) if len(sys.argv) > 2 else []

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*'
                  r'(theorem|def|lemma|abbrev|structure|inductive|class|instance|opaque|example)\b\s*(\S*)')


def parse(mod):
    path = f'{root}/{mod.replace(".", "/")}.lean'
    lines = open(path).read().split('\n')
    items = []
    i, n, pending = 0, len(lines), []
    ns = []  # stack of (kind, name)
    def curns():
        return '.'.join(x[1] for x in ns if x[0] == 'ns' and x[1])
    while i < n:
        l = lines[i]
        if l.startswith('/--'):
            j = i
            if '-/' not in l[3:]:
                j = i + 1
                while '-/' not in lines[j]:
                    j += 1
            pending += lines[i:j + 1]
            i = j + 1
            continue
        if l.startswith('/-'):
            j = i
            while '-/' not in lines[j]:
                j += 1
            items.append(('comment', None, lines[i:j + 1], curns()))
            i = j + 1
            continue
        m = DECL.match(l)
        if not m and (l.startswith('@[') or ((l.startswith('set_option') or l.startswith('open'))
                                             and l.rstrip().endswith(' in'))):
            pending.append(l)
            i += 1
            continue
        if m:
            j = i + 1
            while j < n:
                lj = lines[j]
                if lj and not lj[0].isspace() and not lj.startswith('--') and not lj.startswith('|') \
                        and not lj.startswith('where') and not lj.startswith('termination_by') \
                        and not lj.startswith('decreasing_by'):
                    break
                j += 1
            k = j
            while k > i + 1 and lines[k - 1].strip() == '':
                k -= 1
            name = m.group(2)
            if m.group(1) == 'instance':
                name = None
            full = None
            if name:
                full = name[len('_root_.'):] if name.startswith('_root_.') else \
                    ((curns() + '.' + name) if curns() else name)
            items.append(('decl', full, pending + lines[i:k], curns()))
            pending = []
            for b in lines[k:j]:
                items.append(('blank', None, [b], curns()))
            i = j
            continue
        if pending:
            items.append(('ctx', None, pending, curns()))
            pending = []
        s = l.strip()
        if s.startswith('namespace '):
            for part in s.split()[1].split('.'):
                ns.append(('ns', part))
        elif s.startswith('section') or s.startswith('noncomputable section'):
            nm = s.split()[-1] if len(s.split()) > (2 if s.startswith('noncomputable') else 1) else ''
            ns.append(('sec', nm))
        elif s.startswith('end'):
            parts = s.split()
            if len(parts) > 1:
                cnt = len(parts[1].split('.'))
                if ns and ns[-1][0] == 'sec' and ns[-1][1] == parts[1]:
                    ns.pop()
                else:
                    for _ in range(cnt):
                        if ns:
                            ns.pop()
            else:
                if ns:
                    ns.pop()
        items.append(('ctx' if s else 'blank', None, [l], curns()))
        i += 1
    return items


def norm(c):
    c = re.sub(r'^_private\.[A-Za-z0-9_.]*?\.0\.', '', c)
    return c


def main():
    uses = {}
    modof = {}
    for line in open(deps_file):
        parts = line.rstrip('\n').split('\t')
        if len(parts) < 2:
            continue
        c = norm(parts[0])
        modof[c] = parts[1]
        uses[c] = set(norm(u) for u in (parts[2].split() if len(parts) > 2 else []))
    P = {m: parse(m) for m in MODS}
    srcdecls = {}
    for m in MODS:
        for kind, full, tx, nsn in P[m]:
            if kind == 'decl' and full:
                srcdecls[full] = (m, tx, nsn)

    def parent(c):
        parts = c.split('.')
        for k in range(len(parts), 0, -1):
            p = '.'.join(parts[:k])
            if p in srcdecls:
                return p
        return None
    # aggregate uses per source decl (aux constants folded into parents)
    duses = collections.defaultdict(set)
    for c, us in uses.items():
        p = parent(c)
        if p is None:
            continue
        for u in us:
            pu = parent(u)
            duses[p].add(pu if pu else u)
    # taint
    taint = set(SEEDS)
    changed = True
    while changed:
        changed = False
        for d in srcdecls:
            if d in taint:
                continue
            if duses[d] & taint:
                taint.add(d)
                changed = True
    # need
    need = set()
    st = list(TARGETS)
    while st:
        d = st.pop()
        if d in need or d not in srcdecls:
            continue
        need.add(d)
        st.extend(x for x in duses[d] if x in srcdecls)
    copy = sorted(need & taint)
    json.dump({'copy': copy, 'uses': {d: sorted(duses[d] & set(copy)) for d in copy}},
              open('/tmp/FloatsLinkT_copyset.json', 'w'), indent=1)
    tot = collections.Counter()
    for d in copy:
        tot[srcdecls[d][0]] += len(srcdecls[d][1])
    for m in MODS:
        if tot[m]:
            print(m, tot[m])
    print('TOTAL', sum(tot.values()), len(copy))


if __name__ == '__main__':
    main()


IDENT = re.compile(r"(\.?)((?:[A-Za-z_\u0370-\u03ff\u1f00-\u1fff][A-Za-z0-9_'!?\u0370-\u03ff\u1f00-\u1fff\u2080-\u2089]*)"
                   r"(?:\.[A-Za-z_\u0370-\u03ff][A-Za-z0-9_'!?\u0370-\u03ff\u2080-\u2089]*)*)")


def newname(full):
    parts = full.split('.')
    if 'Ok' in parts[:-1] and parts[parts.index('Ok') - 1] == 'LinkSys':
        i = parts.index('Ok')
        parts[i] = 'OkT'
        return '.'.join(parts)
    parts[-1] = parts[-1] + 'T'
    return '.'.join(parts)


def emit(copy, srcdecls, P, extra_imports, privates):
    cset = set(copy)
    # short name -> list of full copied names that get a last-component rename
    short = collections.defaultdict(list)
    for c in copy:
        nn = newname(c)
        if nn.split('.')[-1] != c.split('.')[-1]:
            short[c.split('.')[-1]].append(c)
    nsset = set()
    for c in copy:
        ps = c.split('.')
        for k in range(1, len(ps)):
            nsset.add(ps[k - 1])

    def is_var(comp):
        return len(comp) <= 2 or comp[0].islower() or comp[0] in 'αβγδκρσφψωΓΔ'

    def rename_token(pre, tok):
        comps = tok.split('.')
        out = []
        for j, c in enumerate(comps):
            if c in short:
                if j == 0 and pre == '':
                    out.append(c + 'T'); continue
                prefix = comps[:j]
                if pre == '.' and j == 0:
                    out.append(c + 'T'); continue
                if prefix and is_var(prefix[-1]) and not prefix[-1] in nsset:
                    out.append(c + 'T'); continue
                ok = False
                for full in short[c]:
                    fns = full.split('.')[:-1]
                    if fns[-len(prefix):] == prefix:
                        ok = True
                if ok:
                    out.append(c + 'T'); continue
            out.append(c)
        return pre + '.'.join(out)

    def rename_text(txt):
        res = []
        for line in txt:
            # protect strings and comments after --
            code, sep, com = line.partition('--') if '"' not in line else (line, '', '')
            segs = re.split(r'("(?:[^"\\]|\\.)*")', code)
            for k in range(0, len(segs), 2):
                segs[k] = IDENT.sub(lambda m: rename_token(m.group(1), m.group(2)), segs[k])
            res.append(''.join(segs) + sep + com)
        return res

    files = {}
    for m in MODS:
        mine = [c for c in copy if srcdecls[c][0] == m]
        privs = [c for c in privates if srcdecls[c][0] == m]
        if not mine and not privs:
            continue
        out = []
        for kind, full, tx, nsn in P[m]:
            if kind == 'ctx':
                s = tx[0].strip()
                if s.startswith('import') or s.startswith('attribute') or s.startswith('deriving'):
                    continue
                out += tx
            elif kind == 'decl' and full in cset:
                out.append('')
                out += rename_text(tx)
            elif kind == 'decl' and full in privates:
                out.append('')
                out += tx
        files[m] = out
    return files


def main2(extra):
    uses = {}
    for line in open(deps_file):
        parts = line.rstrip('\n').split('\t')
        if len(parts) < 2:
            continue
        uses[norm(parts[0])] = set(norm(u) for u in (parts[2].split() if len(parts) > 2 else []))
    P = {m: parse(m) for m in MODS}
    srcdecls = {}
    private = set()
    for m in MODS:
        for kind, full, tx, nsn in P[m]:
            if kind == 'decl' and full:
                srcdecls[full] = (m, tx, nsn)
                if any(re.match(r'^(?:@\[[^\]]*\]\s*)?(?:\w+\s+)*private\s', l) for l in tx if DECL.match(l)):
                    private.add(full)
    d = json.load(open('/tmp/FloatsLinkT_copyset.json'))
    copy = d['copy']
    # private decls used by copies (transitively), not themselves copied
    def parent(c):
        parts = c.split('.')
        for k in range(len(parts), 0, -1):
            p = '.'.join(parts[:k])
            if p in srcdecls:
                return p
        return None
    duses = collections.defaultdict(set)
    for c, us in uses.items():
        p = parent(c)
        if p is None:
            continue
        for u in us:
            pu = parent(u)
            if pu:
                duses[p].add(pu)
    privs = set()
    st = list(copy)
    seen = set()
    while st:
        c = st.pop()
        if c in seen:
            continue
        seen.add(c)
        for u in duses[c]:
            if u in private and u not in copy:
                privs.add(u)
                st.append(u)
    files = emit(copy, srcdecls, P, {}, privs)
    for m, out in files.items():
        src = open(f'{root}/{m.replace(".", "/")}.lean').read().split('\n')
        imps = [l.split()[1] for l in src if l.startswith('import ')]
        timps = [m] + [i + 'T' for i in imps if i in files] + extra.get(m, [])
        hdr = ['\n'.join('import ' + i for i in timps), '',
               f'/-! # Typed copies of `{m}` (S11e5 Stage C, slice 8)',
               '',
               f'The declarations of `{m}` that depend on the integer link contract',
               '(`LinkSys.Ok`, `LinkSys.Thm`, `okB`, `ArmRefines`), for the typed contract `LinkSys.OkT`',
               '(suffix `T`; `LinkSys.Ok.*` as `LinkSys.OkT.*`). -/', '']
        body = out
        # squeeze blank lines
        res = []
        for l in body:
            if l.strip() == '' and res and res[-1].strip() == '':
                continue
            res.append(l)
        path = f'{root}/{m.replace(".", "/")}T.lean'
        open(path, 'w').write('\n'.join(hdr + res).rstrip() + '\n')
        print('wrote', path, len(res))
    print('privates', sorted(privs))


if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'emit':
    pass
