#!/usr/bin/env python3
"""Measured replay of one edit on a built tree, restricted to the lean-backend closure.

usage: replay.py VARIANT TREE CACHE LABEL EDIT
  VARIANT  base | port   (port: the tree's files are the branch's ported files)
  TREE     a worktree whose sources are main (22f3190) in that variant, built (or restorable
           from CACHE) for the lean-backend closure
  EDIT     a commit C whose touched files are unchanged between C and main: the tree is first
           put in the state "main without C" (touched files at C^; for port, C^ ported and
           merged with the branch's fix-ups for that file, as state.py does), built with the
           cache (unmeasured), then the files are put back to main and the closure is rebuilt
           WITHOUT the cache (measured: wall time, modules built);
           or syn:MODULE:proof|doc  a synthetic edit on main: proof = one extra `skip` step in
           the module's first tactic proof, doc = one more comment line at the top of the file.
Writes /home/user/ms/runs/LABEL/{result.json,prep.log,meas.log}.
"""
import importlib.util, json, os, pathlib, re, subprocess, sys, time

variant, tree, cache, label, edit = sys.argv[1:6]
tree = pathlib.Path(tree)
MS = pathlib.Path("/home/user/ms")
REPO = pathlib.Path("/home/user/workspace/repo")
MAIN = "22f3190"
BRANCH = os.environ.get("BRANCH", "parithosh/module-system")
out = MS / "runs" / label
out.mkdir(parents=True, exist_ok=True)
LB = sorted(set((MS / "lbmods.txt").read_text().split()))


def git(*a, cwd=REPO):
    return subprocess.run(["git", "-C", str(cwd), *a], capture_output=True, check=True).stdout.decode()


spec = importlib.util.spec_from_file_location("mp", REPO / "scripts/module-port.py")
mp = importlib.util.module_from_spec(spec); spec.loader.exec_module(mp)


def show(rev, p):
    r = subprocess.run(["git", "-C", str(REPO), "show", f"{rev}:{p}"], capture_output=True)
    return r.stdout.decode() if r.returncode == 0 else None


def ported(rev, p):
    """File p at rev, in the variant's form (None if absent)."""
    t = show(rev, p)
    if t is None or variant == "base":
        return t
    theirs, base, ours = mp.port(t), mp.port(show(MAIN, p) or ""), show(BRANCH, p)
    if ours is None or theirs == base:
        return ours if ours is not None and theirs == base else theirs
    import tempfile
    with tempfile.TemporaryDirectory() as d:
        for n, s in (("t", theirs), ("b", base), ("o", ours)):
            pathlib.Path(d, n).write_text(s)
        r = subprocess.run(["git", "merge-file", "-p", f"{d}/o", f"{d}/b", f"{d}/t"],
                           capture_output=True, text=True)
    if r.returncode:
        raise SystemExit(f"merge conflict in {p}")
    return r.stdout


def put(p, text):
    f = tree / p
    if text is None:
        f.unlink(missing_ok=True)
    else:
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(text)


def build(log, use_cache):
    env = dict(os.environ)
    for k in ("FV_LAKE_CACHE", "LAKE_CACHE_DIR", "LAKE_ARTIFACT_CACHE", "LAKE_RESTORE_ARTIFACTS"):
        env.pop(k, None)
    if use_cache:
        env["FV_LAKE_CACHE"] = cache
    mem = open(out / (log + ".mem"), "w")
    mp_ = subprocess.Popen(["bash", "-c", "while true; do echo $(date +%s) $(awk '/MemTotal|MemAvailable/{printf \"%s \", $2}' /proc/meminfo); sleep 2; done"], stdout=mem)
    t0 = time.time()
    rc = subprocess.run(
        ["python3", "scripts/lake-serial-build.py", "--out", str(out / (log + "-sched")),
         "--record", str(out / "peaks.tsv"), "--profile", str(MS / "profile-ci.tsv"),
         "--profile", "scripts/lake-module-peaks.tsv", "--budget", "26G", "--max-jobs", "8",
         "--heavy", "12G", "--heavy-avail", "20G", "--pause-avail", "3G", "--margin", "1.0",
         "--min-cap", "2G", "--max-cap", "28G", "--retry-failed", "--no-dedup",
         "FVTest.Backend.Main"],
        cwd=tree, env=env, stdout=open(out / (log + ".log"), "w"), stderr=subprocess.STDOUT).returncode
    wall = time.time() - t0
    mp_.kill()
    txt = (out / (log + ".log")).read_text()
    built = re.findall(r"done (\S+) rc=0 (\d+)s maxrss=\S+ cgpeak=([\d.]+)G built -> ok", txt)
    failed = sorted(set(re.findall(r"done (\S+) rc=[1-9]\d* .*-> fail", txt)))
    return dict(rc=rc, wall_s=round(wall, 1), built=len(built),
                module_s=sum(int(b[1]) for b in built),
                max_module_peak_g=max([float(b[2]) for b in built], default=0),
                failed=failed, modules=sorted(b[0] for b in built))


res = dict(variant=variant, edit=edit, tree=str(tree))
# The tree is built at main (restorable from CACHE). The edit is applied on top (a commit C is
# applied in reverse: its files are put back to C^, i.e. the same files change as in C), the
# lean-backend closure is rebuilt WITHOUT the cache (measured), then the files are restored and
# main's outputs are relinked from the cache (unmeasured).
res["pre"] = build("pre", True)
if edit.startswith("syn:"):
    _, mod, kind = edit.split(":")
    files = [mod.replace(".", "/") + ".lean"]
    orig = {files[0]: (tree / files[0]).read_text()}
    src = orig[files[0]]
    if kind == "proof":
        m = re.search(r"^(?:@\[[^\n]*\]\s*)?(?:private )?theorem [^\n]*(?:\n(?!theorem|def|lemma|@\[)[^\n]*)*?:= by\n(\s+)", src, re.M)
        i = m.end()
        new = src[:i] + "skip\n" + m.group(1) + src[i:]
    elif kind == "body":
        # an extra `id` around the body of the first non-exposed plain def with a `:=` body
        m = re.search(r"^(?!.*@\[[^\]]*expose)(?:[^\n]*\s)?def [^\n]*:=\s*\n?(\s*)", src, re.M)
        i = m.end()
        j = src.index("\n", i)
        new = src[:i] + "id (" + src[i:j] + ")" + src[j:]
    else:
        new = "-- (synthetic edit)\n" + src
        i = 0
    res["diff"] = new[max(0, i - 200):i + 80]
    (tree / files[0]).write_text(new)
else:
    c = edit
    files = [l for l in git("diff", "--name-only", f"{c}^", c, "--", "FV", "FVTest", "corpus/dsl").split("\n") if l]
    orig = {p: (tree / p).read_text() if (tree / p).exists() else None for p in files}
    for p in files:
        old = ported(f"{c}^", p)
        if old is not None:          # files C added stay (their importers need them)
            put(p, old)
res["files"] = files
try:
    res["meas"] = build("meas", False)
finally:
    for p, v in orig.items():
        put(p, v)
res["post"] = build("post", True)
(out / "result.json").write_text(json.dumps(res, indent=1))
print(label, json.dumps({k: ({kk: vv for kk, vv in v.items() if kk != "modules"} if isinstance(v, dict) else v)
                         for k, v in res.items() if k not in ("files", "diff")}))
