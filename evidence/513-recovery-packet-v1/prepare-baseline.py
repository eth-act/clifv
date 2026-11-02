"""Snapshot baseline imports without running Lean."""
from pathlib import Path
import fcntl, hashlib, json, os, subprocess

OUT = Path(__file__).resolve().parent
PKG = OUT/'focused-package-v1'
FROZEN = Path('/home/lee/clifv/.worktrees/stock-extending-production-20261031')
context = json.loads((OUT/'focused-context-v1.json').read_text())
ownership = json.loads((OUT/'focused-ownership-v1.json').read_text())
base = context['base']
lines = subprocess.check_output(['git','grep','-n','-E','^import ',base,'--','*.lean'],cwd=FROZEN,text=True).splitlines()
graph = {}
for line in lines:
    _, path, _, text = line.split(':',3)
    graph.setdefault(path,set()).update(m.replace('.','/')+'.lean' for m in text[7:].split('--')[0].split() if m.startswith(('FV.','FVTest.')))
todo = [p for p in context['focused_targets'] if not p.endswith(('/LowerOutcomes.lean','/LowerValueRelations.lean'))]
seen = set()
while todo:
    p = todo.pop()
    if p in seen:
        continue
    seen.add(p)
    todo += list(graph.get(p,set())-seen)
assert len(seen) == context['baseline_closure_count']
baseline = PKG/'.lake/baseline-lib'
assert not baseline.exists()
with (OUT.parent/'main870-cache-import.lock').open('a+') as lock:
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    for p in sorted(seen):
        stem = FROZEN/'.lake/build/lib/lean'/Path(p).with_suffix('')
        for suffix in ['.olean','.ilean','.olean.private','.olean.server']:
            source = Path(str(stem)+suffix)
            if not source.exists():
                assert suffix != '.olean', p
                continue
            target = Path(str(baseline/Path(p).with_suffix(''))+suffix)
            target.parent.mkdir(parents=True,exist_ok=True)
            digest = hashlib.sha256(source.read_bytes()).hexdigest()
            os.link(source,target)
            assert hashlib.sha256(target.read_bytes()).hexdigest() == digest
            ownership['hardlinked_imports'].append({'path':str(target.relative_to(PKG)),'source':str(source),'sha256':digest,'inode':target.stat().st_ino})
ownership['cleanup'] += ' Also remove focused-package-v1/.lake/baseline-lib; these are snapshot hardlinks, not an additional warm cache.'
(OUT/'focused-ownership-v1.json').write_text(json.dumps(ownership,indent=2)+'\n')
print(json.dumps({'baseline_modules':len(seen),'total_hardlinked_outputs':len(ownership['hardlinked_imports']),'no_builds':True}))
