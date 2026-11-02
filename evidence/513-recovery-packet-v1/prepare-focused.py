"""Prepare isolated kernel inputs. This script never starts Lean or a build."""
from pathlib import Path
import collections, fcntl, hashlib, json, os, re, subprocess

ROOT = Path('/home/lee/clifv')
OUT = Path(__file__).resolve().parent
FROZEN = ROOT/'.worktrees/stock-extending-production-20261031'
FROZEN_SHA = 'a4c0726d46c5908b4ac06cf797ee939af8644703'
record = json.loads((OUT/'recovery-receipt.json').read_text())
BASE, TREE = record['base'], record['candidate_tree']
PKG = OUT/'focused-package-v1'
assert not PKG.exists(), 'Preserve the existing package; use a new version'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def save(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2)+'\n')

assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=FROZEN,text=True).strip() == FROZEN_SHA
def blobs(tree):
    return {line.split('\t')[1]:line.split()[2] for line in git('ls-tree','-r',tree).decode().splitlines()}

def imports(tree):
    graph = collections.defaultdict(set)
    for line in git('grep','-n','-E','^import ',tree,'--','*.lean').decode().splitlines():
        _, path, _, text = line.split(':',3)
        graph[path].update(m.replace('.','/')+'.lean' for m in text[7:].split('--')[0].split() if m.startswith(('FV.','FVTest.')))
    return graph

seeds = ['FV/Backend/Proof/'+n+'.lean' for n in ['LowerOutcomes','LowerValueRelations','LowerSim','PrepareSound']]
seeds += ['FV/E2E/'+n+'.lean' for n in ['Statement','Main','ABIReadOnlyRealize']]
frozen, current, candidate = blobs(FROZEN_SHA), blobs(BASE), blobs(TREE)
graphs = {BASE:imports(BASE), TREE:imports(TREE)}

def closure(tree, initial):
    found, pending = set(), list(initial)
    while pending:
        p = pending.pop()
        if p in found:
            continue
        found.add(p)
        pending += list(graphs[tree].get(p,set())-found)
    return found

baseline_closure = closure(BASE,[p for p in seeds if p in current])
candidate_closure = closure(TREE,seeds)
assert all(current[p] == frozen.get(p) for p in baseline_closure), 'Baseline imports differ from the frozen source'
rebuild = {p for p in candidate_closure if candidate[p] != frozen.get(p)}
assert rebuild == set(seeds), ('Unexpected dependency overlay',rebuild-set(seeds))
queue, pending = [], set(rebuild)
while pending:
    ready = sorted(p for p in pending if not graphs[TREE].get(p,set()) & pending)
    assert ready, 'Dependency cycle'
    queue += ready
    pending -= set(ready)

PKG.mkdir()
(PKG/'lakefile.toml').write_text('name = "outcome513focused"\nversion = "0.1.0"\n\n[[lean_lib]]\nname = "FV"\n')
(PKG/'lean-toolchain').write_bytes(git('show',BASE+':lean-toolchain'))
assert (FROZEN/'lean-toolchain').read_bytes() == (PKG/'lean-toolchain').read_bytes()
# All candidate source is retained, but only the seven actual dependencies enter the focused build queue.
for p in record['source_sha256']:
    target = PKG/p
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_bytes((OUT/'source'/p).read_bytes())
for p in candidate_closure:
    target = PKG/p
    if not target.exists():
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(git('show',TREE+':'+p))

shared = FROZEN/'.lake/build/lib/lean'
local = PKG/'.lake/build/lib/lean'
linked = []
with (OUT.parent/'main870-cache-import.lock').open('a+') as lock:
    # A failed nonblocking acquisition requires a later preparation attempt, never a long hidden wait.
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    for p in sorted(candidate_closure-rebuild):
        assert candidate[p] == current[p] == frozen[p]
        stem = shared/Path(p).with_suffix('')
        assert stem.with_suffix('.olean').exists(), ('Missing frozen import output',p)
        for suffix in ['.olean','.ilean','.olean.private','.olean.server']:
            source = Path(str(stem)+suffix)
            if not source.exists():
                continue
            target = local/Path(p).with_suffix('')
            target = Path(str(target)+suffix)
            target.parent.mkdir(parents=True,exist_ok=True)
            digest = hashlib.sha256(source.read_bytes()).hexdigest()
            os.link(source,target)
            assert hashlib.sha256(target.read_bytes()).hexdigest() == digest
            linked.append({'path':str(target.relative_to(PKG)), 'source':str(source), 'sha256':digest,'inode':target.stat().st_ino})

roots = ['VTrapFrom','VRetFrom','VTrapFrom.prefix','VRetFrom.prefix','ArgsAtEntry','Reach','dfgCons_congr','loadVal_congr']
checks = '\n'.join('#check @Backend.Proof.Driver.'+n+'\n#print axioms Backend.Proof.Driver.'+n for n in roots)+'\n'
options = 'set_option pp.universes true\nset_option pp.explicit true\nset_option pp.fullNames true\n'
(PKG/'BaselineTypes.lean').write_text('import FV.Backend.Proof.LowerSim\n'+options+checks)
(PKG/'CandidateTypes.lean').write_text('import FV.Backend.Proof.LowerValueRelations\n'+options+checks)
contexts = {}
for seed in seeds:
    dep = closure(TREE,[seed])
    contexts[seed] = {'closure_count':len(dep),'sources':{p:{'candidate_blob':candidate[p],'main_blob':current.get(p),'frozen_blob':frozen.get(p),'overlay':p in rebuild} for p in sorted(dep)}}
save(OUT/'focused-context-v1.json',{'base':BASE,'candidate_tree':TREE,'frozen_source':FROZEN_SHA,'baseline_closure_count':len(baseline_closure),'candidate_closure_count':len(candidate_closure),'baseline_all_sources_equal_frozen':True,'focused_targets':contexts,'queue':queue,'comparison_roots':['Backend.Proof.Driver.'+n for n in roots]})
save(OUT/'focused-ownership-v1.json',{'owner':'worker-O / stock_driver_delivery / investigate_513','purpose':'Focused current-main outcome-interface kernel gates; not a warm cache','package':str(PKG),'read_only_import_policy':'Never write, chmod, or replace shared hardlink inodes. Unlink any owned destination before output writes.','hardlinked_imports':linked,'owned_output_modules':queue,'cleanup':'Remove focused-package-v1/.lake/build after retaining all sources, logs, output hashes and receipts. Never delete shared source outputs.','allocation':'No build allocation reserved. Parent must grant the existing 3GiB proof slot before execution.','builds_started':False})
print(json.dumps({'base':BASE,'tree':TREE,'baseline_sources_equal_frozen':len(baseline_closure),'candidate_closure':len(candidate_closure),'queued_modules':len(queue),'hardlinked_outputs':len(linked),'no_builds':True}))
