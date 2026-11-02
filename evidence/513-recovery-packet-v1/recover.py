"""Recover PR 513 without a checkout, build, or branch mutation."""
from pathlib import Path
import collections, hashlib, io, json, re, subprocess, tarfile

ROOT = Path('/home/lee/clifv')
OUT = ROOT / '.git/agent-evidence/stock-memory-20261029/513-recovery-packet-v1'
OLD = '5aae55c32030e3e9f15ab6515a2cccf268751646'
BASE = subprocess.check_output(['git', 'rev-parse', 'origin/main'], cwd=ROOT, text=True).strip()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def save(name, value):
    p = OUT / name
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(value if isinstance(value, bytes) else (json.dumps(value, indent=2)+'\n').encode())

merged = subprocess.run(['git', 'merge-tree', '--write-tree', BASE, OLD], cwd=ROOT, capture_output=True)
save('merge-tree.stdout', merged.stdout)
save('merge-tree.stderr', merged.stderr)
assert merged.returncode == 0, 'Preserved merge diagnostics; resolve explicit conflicts before proceeding'
TREE = merged.stdout.decode().splitlines()[0]
paths = git('diff', '--name-only', BASE, TREE).decode().splitlines()
save('candidate.patch', git('diff', '--binary', BASE, TREE))
hashes = {}
for p in paths:
    data = git('show', TREE+':'+p)
    save('source/'+p, data)
    hashes[p] = hashlib.sha256(data).hexdigest()

archive = tarfile.open(fileobj=io.BytesIO(git('show', '385dc1fc:evidence/outcome-and-mixed-recovery.tar.gz')), mode='r:gz')
names = []
for m in archive.getmembers():
    n = Path(m.name).name
    # Retain exact historical scripts, receipts and logs. Exclude manifests with environment inventories.
    if m.isfile() and n.startswith('stock-outcome-') and n != 'stock-outcome-manifest.json' and n.endswith(('.py', '.json', '.md', '.log', '.txt')):
        save('historical/'+n, archive.extractfile(m).read())
        names.append(n)

# Reuse the historical lexical header reader without running its filesystem or build operations.
reader = (OUT/'historical/stock-outcome-header-parity.py').read_text().split('\ncurrent={}')[0]
ns = {}
exec(compile(reader, 'historical-header-reader', 'exec'), ns)
declarations = ns['declarations']
prior, after = {}, {}
for p in paths:
    if not p.endswith('.lean'):
        continue
    old = subprocess.run(['git', 'show', BASE+':'+p], cwd=ROOT, capture_output=True)
    if old.returncode == 0:
        prior.update(declarations(old.stdout.decode()))
    after.update(declarations(git('show', TREE+':'+p).decode()))
missing = sorted(set(prior)-set(after))
changed = sorted(k for k in prior if k in after and prior[k] != after[k])
save('current-header-parity.json', {'scope':'Lexical public theorem headers in changed source; kernel/type/axiom gates remain required', 'base':BASE, 'tree':TREE, 'prior_count':len(prior), 'missing':missing, 'changed':changed, 'headers':prior})
assert not missing and not changed

# Every import-only consumer retains its entire non-import source exactly.
body_equal = []
for p in paths:
    if not p.endswith('.lean') or p.endswith('/LowerSim.lean'):
        continue
    old = subprocess.run(['git', 'show', BASE+':'+p], cwd=ROOT, capture_output=True)
    if old.returncode:
        continue
    strip = lambda b: re.sub(rb'(?m)^import [^\n]*\n', b'', b)
    assert strip(old.stdout) == strip(git('show', TREE+':'+p)), p
    body_equal.append(p)
save('consumer-body-parity.json', {'base':BASE, 'tree':TREE, 'exact_non_import_source':body_equal})

# Record fresh static dependency scopes. This inventory does not establish elaboration success.
def graph(tree):
    text = git('grep', '-n', '-E', '^import ', tree, '--', '*.lean').decode()
    rev = collections.defaultdict(set)
    modules = set()
    for line in text.splitlines():
        _, path, _, imports = line.split(':', 3)
        mod = path[:-5].replace('/', '.')
        modules.add(mod)
        for dep in imports.removeprefix('import ').split('--')[0].split():
            rev[dep].add(mod)
    return rev, modules

rev, modules = graph(TREE)
seeds = {p[:-5].replace('/', '.') for p in paths if p.endswith('.lean') and p.startswith(('FV/', 'FVTest/', 'Corpus/'))}
affected, todo = set(seeds), list(seeds)
while todo:
    for dependent in rev[todo.pop()]:
        if dependent not in affected:
            affected.add(dependent)
            todo.append(dependent)
audits = sorted(m for m in affected if m.startswith('scripts.audit.'))
inventory = {'base':BASE, 'candidate_tree':TREE, 'changed_roots':sorted(seeds), 'static_reverse_closure':sorted(affected), 'affected_audits':audits, 'count':len(affected), 'audit_count':len(audits), 'classification':'Static import inventory only; fresh normal keys, trust audits, exact old axioms, real tools and generated consumers remain required'}
save('affected-gates.json', inventory)
save('affected-modules.txt', ('\n'.join(sorted(m for m in affected if m.startswith(('FV.', 'FVTest.', 'Corpus.'))))+'\n').encode())
save('recovery-receipt.json', {'base':BASE, 'original_head':OLD, 'candidate_tree':TREE, 'merge_conflicts':[], 'changed_files':len(paths), 'source_sha256':hashes, 'old_headers_exact':len(prior), 'consumer_bodies_exact':len(body_equal), 'recovered_historical_files':names, 'no_builds':True, 'no_branch_or_checkout_mutation':True, 'no_publication':True})
print(json.dumps({'base':BASE,'tree':TREE,'files':len(paths),'headers':len(prior),'bodies':len(body_equal),'affected':len(affected),'audits':len(audits)}))
