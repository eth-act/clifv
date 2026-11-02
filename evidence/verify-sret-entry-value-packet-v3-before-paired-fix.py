from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess

b = Path('/home/lee/clifv')
r = b / '.worktrees/stock-extending-production-20261031'
e = b / '.git/agent-evidence/stock-memory-20261029'
source = e / 'sret-entry-value-packet-v3'
output = r / '.lake/build/lib/lean'
logs = e / 'sret-entry-value-packet-kernel-v3'
logs.mkdir(exist_ok=True)
output.mkdir(exist_ok=True)
(e / 'sret-entry-value-packet-owned-outputs-v1.json').write_text(json.dumps(dict(purpose='Compile the ten staged proof modules without altering tracked source or adding a worktree/cache. Only new module artifacts enter the existing build view; normal Lake traces remain absent until publication.',output=str(output)),indent=2)+'\n')
manifest = json.loads((e / 'sret-entry-value-packet-v3.json').read_text())
hashes = manifest['files']
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=r, text=True).strip()
env = dict(os.environ)
env.update(json.loads((e / 'author-env-v1.json').read_text()))
env.update(FV_MEMCAP='3G', LEAN_NUM_THREADS='2', OMP_NUM_THREADS='2', OMP_THREAD_LIMIT='2')
modules = ['FV/Backend/Proof/StockSourceReachability.lean', 'FV/Backend/Proof/StockSretSourceStability.lean', 'FV/Backend/Proof/StockReachableReturn.lean', 'FV/Backend/Proof/StockReachableJump.lean', 'FV/Backend/Proof/StockMemorySretCopyEntryValue.lean', 'FV/Backend/Proof/StockMemorySretCopyEntryValueWitness.lean', 'FV/E2E/StockSretPointerWorld.lean', 'FV/E2E/StockSretPointerWorldWitness.lean', 'FV/E2E/StockSretPointerPaired.lean', 'FV/E2E/StockSretPointerPairedWitness.lean']
for name in modules:
    assert hashlib.sha256((source / name).read_bytes()).hexdigest() == hashes[name]
    assert name in hashes  # Rebuild only worker-O's ten additive modules in this reviewed packet.
    target = output / Path(name).with_suffix('')
    target.parent.mkdir(parents=True, exist_ok=True)
    with (logs / (Path(name).stem + '.log')).open('w') as log:
        subprocess.run(['nice', '-n', '10', str(r / 'scripts/memcap.sh'), 'lake', 'env', 'lean',
                        '--root=' + str(source), str(source / name), '-o', str(target) + '.olean',
                        '-i', str(target) + '.ilean', '-c', str(target) + '.c'],
                       cwd=r, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    print('KERNEL', name, 'passed', flush=True)
with (logs / 'audit-summary.log').open('w') as log:
    subprocess.run(['nice', '-n', '10', str(r / 'scripts/memcap.sh'), 'python3', 'scripts/axiom-audit.py',
                    '--log-dir', str(logs / 'audit'), str(source / 'scripts/audit/stock-sret-entry-value.lean')],
                   cwd=r, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=r, text=True).strip() == head
assert all(hashlib.sha256((source / name).read_bytes()).hexdigest() == digest for name, digest in hashes.items())
receipt = dict(status='passed', head=head, source_hashes=hashes, modules=len(modules),
               generic_roots=30, fixed_witness_roots=4, full_goal_complete=False,
               scope='The complete original captured source returns its entry pointer in the actual ARM x8 register through both cleanup modes and every backend stage. Original source/world/argument/heap/ABI/trace/per-state premises remain unchanged. Paired runs retain the original pointer in physical ARM x8. Linked program integration, executable heap witnesses, default activation, and full140 remain open.',
               utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(e / 'sret-entry-value-packet-state-v3.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
