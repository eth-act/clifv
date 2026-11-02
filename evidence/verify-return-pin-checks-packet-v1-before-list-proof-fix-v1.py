from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess

b = Path('/home/lee/clifv')
r = b / '.worktrees/stock-extending-production-20261031'
e = b / '.git/agent-evidence/stock-memory-20261029'
source = e / 'return-pin-checks-packet-v1'
output = r / '.lake/build/lib/lean'
logs = e / 'return-pin-checks-packet-kernel-v1'
logs.mkdir(exist_ok=True)
output.mkdir(exist_ok=True)
(e / 'return-pin-checks-packet-owned-outputs-v1.json').write_text(json.dumps(dict(purpose='Compile the one staged heap module without altering tracked source or adding a worktree/cache. Only new module artifacts enter the existing build view; normal Lake traces remain absent until publication.',output=str(output)),indent=2)+'\n')
manifest = json.loads((e / 'return-pin-checks-packet-v1.json').read_text())
hashes = manifest['files']
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=r, text=True).strip()
env = dict(os.environ)
env.update(json.loads((e / 'author-env-v1.json').read_text()))
env.update(FV_MEMCAP='3G', LEAN_NUM_THREADS='2', OMP_NUM_THREADS='2', OMP_THREAD_LIMIT='2')
modules = ['FV/E2E/ReturnPinChecksWith.lean','FV/E2E/ReturnPinChecksWithWitness.lean']
for name in modules:
    assert hashlib.sha256((source / name).read_bytes()).hexdigest() == hashes[name]
    assert name in hashes  # Rebuild only worker-O's additive heap module in this reviewed packet.
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
                    '--log-dir', str(logs / 'audit'), str(source / 'scripts/audit/return-pin-checks-with.lean')],
                   cwd=r, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=r, text=True).strip() == head
assert all(hashlib.sha256((source / name).read_bytes()).hexdigest() == digest for name, digest in hashes.items())
receipt = dict(status='passed', head=head, source_hashes=hashes, modules=len(modules),
               generic_roots=5, fixed_witness_roots=2, full_goal_complete=False,
               scope='The generated checker composes slices against the complete actual program and one return-pin context. Its complete original mixed-program witness and prior identity witness retain both cleanup modes. No old API changes. Proof emitter/default activation and full140 remain open',
               utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(e / 'return-pin-checks-packet-state-v1.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
