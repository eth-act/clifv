from pathlib import Path
import datetime
import fcntl
import hashlib
import json
import os
import subprocess

b = Path('/home/lee/clifv')
r = b / '.worktrees/stock-extending-production-20261031'
e = b / '.git/agent-evidence/stock-memory-20261029'
lock=(e/'main870-cache-import.lock').open('a+')
fcntl.flock(lock,fcntl.LOCK_SH)
source = e / 'sret-result-bytes-packet-v2'
output = r / '.lake/build/lib/lean'
logs = e / 'sret-result-bytes-packet-kernel-v2'
logs.mkdir(exist_ok=True)
output.mkdir(exist_ok=True)
(e / 'sret-result-bytes-packet-owned-outputs-v2.json').write_text(json.dumps(dict(purpose='Compile the one staged heap module without altering tracked source or adding a worktree/cache. Only new module artifacts enter the existing build view; normal Lake traces remain absent until publication.',output=str(output)),indent=2)+'\n')
manifest = json.loads((e / 'sret-result-bytes-packet-v2.json').read_text())
hashes = manifest['files']
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=r, text=True).strip()
env = dict(os.environ)
env.update(json.loads((e / 'author-env-v1.json').read_text()))
env.update(FV_MEMCAP='3G', LEAN_NUM_THREADS='2', OMP_NUM_THREADS='2', OMP_THREAD_LIMIT='2')
previous = json.loads((e / 'sret-result-bytes-packet-state-v1.json').read_text())
assert previous['status'] == 'passed' and previous['head'] == head
name = 'FV/E2E/SretCopyResultBytes.lean'
assert hashes[name] == previous['source_hashes'][name]
assert hashlib.sha256((source / name).read_bytes()).hexdigest() == hashes[name]
modules = ['FV/E2E/SretCopyResultBytesWitness.lean']
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
                    '--log-dir', str(logs / 'audit'), str(source / 'scripts/audit/sret-copy-result-bytes.lean')],
                   cwd=r, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=r, text=True).strip() == head
assert all(hashlib.sha256((source / name).read_bytes()).hexdigest() == digest for name, digest in hashes.items())
receipt = dict(status='passed', head=head, source_hashes=hashes, modules=2, modules_checked=len(modules), modules_reused=1,
               generic_roots=6, fixed_witness_roots=0, full_goal_complete=False,
               scope='Both original source allocations remain live after return. The existing model result yields all destination and source bytes for arbitrary contents. This is a conclusion adapter,not an accepted-input execution certificate. A constructive witness inhabits every conditional adapter premise. It uses an identity machine only for abstract non-vacuity. Actual compiled execution,default activation,and full140 remain open',
               utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(e / 'sret-result-bytes-packet-state-v2.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
