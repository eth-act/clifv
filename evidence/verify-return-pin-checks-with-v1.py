from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess

b = Path('/home/lee/clifv')
r = b / '.worktrees/stock-extending-production-20261031'
e = b / '.git/agent-evidence/stock-memory-20261029'
source = e / 'WorkerOReturnPinChecksWithDraftV1.lean'
assert source.is_file()
digest = hashlib.sha256(source.read_bytes()).hexdigest()
env = dict(os.environ)
env.update(json.loads((e / 'author-env-v1.json').read_text()))
env.update(FV_MEMCAP='3G', LEAN_NUM_THREADS='2', OMP_NUM_THREADS='2', OMP_THREAD_LIMIT='2',
           FV_MEMCAP_UNIT='worker-o-return-pin-checks-with-v1',
           FV_MEMCAP_STATS=str(e / 'return-pin-checks-with-memory-v1.log'))
logs = e / 'return-pin-checks-with-kernel-v1'
logs.mkdir(exist_ok=True)
with (logs / 'summary.log').open('w') as log:
    subprocess.run(['nice', '-n', '10', str(r / 'scripts/memcap.sh'), 'python3', 'scripts/axiom-audit.py',
                    '--log-dir', str(logs / 'audit'), str(source)],
                   cwd=r, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
assert hashlib.sha256(source.read_bytes()).hexdigest() == digest
receipt = dict(status='passed', source_sha256=digest, generic_roots=5, fixed_roots=0,
               full_goal_complete=False,
               scope='Generated proofs can compose ABI-aware slices against the complete program and one cached return-pin context. Exact whole-check equivalence retains the original global checks and all previous successful programs. Concrete capture witnesses and consumer activation remain pending; full140 remains incomplete',
               utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(e / 'return-pin-checks-with-state-v1.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt), flush=True)
