from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess

b = Path('/home/lee/clifv')
r = b / '.worktrees/stock-extending-production-20261031'
e = b / '.git/agent-evidence/stock-memory-20261029'
source = e / 'WorkerOSretExecResultBytesDraftV1.lean'
assert source.is_file()
digest = hashlib.sha256(source.read_bytes()).hexdigest()
env = dict(os.environ)
env.update(json.loads((e / 'author-env-v1.json').read_text()))
env.update(FV_MEMCAP='3G', LEAN_NUM_THREADS='2', OMP_NUM_THREADS='2', OMP_THREAD_LIMIT='2',
           FV_MEMCAP_UNIT='worker-o-sret-exec-result-bytes-v1',
           FV_MEMCAP_STATS=str(e / 'sret-exec-result-bytes-memory-v1.log'))
logs = e / 'sret-exec-result-bytes-kernel-v1'
logs.mkdir(exist_ok=True)
with (logs / 'summary.log').open('w') as log:
    subprocess.run(['nice', '-n', '10', str(r / 'scripts/memcap.sh'), 'python3', 'scripts/axiom-audit.py',
                    '--log-dir', str(logs / 'audit'), str(source)],
                   cwd=r, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
assert hashlib.sha256(source.read_bytes()).hexdigest() == digest
receipt = dict(status='passed', source_sha256=digest, generic_roots=2, fixed_roots=0,
               full_goal_complete=False,
               scope='The existing executable result yields all symbolic source and destination bytes because compact code relocation bytes exclude both live heap regions. This is an output adapter only. Actual linked instantiation,default activation,and full140 remain open',
               utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(e / 'sret-exec-result-bytes-state-v1.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt), flush=True)
