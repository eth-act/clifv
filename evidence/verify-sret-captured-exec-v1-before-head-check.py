from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess

b = Path('/home/lee/clifv')
r = b / '.worktrees/stock-extending-production-20261031'
e = b / '.git/agent-evidence/stock-memory-20261029'
source = e / 'WorkerOSretCapturedExecDraftV1.lean'
assert source.is_file()
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()
for name in ['return-pin-binary-final-state-v1.json','return-pin-executable-final-state-v1.json','sret-exec-result-bytes-packet-state-v1.json']:
    prerequisite=json.loads((e/name).read_text())
    assert prerequisite['status']=='passed' and prerequisite['head']==head,name
digest = hashlib.sha256(source.read_bytes()).hexdigest()
env = dict(os.environ)
env.update(json.loads((e / 'author-env-v1.json').read_text()))
env.update(FV_MEMCAP='3G', LEAN_NUM_THREADS='2', OMP_NUM_THREADS='2', OMP_THREAD_LIMIT='2',
           FV_MEMCAP_UNIT='worker-o-sret-captured-exec-v1',
           FV_MEMCAP_STATS=str(e / 'sret-captured-exec-memory-v1.log'))
logs = e / 'sret-captured-exec-kernel-v1'
logs.mkdir(exist_ok=True)
with (logs / 'summary.log').open('w') as log:
    subprocess.run(['nice', '-n', '10', str(r / 'scripts/memcap.sh'), 'python3', 'scripts/axiom-audit.py',
                    '--log-dir', str(logs / 'audit'), str(source)],
                   cwd=r, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
assert hashlib.sha256(source.read_bytes()).hexdigest() == digest
receipt = dict(status='passed', source_sha256=digest, generic_roots=0, fixed_roots=2,
               full_goal_complete=False,
               scope='The original complete linked caller/callee executes under the existing source and executable theorems for arbitrary symbolic source bytes in both cleanup modes. Every destination and source byte is specified. The fixed-image static facts supply non-vacuity; no accepted-input execution certificate is added. Default activation and full140 remain open',
               utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(e / 'sret-captured-exec-state-v1.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt), flush=True)
