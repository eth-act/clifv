from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import time

b = Path('/home/lee/clifv')
r = b / '.worktrees/stock-extending-production-20261031'
e = b / '.git/agent-evidence/stock-memory-20261029'
env = dict(os.environ)
env.update(json.loads((e / 'author-env-v1.json').read_text()))
env.update(FV_MEMCAP='12G', LEAN_NUM_THREADS='2', OMP_NUM_THREADS='2', OMP_THREAD_LIMIT='2')
plan = json.loads((e / 'return-pin-call-consumer-outside-plan-v1.json').read_text())
pid = 1851170
while Path(f'/proc/{pid}/cmdline').exists():
    command = Path(f'/proc/{pid}/cmdline').read_bytes()
    if b'return-pin-call-consumer-importer-gate-v3' not in command:
        break
    time.sleep(2)
parent = json.loads((e / 'return-pin-call-consumer-current-main-state-v1.json').read_text())
assert parent['status'] == 'passed', parent
hashes = parent['source_hashes']
assert all(hashlib.sha256((r / n).read_bytes()).hexdigest() == h for n, h in hashes.items())
with (e / 'return-pin-call-consumer-outside-fv-kernel-v2.log').open('w') as out:
    subprocess.run([
        'nice', '-n', '10', str(r / 'scripts/memcap.sh'), 'python3', 'scripts/lake-serial-build.py',
        '--budget', '12G', '--max-jobs', '1', '--max-cap', '12G', '--default-cap', '6G',
        '--profile', 'scripts/lake-module-peaks.tsv', '--out', str(e / 'return-pin-call-consumer-outside-fv-modules-v2'),
        *plan['fv_roots'],
    ], cwd=r, env=env, stdout=out, stderr=subprocess.STDOUT, check=True)
with (e / 'return-pin-call-consumer-outside-audits-v2.log').open('w') as out:
    subprocess.run([
        'nice', '-n', '10', str(r / 'scripts/memcap.sh'), 'python3', 'scripts/axiom-audit.py',
        '--log-dir', str(e / 'return-pin-call-consumer-outside-audit-v2'), *plan['audits'],
    ], cwd=r, env=env, stdout=out, stderr=subprocess.STDOUT, check=True)
env['FV_MEMCAP'] = '8G'
with (e / 'return-pin-call-consumer-crate-kernel-v2.log').open('w') as out:
    for module in plan['crate_order']:
        print('BUILD', module, flush=True)
        out.write('\nBUILD ' + module + '\n')
        out.flush()
        subprocess.run([
            'nice', '-n', '10', str(r / 'scripts/memcap.sh'), 'lake', 'build', module,
        ], cwd=r / 'crate-proofs', env=env, stdout=out, stderr=subprocess.STDOUT, check=True)
    subprocess.run([
        str(r / 'scripts/memcap.sh'), 'lake', 'build', '--no-build', *plan['crate_targets'],
    ], cwd=r / 'crate-proofs', env=env, stdout=out, stderr=subprocess.STDOUT, check=True)
assert all(hashlib.sha256((r / n).read_bytes()).hexdigest() == h for n, h in hashes.items())
# Keep the shared source view stable until its independent proof owner exits.
while True:
    try:
        proof_owner = Path('/proc/3507911/cmdline').read_bytes()
    except FileNotFoundError:
        break
    if b'captured-symbolic-packet-after-importers-v1' not in proof_owner:
        break
    time.sleep(10)

receipt = dict(status='passed', source_hashes=hashes, affected_crate_modules=len(plan['crate_targets']),
               built_crate_closure=len(plan['crate_order']), external_audits=len(plan['audits']),
               utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), full_goal_complete=False)
(e / 'return-pin-call-consumer-outside-state-v2.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
