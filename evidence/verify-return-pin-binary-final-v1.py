from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess

b = Path('/home/lee/clifv')
r = b / '.worktrees/stock-extending-production-20261031'
e = b / '.git/agent-evidence/stock-memory-20261029'
manifest = json.loads((e / 'return-pin-binary-packet-v1.json').read_text())
hashes = manifest['files']
env = dict(os.environ)
env.update(json.loads((e / 'author-env-v1.json').read_text()))
env.update(FV_ROOT=str(r), FV_MEMCAP='12G', LEAN_NUM_THREADS='2',
           OMP_NUM_THREADS='2', OMP_THREAD_LIMIT='2')

def git(*args):
    return subprocess.check_output(['git', *args], cwd=r, text=True).strip()

# This gate needs an explicitly released, integrated source view.
# It must not replace SemanticBinary beside the current importer or delivery jobs.
head = git('rev-parse', 'HEAD')
release = json.loads((e / 'return-pin-binary-view-release-v1.json').read_text())
assert release['head'] == head and release['status'] == 'released'
assert release['source_hashes'] == hashes
assert git('branch', '--show-current').startswith('agent/stock-return-pin-binary-final-')
for pid, label in [(3477137, b'return-pin-call-consumer-recovery-v3'),
                   (3478090, b'consumer-runtime-recovered-delivery-v3'),
                   (3478318, b'sret-recovered-delivery-and-pointer-gates-v2'),
                   (3507911, b'captured-symbolic-packet-after-importers-v1')]:
    process = Path('/proc') / str(pid) / 'cmdline'
    assert not process.exists() or label not in process.read_bytes(), (pid, label)
for name, digest in hashes.items():
    assert hashlib.sha256((r / name).read_bytes()).hexdigest() == digest, name
headers = json.loads((e / 'return-pin-binary-old-headers-v1.json').read_text())
declarations = '\n'.join((r / name).read_text() for name in hashes
                         if name.startswith('FV/') and name.endswith('.lean'))
assert len(headers) == 25
assert all(header in declarations for header in headers.values())
logs = e / ('return-pin-binary-final-kernel-v1-' + head[:12])
assert not logs.exists(), 'Preserve the previous attempt before choosing a new gate version'
logs.mkdir()
roots = sorted(str(p.relative_to(r)).removesuffix('.lean').replace('/', '.')
               for p in (r / 'FV').rglob('*.lean'))
assert 'FV.E2E.ReturnPinBinaryWitness' in roots
with (logs / 'modules.log').open('w') as log:
    subprocess.run(['nice', '-n', '10', str(r / 'scripts/memcap.sh'), 'python3',
                    'scripts/lake-serial-build.py', '--budget', '12G', '--max-jobs', '1',
                    '--max-cap', '12G', '--default-cap', '6G', '--profile',
                    'scripts/lake-module-peaks.tsv', '--out', str(logs / 'modules'), *roots],
                   cwd=r, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
with (logs / 'audit-summary.log').open('w') as log:
    subprocess.run(['nice', '-n', '10', str(r / 'scripts/memcap.sh'), 'python3',
                    'scripts/axiom-audit.py', '--log-dir', str(logs / 'audit'),
                    str(e / 'return-pin-binary-old-audit-v1.lean'),
                    'scripts/audit/return-pin-binary.lean'], cwd=r, env=env,
                   stdout=log, stderr=subprocess.STDOUT, check=True)

def axioms(path):
    text = ' '.join(path.read_text().split())
    return {name: sorted(v.strip() for v in values.split(',') if v.strip())
            for name, values in re.findall(
                r"'(\S+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", text)}

old = axioms(e / 'return-pin-binary-old-audit-v1/return-pin-binary-old-audit-v1.log')
current = axioms(logs / 'audit/return-pin-binary-old-audit-v1.log')
assert len(old) == 25 and current == old
new = axioms(logs / 'audit/return-pin-binary.log')
assert len(new) == 40
assert git('rev-parse', 'HEAD') == head
assert all(hashlib.sha256((r / name).read_bytes()).hexdigest() == digest
           for name, digest in hashes.items())
receipt = dict(status='passed', head=head, source_hashes=hashes, fv_roots=len(roots),
               old_headers_exact=25, old_axiom_sets_exact=25, new_roots=40,
               logs=str(logs), full_goal_complete=False,
               scope='The integrated binary modules and all FV importers pass. All original binary statement headers and axiom sets remain exact. The unchanged audit checks generic roots and explicitly marked fixed witnesses. Executable consumers, production activation, and full140 remain open.',
               utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(e / 'return-pin-binary-final-state-v1.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt), flush=True)
