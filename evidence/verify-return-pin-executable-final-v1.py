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
manifest = json.loads((e / 'return-pin-executable-packet-v3.json').read_text())
runtime = json.loads((e / 'return-pin-linker-runtime-packet-v5.json').read_text())
hashes = manifest['files']
env = dict(os.environ)
env.update(json.loads((e / 'author-env-v1.json').read_text()))
env.update(FV_ROOT=str(r), FV_MEMCAP='12G', LEAN_NUM_THREADS='2',
           OMP_NUM_THREADS='2', OMP_THREAD_LIMIT='2')

def head():
    return subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=r, text=True).strip()

start = head()
binary = json.loads((e / 'return-pin-binary-final-state-v1.json').read_text())
assert binary['status'] == 'passed' and binary['head'] == start
assert binary['old_headers_exact'] == binary['old_axiom_sets_exact'] == 25
release = json.loads((e / 'return-pin-executable-view-release-v1.json').read_text())
assert release['status'] == 'released' and release['head'] == start
assert release['source_hashes'] == hashes
# Keep the prior runtime packet and the final binary packet byte-identical.
all_hashes = {**binary['source_hashes'], **runtime['files'], **hashes}
assert len(all_hashes) == len(binary['source_hashes']) + len(runtime['files']) + len(hashes)
assert all(hashlib.sha256((r / name).read_bytes()).hexdigest() == digest
           for name, digest in all_hashes.items())
for pid, label in [(3477137, b'return-pin-call-consumer-recovery-v3'),
                   (3478090, b'consumer-runtime-recovered-delivery-v3'),
                   (3478318, b'sret-recovered-delivery-and-pointer-gates-v2'),
                   (3507911, b'captured-symbolic-packet-after-importers-v1')]:
    process = Path('/proc') / str(pid) / 'cmdline'
    assert not process.exists() or label not in process.read_bytes(), (pid, label)
logs = e / ('return-pin-executable-final-kernel-v1-' + start[:12])
assert not logs.exists(), 'Preserve the previous attempt before choosing a new gate version'
logs.mkdir()
roots = sorted(str(p.relative_to(r)).removesuffix('.lean').replace('/', '.')
               for p in (r / 'FV').rglob('*.lean'))
assert 'FV.Link.ReturnPinExeWith' in roots
assert 'FV.E2E.ReturnPinLinkerWitness' in roots
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
                    'scripts/audit/return-pin-compile.lean',
                    'scripts/audit/return-pin-executable.lean'], cwd=r, env=env,
                   stdout=log, stderr=subprocess.STDOUT, check=True)

def axioms(path):
    text = ' '.join(path.read_text().split())
    return {name: sorted(v.strip() for v in values.split(',') if v.strip())
            for name, values in re.findall(
                r"'(\S+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", text)}

audit = r / 'scripts/audit/return-pin-executable.lean'
generic = set(re.findall(r'^#print axioms (\S+)\s*$', audit.read_text(), re.M))
fixed = set(re.findall(r'^#print axioms (\S+) -- witness: native_decide\s*$', audit.read_text(), re.M))
assert len(generic) == 43 and len(fixed) == 17 and not generic.intersection(fixed)
actual = axioms(logs / 'audit/return-pin-executable.log')
assert set(actual) == generic | fixed
assert all(actual[name] == manifest['expected_axiom_sets'][name] for name in generic)
old = axioms(e / 'return-pin-binary-old-audit-v1/return-pin-binary-old-audit-v1.log')
assert len(old) == 25 and axioms(logs / 'audit/return-pin-binary-old-audit-v1.log') == old
assert head() == start
assert all(hashlib.sha256((r / name).read_bytes()).hexdigest() == digest
           for name, digest in all_hashes.items())
receipt = dict(status='passed', head=start, source_hashes=hashes,
               prerequisite_hashes={**binary['source_hashes'], **runtime['files']},
               fv_roots=len(roots), generic_roots=43, fixed_roots=17,
               old_binary_axiom_sets_exact=25, logs=str(logs), full_goal_complete=False,
               scope='The integrated executable and linker modules pass all FV importers and the unchanged audit. Generic axiom sets remain exact. The prior runtime and binary sources remain exact. Captured symbolic execution, generated proofs, production activation, and full140 remain open.',
               utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(e / 'return-pin-executable-final-state-v1.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt), flush=True)
