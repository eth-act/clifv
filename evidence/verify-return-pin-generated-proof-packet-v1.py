from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess

b = Path('/home/lee/clifv')
r = b / '.worktrees/stock-extending-production-20261031'
e = b / '.git/agent-evidence/stock-memory-20261029'
packet = e / 'return-pin-generated-proof-packet-v1'
logs = e / 'return-pin-generated-proof-kernel-v1'
output = r / '.lake/build/lib/lean'
manifest = json.loads((e / 'return-pin-generated-proof-packet-v1.json').read_text())
hashes = manifest['files']
driver = e / manifest['driver']
assert hashlib.sha256(driver.read_bytes()).hexdigest() == manifest['driver_sha256']
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=r, text=True).strip()
env = dict(os.environ)
env.update(json.loads((e / 'author-env-v1.json').read_text()))
env.update(FV_ROOT=str(r), FV_MEMCAP='3G', LEAN_NUM_THREADS='2', OMP_NUM_THREADS='2', OMP_THREAD_LIMIT='2')
logs.mkdir(exist_ok=True)
# Run only after the final binary and generated-checker modules enter this owned build view.
for name in ['return-pin-binary-final-state-v1.json', 'return-pin-checks-packet-state-v1.json']:
    prerequisite = json.loads((e / name).read_text())
    assert prerequisite['status'] == 'passed' and prerequisite['head'] == head, name
assert hashlib.sha256((r / 'FVTest/E2E/SemanticLinkProofWith.lean').read_bytes()).hexdigest() == manifest['previous_emitter_sha256']
for module in ['FV/E2E/ReturnPinBinary.olean', 'FV/E2E/ReturnPinChecksWith.olean']:
    assert (output / module).is_file(), 'Finish the existing prerequisite gates before this packet'

def kernel(source, root, name, log_path):
    target = output / Path(name).with_suffix('')
    target.parent.mkdir(parents=True, exist_ok=True)
    with log_path.open('w') as log:
        subprocess.run(['nice', '-n', '10', str(r / 'scripts/memcap.sh'), 'lake', 'env', 'lean',
                        '--root=' + str(root), str(source), '-o', str(target) + '.olean',
                        '-i', str(target) + '.ilean', '-c', str(target) + '.c'],
                       cwd=r, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)

owned = []
for name in ['FV/E2E/ReturnPinGeneratedStack.lean', 'FVTest/E2E/ReturnPinLinkProofWith.lean']:
    source = packet / name
    assert hashlib.sha256(source.read_bytes()).hexdigest() == hashes[name]
    assert not (r / name).exists(), 'Do not overwrite tracked source'
    kernel(source, packet, name, logs / (source.stem + '.log'))
    owned.append(name)
    print('KERNEL', name, 'passed', flush=True)
with (logs / 'stack-audit-summary.log').open('w') as log:
    subprocess.run(['nice', '-n', '10', str(r / 'scripts/memcap.sh'), 'python3', 'scripts/axiom-audit.py',
                    '--log-dir', str(logs / 'stack-audit'), str(packet / 'scripts/audit/return-pin-generated-stack.lean')],
                   cwd=r, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
generated = logs / 'generated'
assert not generated.exists(), 'Preserve the previous generated proof attempt before retrying'
with (logs / 'generate.log').open('w') as log:
    subprocess.run(['nice', '-n', '10', str(r / 'scripts/memcap.sh'), 'lake', 'env', 'lean', '--run',
                    str(driver), str(generated)],
                   cwd=r, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
cases = json.loads((generated / 'manifest.json').read_text())
assert len(cases) == 12
assert {(c['mixed'], c['cleanup'], c['split'], c['all_stack']) for c in cases} == {
    (mixed, cleanup, split, stack) for mixed in [False, True] for cleanup in [False, True]
    for split in ([False, True] if mixed else [False]) for stack in [False, True]}
proof_hashes = {}
for case in cases:
    label = case['module']
    assert label.startswith('WorkerOReturnPinGenerated')
    for index, name in enumerate(case['files']):
        source = Path(name)
        relative = source.relative_to(generated)
        assert relative.parts[0] == 'Crates'
        assert not (r / relative).exists()
        kernel(source, generated, relative, logs / (label + '-' + str(index) + '.log'))
        proof_hashes[str(relative)] = hashlib.sha256(source.read_bytes()).hexdigest()
        owned.append(str(relative))
    audit = logs / (label + '-audit.lean')
    # Each imported crate is a fixed original input. Generic stack/checker roots have separate standard-only audits.
    audit.write_text('import Crates.' + label + '\n\n' + '\n'.join(
        '#print axioms Crates.' + label + '.' + root + ' -- witness: native_decide'
        for root in ['okB_input', 'link_ok', 'base_closed', 'bin_ok', 'correct_0', 'correct_stack_0']) + '\n')
    with (logs / (label + '-audit-summary.log')).open('w') as log:
        subprocess.run(['nice', '-n', '10', str(r / 'scripts/memcap.sh'), 'python3', 'scripts/axiom-audit.py',
                        '--log-dir', str(logs / (label + '-audit')), str(audit)],
                       cwd=r, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    print('GENERATED', label, 'passed', flush=True)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=r, text=True).strip() == head
assert all(hashlib.sha256((packet / name).read_bytes()).hexdigest() == digest for name, digest in hashes.items())
assert hashlib.sha256(driver.read_bytes()).hexdigest() == manifest['driver_sha256']
receipt = dict(status='passed', head=head, source_hashes=hashes, generated_hashes=proof_hashes,
               cases=12, generic_roots=2, fixed_generated_roots=72, owned_modules=owned,
               full_goal_complete=False, scope='The actual unchanged mixed and previous identity images generate and kernel-check ordinary,all-stack,and per-entry stack proofs in both cleanup modes and both split layouts. Original emitter and theorem variants remain unchanged. Production activation and full140 remain open',
               utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
# Generated proof artifacts serve this gate only. Preserve sources and logs, then reclaim them.
removed = []
for name in owned:
    if not name.startswith('Crates/WorkerOReturnPinGenerated'):
        continue
    target = output / Path(name).with_suffix('')
    for suffix in ['.olean', '.olean.private', '.olean.server', '.ilean', '.c']:
        artifact = Path(str(target) + suffix)
        if artifact.exists():
            removed.append(dict(path=str(artifact), bytes=artifact.stat().st_size))
            artifact.unlink()
    try:
        target.parent.rmdir()
    except OSError:
        pass
receipt['generated_artifacts_removed'] = removed
receipt['generated_sources_and_logs_preserved'] = True
(e / 'return-pin-generated-proof-state-v1.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt), flush=True)
