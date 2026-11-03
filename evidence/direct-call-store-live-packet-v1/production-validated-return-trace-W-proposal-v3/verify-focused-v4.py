from pathlib import Path
import hashlib
import json
import os
import psutil
import shutil
import subprocess

D = Path(__file__).resolve().parent
Q = D.parent
E = Q.parent
R = Q / 'validation-package-v1'
P = E / '892-joint-current-context-v2/package'
T = Q / 'callee-trap-prep-v1'
L = D / 'focused-kernel-v4'
release = json.loads((D / 'command-release-v4.json').read_text())
assert release['approved'] and release['allocation'] == '2G'
assert release['prefix_returned_by_coordinator'] is True
assert release['script_sha256'] == hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
assert release['proposal_sha256'] == '135154e882ed8df490f3ad94cea475b434a48da9d53ea2a2d2fa94128ce20750'
L.mkdir()

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

context_path = D / 'current-source-context-v1/manifest.json'
assert sha(context_path) == 'a63b2a4785011325f2dc9a2e6804abbe9000890eafcff37a934b07771d2520b2'
I = json.loads(context_path.read_text())
assert sha(D / 'manifest.json') == '135154e882ed8df490f3ad94cea475b434a48da9d53ea2a2d2fa94128ce20750'
assert I['staged_dependencies']['FV/E2E/WorldReturnTraceCore.lean']['approved_definition_source_equal']
for name, digest in I['configs'].items():
    assert sha(R / name) == digest, name
for rel, digest in I['sources'].items():
    path = D / 'source' / rel if rel == I['owned'] else R / rel
    assert sha(path) == digest, rel
for process in psutil.process_iter(['name', 'cmdline', 'status', 'uids']):
    try:
        if process.info['uids'].real != os.getuid() or process.info['status'] == 'zombie':
            continue
        if process.info['name'] in ['lean', 'lake']:
            assert not process.cwd().startswith(str(R)), (process.pid, 'R writer')
            assert not any(str(R) in arg for arg in (process.info['cmdline'] or [])), (process.pid, 'R writer')
    except (psutil.NoSuchProcess, psutil.AccessDenied):
        pass

env = dict(os.environ)
for key in ['FV_LAKE_CACHE', 'FV_MEMCAP_OFF', 'LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LAKE_CACHE_DIR']:
    env.pop(key, None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:' + env['PATH'],
           FV_ROOT=str(R), FV_MEMCAP='2G', LAKE_ARTIFACT_CACHE='false',
           LAKE_RESTORE_ARTIFACTS='false', LEAN_NUM_THREADS='1', OMP_NUM_THREADS='1', OMP_THREAD_LIMIT='1')
records = []

def run(label, args):
    local_env = dict(env, FV_MEMCAP_STATS=str(L / (label + '.mem')),
                     FV_MEMCAP_UNIT='worker-o-validated-W-' + label)
    with (L / (label + '.log')).open('w') as output:
        code = subprocess.call([str(P / 'scripts/memcap.sh'), *args], cwd=R, env=local_env,
                               stdout=output, stderr=subprocess.STDOUT)
    record = dict(label=label, argv=args, exit=code, log_sha256=sha(L / (label + '.log')),
                  memory=(L / (label + '.mem')).read_text() if (L / (label + '.mem')).exists() else None)
    records.append(record)
    (L / 'progress.json').write_text(json.dumps(records, indent=2) + '\n')
    print(label, code, flush=True)
    if code:
        raise SystemExit(code)

baseline = sorted(set(I['sources']) - {I['owned']})
assert sha(Q/'production-validated-return-trace-W-proposal-v2/focused-kernel-v3/proper387.log')=='9a1b137bf58bb3cffd1f2bfae55fbb10558fccdaced92a1bdaa98345231e8e2f'
(L/'reused-proper387.json').write_text(json.dumps({'actual_prior_exit':0,'source_and_config_bytes_rechecked':True,'prior_log_sha256':'9a1b137bf58bb3cffd1f2bfae55fbb10558fccdaced92a1bdaa98345231e8e2f','no_dependency_build_requested':True})+'\n')
source = D / 'source' / I['owned']
destination = R / I['owned']
if destination.exists() and sha(destination)!=sha(source):
    assert sha(destination)==sha(D/'failed-source-v3.lean')
    (L/'source-before-namespace-fix.lean').write_bytes(destination.read_bytes())
destination.parent.mkdir(parents=True, exist_ok=True)
shutil.copyfile(source, destination)
(L / 'source-before-kernel.lean').write_bytes(source.read_bytes())
module = I['owned'][:-5].replace('/', '.')
run('kernel', ['lake', '-v', 'build', '+' + module + ':leanArts'])
run('normal388', ['lake', 'build', '--no-build', module])
roots = ['E2E.backend_correct_world_niX_validatedW', 'E2E.backend_correct_world_niX_cleanup_validatedW',
         'E2E.worldReturnTraceProvider_validated', 'E2E.worldReturnTraceProvider_cleanup_validated']
audit = L / 'validated-return-trace-w.lean'
audit.write_text('import FV.E2E.ValidatedReturnTraceW\n\n' + '\n'.join('#print axioms ' + name for name in roots) + '\n')
env['WORKER_O_AUDIT_COMMAND_LOG'] = str(L / 'actual-lean-commands.jsonl')
run('real-audit', ['python3', str(P / 'scripts/axiom-audit.py'), '--cwd', str(R),
                   '--log-dir', str(L / 'audit'), str(audit)])
import importlib.util
spec=importlib.util.spec_from_file_location('validated_w_axioms',E/'general7-main-candidate-v1/old-axiom-preservation-v1/axiom_records.py')
collector=importlib.util.module_from_spec(spec);spec.loader.exec_module(collector)
axes={}
for log in (L/'audit').glob('*.log'):
    for name,used in collector.parse_records(log.read_text()):
        assert name not in axes
        axes[name]=sorted(used)
assert set(axes)==set(roots)
assert all(set(used)<={'Classical.choice','Quot.sound','propext'} for used in axes.values())
for rel, digest in I['sources'].items():
    assert sha(R / rel) == digest, rel
outputs = {}
for area in ['lib/lean', 'ir']:
    stem = R / '.lake/build' / area / I['owned'][:-5]
    for path in stem.parent.glob(stem.name + '.*'):
        if path.is_file():
            outputs[str(path.relative_to(R))] = sha(path)
receipt = dict(status='PASSED_STAGED_W_EXPORT;NOT_PRODUCTION_COMPLETION', records=records,
               source_context_sha256=sha(context_path), proposal_sha256=sha(D / 'manifest.json'),
               current_main_source_projection=I['main'], staged_Core=I['staged_dependencies'],
               baseline_modules=len(baseline), source_hashes=I['sources'], outputs=outputs,
               standard_roots=roots, axiom_sets=axes, actual_auditor_sha256=sha(P / 'scripts/axiom-audit.py'),
               no_old_source_change=True, full_goal_complete=False)
(L / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
