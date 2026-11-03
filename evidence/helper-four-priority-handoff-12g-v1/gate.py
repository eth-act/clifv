from pathlib import Path
import hashlib, json, os, psutil, re, shutil, subprocess
D = Path(__file__).resolve().parent
E = D.parent
P = E / '892-joint-current-context-v2/package'
Q = E / 'direct-call-store-live-packet-v1/callee-trap-prep-v1/four-provider-broad-proposal-v1'
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(Q / 'manifest.json') == '969def0e82773f63336fefa111795c1a86076d63adf1fe7e31b564403d1ae098'
I = json.loads((Q / 'manifest.json').read_text())
release = json.loads((D / 'command-release-v1.json').read_text())
assert release['approved'] and release['allocation'] == '12G'
assert release['manifest_sha256'] == sha(Q / 'manifest.json') and release['script_sha256'] == sha(Path(__file__))
env = dict(os.environ)
for k in ['FV_MEMCAP_OFF', 'FV_LAKE_CACHE', 'LEAN_PATH', 'LEAN_SYSROOT', 'LEAN_SRC_PATH', 'LAKE_CACHE_DIR']:
    env.pop(k, None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:' + env['PATH'], FV_ROOT=str(P), FV_MEMCAP='12G', LAKE_ARTIFACT_CACHE='false', LAKE_RESTORE_ARTIFACTS='false', LEAN_NUM_THREADS='2', OMP_NUM_THREADS='2', OMP_THREAD_LIMIT='2')
records = []
def guards():
    controller = psutil.Process(release['broad_controller_pid'])
    assert controller.create_time() == release['scheduler_birth'] and controller.status() == psutil.STATUS_STOPPED
    assert not any(p.is_running() and p.status() != psutil.STATUS_ZOMBIE for p in controller.children(recursive=True))
    for n, h in I['config_hashes'].items():
        assert sha(P / n) == h, n
    for n, h in I['source686_hashes'].items():
        assert sha(P / n) == h, n
def run(label, args, allowed=(0,)):
    guards()
    e = dict(env, FV_MEMCAP_STATS=str(D / (label + '.mem')), FV_MEMCAP_UNIT='worker-o-helper-four12-' + label)
    with (D / (label + '.log')).open('w') as out:
        rc = subprocess.call([str(P / 'scripts/memcap.sh'), 'lake', *args], cwd=P, env=e, stdout=out, stderr=subprocess.STDOUT)
    records.append({'label': label, 'argv': ['lake', *args], 'exit': rc, 'log_sha256': sha(D / (label + '.log')), 'memory': (D / (label + '.mem')).read_text() if (D / (label + '.mem')).exists() else None})
    (D / 'progress.json').write_text(json.dumps(records, indent=2) + '\n')
    print(label, rc, flush=True)
    assert rc in allowed, (label, rc, 'Inspect exact diagnostic; no unchanged retry')
    return rc
def module(path):
    return path[:-5].replace('/', '.')
def artifacts(name):
    result = {}
    for directory in ['lib/lean', 'ir']:
        stem = P / '.lake/build' / directory / name.replace('.', '/')
        for p in stem.parent.glob(stem.name + '.*'):
            if p.is_file():
                result[str(p.relative_to(P))] = sha(p)
    return result
targets = {}
try:
    guards()
    old = {}
    for rel in I['sequential_order']:
        name = module(rel)
        old[name] = artifacts(name)
        for path in old[name]:
            dest = D / 'old-provider-outputs' / path
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(P / path, dest)
    (D / 'preserved-old-outputs.json').write_text(json.dumps(old, indent=2) + '\n')
    for index, rel in enumerate(I['sequential_order']):
        name = module(rel)
        run('deps' + str(index), ['build', '--no-build', *[module(n) for n in I['baseline_graph'][rel]]])
        run('key' + str(index), ['query', '--no-build', '+' + name + ':depHash'])
        keys = re.findall(r'^[0-9a-f]{16}$', (D / ('key' + str(index) + '.log')).read_text(), re.M)
        assert keys and keys[-1] == I['targets'][rel]['expected_native_key'], (name, keys, 'Expected key changed; inspect before building')
        ready = run('ready' + str(index), ['build', '--no-build', name], allowed=(0, 3)) == 0
        if not ready:
            run('kernel' + str(index), ['-v', 'build', '+' + name + ':leanArts'])
        run('normal' + str(index), ['build', '--no-build', name])
        trace = P / '.lake/build/lib/lean' / Path(name.replace('.', '/')).with_suffix('.trace')
        t = json.loads(trace.read_text())
        assert not t.get('synthetic') and t.get('inputs') and t['depHash'] == keys[-1], name
        targets[name] = {'native_key': t['depHash'], 'outputs': t['outputs'], 'trace_sha256': sha(trace), 'artifacts': artifacts(name), 'reused_completed_output': ready}
        (D / 'passed-provider-outputs.json').write_text(json.dumps(targets, indent=2) + '\n')
    run('complete686', ['build', '--no-build', *[module(n) for n in sorted(I['source686_hashes'])]])
    (D / 'receipt.json').write_text(json.dumps({'status': 'passed-four-proper-providers-and-complete686', 'manifest_sha256': sha(Q / 'manifest.json'), 'release_sha256': sha(D / 'command-release-v1.json'), 'targets': targets, 'records': records, 'source_change': 'none', 'allocation': 'exclusive12GiB broad slot', 'full_goal_complete': False}, indent=2) + '\n')
finally:
    (D / 'lease-ended.json').write_text(json.dumps({'controller': os.getpid(), 'restore_same_broad_scheduler': True}) + '\n')
