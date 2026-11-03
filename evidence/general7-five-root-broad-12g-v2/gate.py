from pathlib import Path
import hashlib, json, os, psutil, re, shutil, subprocess
D = Path(__file__).resolve().parent
E = D.parent
P = E / 'direct-call-store-live-packet-v1/validation-package-v1'
Q = E / 'general7-main-candidate-v1/five-root-minimal-proposal-v3'
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(Q / 'manifest.json') == '1e7d606253193cc6b8e3c449ac384520e70e470800b234f12bbb37e2a629e309'
I = json.loads((Q / 'manifest.json').read_text())
I['config_hashes'] = I['configs']
I['canonical_memcap'] = str(E / '892-joint-current-context-v2/package/scripts/memcap.sh')
I['canonical_memcap_sha256'] = '9e9adcac1cfc595cb420e0ea2bf6815e643f5a7e508f559c0b2055600804a9a5'
I['targets_topological'] = list(I['targets'])
I['unaffected1080'] = sorted(set(I['source_hashes']) - set(I['targets']))
assert len(I['unaffected1080']) == 1080
for record in I['records'].values(): record['expected_key'] = record['expected_R_key']
I['source_hashes'] = {n.replace('.', '/') + '.lean': h for n,h in I['source_hashes'].items()}

release = json.loads((D / 'command-release-v1.json').read_text())
assert release['approved'] and release['allocation'] == '12G'
assert release['manifest_sha256'] == sha(Q / 'manifest.json') and release['script_sha256'] == sha(Path(__file__))
env = dict(os.environ)
for k in ['FV_MEMCAP_OFF', 'FV_LAKE_CACHE', 'LEAN_PATH', 'LEAN_SYSROOT', 'LEAN_SRC_PATH', 'LAKE_CACHE_DIR']:
    env.pop(k, None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:' + env['PATH'], FV_ROOT=str(P), FV_MEMCAP='12G', LAKE_ARTIFACT_CACHE='false', LAKE_RESTORE_ARTIFACTS='false', LEAN_NUM_THREADS='1', OMP_NUM_THREADS='2', OMP_THREAD_LIMIT='2')
records = []
def guards():
    controller = psutil.Process(release['broad_controller_pid'])
    assert controller.create_time() == release['scheduler_birth'] and controller.status() == psutil.STATUS_STOPPED
    assert not any(p.is_running() and p.status() != psutil.STATUS_ZOMBIE for p in controller.children(recursive=True))
    for process in psutil.process_iter(['pid','name','uids']):
        if process.info['name'] not in ['lean','lake'] or process.info['uids'] is None or process.info['uids'].real != os.getuid():
            continue
        try:
            assert process.cwd() != str(P) and not any(str(P) in a for a in process.cmdline()), ('R compiler active',process.pid)
        except (psutil.NoSuchProcess, psutil.ZombieProcess):
            continue
    assert sha(Path(I['canonical_memcap'])) == I['canonical_memcap_sha256']
    for n, h in I['config_hashes'].items():
        assert sha(P / n) == h, n
    for n, h in I['source_hashes'].items():
        assert sha(P / n) == h, n
def run(label, args, allowed=(0,)):
    guards()
    e = dict(env, FV_MEMCAP_STATS=str(D / (label + '.mem')), FV_MEMCAP_UNIT='worker-o-general7-five12v2-' + label)
    with (D / (label + '.log')).open('w') as out:
        rc = subprocess.call([str(E / '892-joint-current-context-v2/package/scripts/memcap.sh'), 'lake', *args], cwd=P, env=e, stdout=out, stderr=subprocess.STDOUT)
    records.append({'label': label, 'argv': ['lake', *args], 'exit': rc, 'log_sha256': sha(D / (label + '.log')), 'memory': (D / (label + '.mem')).read_text() if (D / (label + '.mem')).exists() else None})
    (D / 'progress.json').write_text(json.dumps(records, indent=2) + '\n')
    print(label, rc, flush=True)
    assert rc in allowed, (label, rc, 'Inspect exact diagnostic; no unchanged retry')
    return rc
def module(path):
    return path[:-5].replace('/', '.') if path.endswith('.lean') else path
def artifacts(name):
    result = {}
    for directory in ['lib/lean', 'ir']:
        stem = P / '.lake/build' / directory / name.replace('.', '/')
        for p in stem.parent.glob(stem.name + '.*'):
            if p.is_file():
                result[str(p.relative_to(P))] = sha(p)
    return result
def protected_hashes():
    receipt=E/'direct-call-store-live-packet-v1/callee-trap-prep-v1/helper-final-five-kernels-v1/receipt.json'
    names=list(json.loads(receipt.read_text())['proper12'])+['FV/Backend/Proof/StockTableSelection.lean','FV/Backend/Proof/StockTableValues.lean']
    out={}
    for rel in names:
        for directory,extensions in [('lib/lean',['.trace','.olean','.ilean']),('ir',['.c'])]:
            stem=P/'.lake/build'/directory/rel[:-5]
            for ext in extensions:
                p=stem.with_suffix(ext)
                if p.is_file():out[str(p)]=sha(p)
    return out
targets = {}
try:
    guards()
    assert (D / 'R-writer-release.json').exists(), 'Source worker release is required'
    run('unaffected1080', ['build', '--no-build', *[module(n) for n in I['unaffected1080']]])
    protected_before=protected_hashes()
    (D/'protected-before.json').write_text(json.dumps(protected_before,indent=2)+'\n')
    old = {}
    for rel in I['targets_topological']:
        name = module(rel)
        old[name] = artifacts(name)
        for path in old[name]:
            dest = D / 'old-provider-outputs' / path
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(P / path, dest)
    (D / 'preserved-old-outputs.json').write_text(json.dumps(old, indent=2) + '\n')
    for index, rel in enumerate(I['targets_topological']):
        name = module(rel)
        run('deps' + str(index), ['build', '--no-build', *[module(n) for n in I['records'][rel]['dependencies']]])
        run('key' + str(index), ['query', '--no-build', '+' + name + ':depHash'])
        keys = re.findall(r'^[0-9a-f]{16}$', (D / ('key' + str(index) + '.log')).read_text(), re.M)
        assert len(keys) == 1, (name, keys)
        expected = I['records'][rel]['expected_key']
        if expected is not None:
            assert keys[-1] == expected, (name, keys, 'Expected ready-frontier key changed')
        (D / ('bound-key' + str(index) + '.json')).write_text(json.dumps({'target': name, 'key': keys[-1], 'dependencies_passed': True, 'source_sha256': sha(P / Path(name.replace('.', '/') + '.lean')), 'manifest_sha256': sha(Q / 'manifest.json')}))
        ready = run('ready' + str(index), ['build', '--no-build', name], allowed=(0, 3)) == 0
        if not ready:
            for directory in ['lib/lean','ir']:
                stem = P/'.lake/build'/directory/name.replace('.','/')
                assert str(stem.parent.resolve()).startswith(str((P/'.lake/build').resolve())+'/')
                for output in list(stem.parent.glob(stem.name+'.*')):
                    if output.is_file() and (output.is_symlink() or output.stat().st_nlink != 1 or not output.stat().st_mode & 0o200):
                        temporary = output.with_name(output.name+'.lease-detach')
                        shutil.copyfile(output,temporary)
                        os.replace(temporary,output)
            run('kernel' + str(index), ['-v', 'build', '+' + name + ':leanArts'])
        run('normal' + str(index), ['build', '--no-build', name])
        trace = P / '.lake/build/lib/lean' / Path(name.replace('.', '/')).with_suffix('.trace')
        t = json.loads(trace.read_text())
        assert not t.get('synthetic') and t.get('inputs') and t['depHash'] == keys[-1], name
        targets[name] = {'native_key': t['depHash'], 'outputs': t['outputs'], 'trace_sha256': sha(trace), 'artifacts': artifacts(name), 'reused_completed_output': ready}
        (D / 'passed-provider-outputs.json').write_text(json.dumps(targets, indent=2) + '\n')
    run('complete1085', ['build', '--no-build', *[module(n) for n in sorted(I['source_hashes'])]])
    assert protected_hashes()==protected_before,'Protected passed outputs changed'
    (D / 'receipt.json').write_text(json.dumps({'status': 'passed-five-kernels-and-complete1085', 'manifest_sha256': sha(Q / 'manifest.json'), 'release_sha256': sha(D / 'command-release-v1.json'), 'targets': targets, 'records': records, 'source_change': 'none', 'allocation': 'exclusive12GiB broad slot', 'full_goal_complete': False}, indent=2) + '\n')
finally:
    (D / 'lease-ended.json').write_text(json.dumps({'controller': os.getpid(), 'restore_source2_acquire1': True}) + '\n')
