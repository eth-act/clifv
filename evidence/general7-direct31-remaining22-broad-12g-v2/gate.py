from pathlib import Path
import hashlib, json, os, psutil, re, shutil, subprocess, tomllib
D = Path(__file__).resolve().parent
E = D.parent
P = E / 'direct-call-store-live-packet-v1/validation-package-v1'
Q = E / 'general7-main-candidate-v1/direct31-remaining22-continuation-proposal-v1'
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(Q / 'manifest.json') == 'd91c57bccb37d97ba5d5d234e408718fb7043db71de71e7ac8e8f44eac32bb26'
I = json.loads((Q / 'manifest.json').read_text())
I['config_hashes'] = I['configs']
I['canonical_memcap'] = str(E / '892-joint-current-context-v2/package/scripts/memcap.sh')
I['canonical_memcap_sha256'] = '9e9adcac1cfc595cb420e0ea2bf6815e643f5a7e508f559c0b2055600804a9a5'
I['targets_topological'] = I['targets_topological22']
I['unaffected1688'] = sorted(set(I['source_hashes'])-set(I['records'])-set(I['protected_ready_targets58']))
assert len(I['unaffected1688']) == 1688 and len(I['targets_topological']) == 22
for record in I['records'].values():
    if record['expected_key'] == 'BIND_ONLY_AFTER_PREDECESSOR_NORMAL_SUCCESS': record['expected_key'] = None
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
            assert process.cwd() not in [str(P),'/home/lee/clifv/.worktrees/loop-20261102'] and not any(str(P) in a or '/home/lee/clifv/.worktrees/loop-20261102' in a for a in process.cmdline()), ('R/G compiler active',process.pid)
        except (psutil.NoSuchProcess, psutil.ZombieProcess):
            continue
    assert sha(Path(I['canonical_memcap'])) == I['canonical_memcap_sha256']
    for n, h in I['config_hashes'].items():
        assert sha(P / n) == h, n
    for n, h in I['source_hashes'].items():
        assert sha(P / n) == h, n
def run(label, args, allowed=(0,)):
    guards()
    e = dict(env, FV_MEMCAP_STATS=str(D / (label + '.mem')), FV_MEMCAP_UNIT='worker-o-general7-direct31-cone22-' + label)
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
    prior=json.loads((E/'general7-five-root-broad-12g-v2/receipt.json').read_text())
    names += [n.replace('.', '/')+'.lean' for n in prior['targets']]
    ladder=json.loads((E/'general7-lowering-ladder-broad-12g-v1/receipt.json').read_text())
    names += [n.replace('.', '/')+'.lean' for n in ladder['targets']]
    names += [n.replace('.', '/')+'.lean' for n in I['protected_ready_targets58']]
    out={}
    for rel in names:
        for directory,extensions in [('lib/lean',['.trace','.olean','.ilean']),('ir',['.c'])]:
            stem=P/'.lake/build'/directory/rel[:-5]
            for ext in extensions:
                p=stem.with_suffix(ext)
                if p.is_file():out[str(p)]=sha(p)
    G=Path('/home/lee/clifv/.worktrees/loop-20261102')
    ni=json.loads((E/'general7-main-candidate-v1/independent-backend-NI-v6/receipt.json').read_text())
    for rel,expected in ni['all8_source_hashes'].items():
        assert sha(G/rel)==expected
        out[str(G/rel)]=expected
    out[str(G/'lakefile.toml')]=sha(G/'lakefile.toml')
    full=json.loads((E/'general7-main-candidate-v1/direct31-current-inventory-v1/manifest.json').read_text())
    for name in full['completed_affected30']:
        for directory,extensions in [('lib/lean',['.trace','.olean','.ilean']),('ir',['.c'])]:
            stem=G/'.lake/build'/directory/name.replace('.','/')
            for ext in extensions:
                file=stem.with_suffix(ext)
                assert file.is_file(),file
                out[str(file)]=sha(file)
    protected=json.loads((Q/'protected-artifacts.json').read_text())
    assert sha(Q/'protected-artifacts.json')==I['protected_artifacts_sha256']
    for rel,h in protected.items():
        assert sha(P/rel)==h,rel
        out[str(P/rel)]=h
    return out
assert sha(Q/'per-entry-origins-proposed.json')==I['proposed_origins_sha256']
origin_release=json.loads((D/'specific20-origin-release.json').read_text())
assert origin_release['approved'] and origin_release['receipt_sha256']==I['new_origins_receipt_sha256']=='0dfe62d4a587efa0dbbfc6d08c6dc6d418ad851a5cd6c057c81867ee81d73a81'
approved=json.loads((Q/'per-entry-origins-proposed.json').read_text())
def origin_ok(root,name):
    path=root/'.lake/build/lib/lean'/Path(name.replace('.', '/')+'.trace')
    data=json.loads(path.read_text())
    if data.get('synthetic'):return False
    if data.get('inputs'):return True
    r=approved.get(name.replace('.', '/')+'.lean',{})
    return r.get('trace_sha256')==sha(path) and r.get('native_key')==data['depHash'] and r.get('outputs')==data['outputs']
def without_weak(value):
    if isinstance(value,dict):return {k:without_weak(v) for k,v in value.items() if k!='weakLeanArgs'}
    if isinstance(value,list):return [without_weak(v) for v in value]
    return value
reuse = {}
def try_donor(name,key,index):
    for label,root in [('P',E/'892-joint-current-context-v2/package'),('G',Path('/home/lee/clifv/.worktrees/loop-20261102'))]:
        tr=root/'.lake/build/lib/lean'/Path(name.replace('.', '/')+'.trace')
        if not tr.exists():continue
        data=json.loads(tr.read_text())
        if data.get('depHash')!=key:continue
        rel=Path(name.replace('.', '/')+'.lean')
        assert sha(root/rel)==sha(P/rel), (name,label,'source mismatch')
        assert without_weak(tomllib.loads((root/'lakefile.toml').read_text()))==without_weak(tomllib.loads((P/'lakefile.toml').read_text())),(name,label,'config difference exceeds weakLeanArgs')
        for config in ['lean-toolchain','lake-manifest.json']:assert sha(root/config)==sha(P/config)
        known=json.loads((D/'donor-config-allowlist.json').read_text())[label]
        for config,expected in known.items():assert sha(root/config)==expected,(label,config,'donor config drift')
        assert origin_ok(root,name),(name,label,'matching donor needs supported creator/archive receipt')
        guards()
        stats=D/('donor'+str(index)+'-'+label+'.mem')
        e=dict(env,FV_ROOT=str(root),FV_MEMCAP_STATS=str(stats),FV_MEMCAP_UNIT='worker-o-general7-direct31-cone22-donor'+str(index)+label)
        log=D/('donor'+str(index)+'-'+label+'.log')
        with log.open('w') as out:rc=subprocess.call([I['canonical_memcap'],'lake','build','--no-build',name],cwd=root,env=e,stdout=out,stderr=subprocess.STDOUT)
        assert rc==0,(name,label,'donor normal check failed',rc)
        before=sha(tr)
        copied={}
        for directory in ['lib/lean','ir']:
            stem=root/'.lake/build'/directory/name.replace('.','/')
            for source in stem.parent.glob(stem.name+'.*'):
                if not source.is_file() or source.name.endswith(('.c.o','.o','.bc')):continue
                dest=P/source.relative_to(root);h=sha(source)
                if dest.is_symlink() or dest.exists():dest.unlink()
                dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,dest)
                assert sha(dest)==h and sha(source)==h
                copied[str(dest.relative_to(P))]=h
        assert sha(tr)==before
        reuse[name]={'owner':label,'key':key,'trace_sha256':before,'artifacts':copied,'normal_exit':rc,'config_relation':'identical except weakLeanArgs','provenance':'fresh normal inputs' if data.get('inputs') else 'specifically approved archive origin'}
        (D/'verified-donor-reuse.json').write_text(json.dumps(reuse,indent=2)+'\n')
        return True
    return False

targets = {}
try:
    guards()
    assert (D / 'R-writer-release.json').exists(), 'Source worker release is required'
    run('unaffected1688', ['build', '--no-build', *[module(n) for n in I['unaffected1688']]])
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
        if not ready and try_donor(name,keys[-1],index):
            ready = run('reused'+str(index), ['build','--no-build',name]) == 0
        if not ready:
            candidates = []
            for label, root in [('A',Path('/home/lee/clifv/.worktrees/driver-proof-resume/.lake/artifact-cache')),('C',E/'892-current-main-context-v1/package/.lake/ci-cache')]:
                descriptor=root/'outputs/fv'/(keys[-1]+'.json')
                if descriptor.exists(): candidates.append({'owner':label,'descriptor':str(descriptor),'sha256':sha(descriptor)})
            for label, root in [('G',Path('/home/lee/clifv/.worktrees/loop-20261102')),('P',E/'892-joint-current-context-v2/package')]:
                donor=root/'.lake/build/lib/lean'/Path(name.replace('.', '/')+'.trace')
                if donor.exists() and json.loads(donor.read_text()).get('depHash')==keys[-1]:
                    candidates.append({'owner':label,'trace':str(donor),'sha256':sha(donor)})
            (D/('matching-donors'+str(index)+'.json')).write_text(json.dumps(candidates,indent=2)+'\n')
            assert not candidates, (name,'Inspect matching provenance before any duplicate build',candidates)
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
        assert origin_ok(P,name) and t['depHash'] == keys[-1], name
        targets[name] = {'native_key': t['depHash'], 'outputs': t['outputs'], 'trace_sha256': sha(trace), 'artifacts': artifacts(name), 'reused_completed_output': ready}
        (D / 'passed-provider-outputs.json').write_text(json.dumps(targets, indent=2) + '\n')
    run('complete1768', ['build', '--no-build', *[module(n) for n in sorted(I['source_hashes'])]])
    assert protected_hashes()==protected_before,'Protected passed outputs changed'
    (D / 'receipt.json').write_text(json.dumps({'status': 'passed-conditional-cone-and-complete1768', 'manifest_sha256': sha(Q / 'manifest.json'), 'release_sha256': sha(D / 'command-release-v1.json'), 'targets': targets, 'records': records, 'source_change': 'none', 'allocation': 'exclusive12GiB broad slot', 'full_goal_complete': False}, indent=2) + '\n')
finally:
    (D / 'lease-ended.json').write_text(json.dumps({'controller': os.getpid(), 'restore_source2_acquire1': True}) + '\n')
