from common import D,E,restore
from pathlib import Path
import fcntl,hashlib,json,os,psutil,signal,subprocess,sys,time
B=Path('/home/lee/clifv')
R=E/'direct-call-store-live-packet-v1/validation-package-v1'
F=E/'140-fence-packet-v1/package'
Q=E/'general7-main-candidate-v1/complete-two-frontier-repair-proposal-v1'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
lock=(D/'owner.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
assert not (D/'state.json').exists()
assert sha(Q/'manifest.json')=='fd78ff23a58abafa1da1fbfc043b6ec4c2ebdf3a6fa215442c215080aa8e6b13'
I=json.loads((Q/'manifest.json').read_text())
releases=[Q/'source-share-release-v1.json',E/'140-acquire-fused810-packet-v1/share-release-for-three-leaves-v1.json']
for p in releases:assert p.is_file()
assert json.loads(releases[0].read_text())['active_compiler_or_verifier']==[]
assert json.loads(releases[1].read_text())['no_active_owned_compiler']
for p in psutil.process_iter(['pid','name','cmdline']):
    args=p.info['cmdline'] or []
    assert not any(str(E/'backup-reviewed-handoff-') in a for a in args),('Active backup',p.pid)
    if p.info['name'] in ['lean','lake']:
        assert not any(str(R) in a or str(F) in a for a in args),('Compiler not yet released',p.pid,args)
for p,h in I['source_hashes'].items():assert sha(R/p)==h,p
for p,h in I['current_configs'].items():assert sha(R/p)==h,p
scope=Path(f'/sys/fs/cgroup/user.slice/user-{os.getuid()}.slice/user@{os.getuid()}.service/clifv.slice');assert scope.is_dir()
state={'status':'arming','owner':os.getpid(),'owner_birth':psutil.Process().create_time(),'scope_parent':str(scope),'allocation':'broad12/source3/acquire0/orchestration1','release_hashes':{str(p):sha(p) for p in releases},'signals_to_compilers':[],'full_goal_complete':False}
def save():
    p=D/'state.tmp';p.write_text(json.dumps(state,indent=2)+'\n');os.replace(p,D/'state.json')
save()
subprocess.run(['ai-coord','watch','--label','general7-three-leaf-share-restore-v1','--','python3',str(D/'guard.py')],cwd=B,check=True)
for _ in range(100):
    if (D/'guard-armed.json').exists():break
    time.sleep(.1)
else:raise RuntimeError('Independent guard not armed')
release={'approved':True,'allocation':'3G','owner':state['owner'],'owner_birth':state['owner_birth'],'manifest_sha256':sha(Q/'manifest.json'),'script_sha256':sha(D/'gate.py')}
(D/'command-release-v1.json').write_text(json.dumps(release,indent=2)+'\n')
protected=json.loads((E/'direct-call-store-live-packet-v1/callee-trap-prep-v1/helper-final-five-kernels-v1/receipt.json').read_text())['proper12']
def protected_hashes():
    out={}
    for rel in [*protected,'FV/Backend/Proof/StockTableSelection.lean']:
        for directory,extensions in [('lib/lean',['.trace','.olean','.ilean']),('ir',['.c'])]:
            stem=R/'.lake/build'/directory/rel[:-5]
            for ext in extensions:
                p=stem.with_suffix(ext)
                if p.is_file():out[str(p)]=sha(p)
    return out
before=protected_hashes();(D/'protected-before.json').write_text(json.dumps(before,indent=2)+'\n')
child=None
signal.signal(signal.SIGTERM,lambda *_:sys.exit(143))
try:
    child=subprocess.Popen([sys.executable,str(D/'launch.py')],cwd=B,stdout=(D/'consumer-command.log').open('w'),stderr=subprocess.STDOUT)
    for _ in range(100):
        if (D/'consumer-identity.json').exists():break
        time.sleep(.1)
    else:raise RuntimeError('Consumer identity missing')
    state.update(status='running',consumer=json.loads((D/'consumer-identity.json').read_text()));save()
    (D/'permit.json').write_text(json.dumps({'approved':True}))
    rc=child.wait();state['exit']=rc;save();assert rc==0,('Inspect diagnostic before retry',rc)
    assert protected_hashes()==before,'Protected helpers changed'
    state['status']='passed';save()
finally:
    if child is not None and child.poll() is None:
        if not (D/'permit.json').exists():(D/'cancel.json').write_text('{"cancelled":true}')
        child.wait()
    while True:
        busy=False
        for f in scope.glob('worker-o-general7-two3-*.scope/cgroup.procs'):
            try:busy=busy or bool(f.read_text().strip())
            except FileNotFoundError:pass
        if not busy:break
        time.sleep(.2)
    restore('owner finalizer after compiler exit')
    print('Restored source2GiB and acquire1GiB',flush=True)
