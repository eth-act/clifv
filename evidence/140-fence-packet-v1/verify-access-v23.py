from pathlib import Path
import argparse,hashlib,json,os,subprocess,time
O=Path(__file__).resolve().parent;P=O/'package';E=O.parent
a=argparse.ArgumentParser();a.add_argument('--attempt',required=True);a.add_argument('--preflight',action='store_true');a.add_argument('modules',nargs='*');args=a.parse_args()
assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='fence-1G'
SNAP=O/'import-snapshot-v23.json'
S=json.loads(SNAP.read_text())
log=O/'runs'/args.attempt;log.mkdir(parents=True,exist_ok=False)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for m,v in S['modules'].items():assert sha(P/v['source'])==v['sha256']
for p,h in S['artifacts'].items():assert sha(P/p)==h,('Borrowed artifact changed',p)
env=dict(os.environ);env.pop('FV_LAKE_CACHE',None);env.pop('FV_MEMCAP_OFF',None)
env.update(FV_ROOT=str(P),FV_MEMCAP='1G',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LAKE_CACHE_DIR=str(O/'disabled-cache'))
lean=S['lean_executable'];env['PATH']=str(Path(lean).parent)+':'+env['PATH']
env['LEAN_PATH']=str(P/'.lake/build/lib/lean')+':'+S['toolchain_library']
records=[]
def run(label,cmd):
    env['FV_MEMCAP_UNIT']='worker-o-fence-'+args.attempt+'-'+label
    env['FV_MEMCAP_STATS']=str(log/(label+'.mem'))
    start=time.time()
    with (log/(label+'.log')).open('w') as f:
        proc=subprocess.run(['/home/lee/clifv/.worktrees/stock-extending-production-20261031/scripts/memcap.sh',*cmd],cwd=P,env=env,stdout=f,stderr=subprocess.STDOUT)
    records.append({'label':label,'argv':cmd,'exit':proc.returncode,'seconds':time.time()-start,'memstats':(log/(label+'.mem')).read_text() if (log/(label+'.mem')).exists() else None})
    (log/'state.json').write_text(json.dumps({'status':'running' if proc.returncode==0 else 'failed','records':records},indent=2)+'\n')
    assert proc.returncode==0,('Inspect exact diagnostic; no unchanged cap retry',label,proc.returncode)
    print('PASSED',label,flush=True)
if args.preflight:
    run('normal-import-check',[str(Path(lean).with_name('lake')),'build','--no-build',*S['roots']])
    # Genuine normal-key checks must succeed before candidate kernels.
    (O/'import-normal-check-v23.json').write_text(json.dumps({'status':'passed','snapshot_sha256':sha(SNAP),'record':records[-1]},indent=2)+'\n')
else:
    assert json.loads((O/'import-normal-check-v23.json').read_text())['status']=='passed'
for mod in args.modules:
    rel=Path(mod.replace('.','/')+'.lean');stem=P/'.lake/build/lib/lean'/rel.with_suffix('');stem.parent.mkdir(parents=True,exist_ok=True)
    assert mod not in S['modules'],'Do not overwrite borrowed imports'
    for old in stem.parent.glob(stem.name+'.*'):
        if old.is_file() or old.is_symlink():old.unlink()
    run(mod.split('.')[-1],[lean,'-j1','--root='+str(P),str(P/rel),'-o',str(stem)+'.olean','-i',str(stem)+'.ilean'])
    records[-1]['source_sha256']=sha(P/rel);records[-1]['olean_sha256']=sha(Path(str(stem)+'.olean'))
(log/'state.json').write_text(json.dumps({'status':'passed','records':records},indent=2)+'\n')
