from pathlib import Path
import json,hashlib,subprocess,os,time,psutil,fcntl,datetime
O=Path(__file__).resolve().parent;C=json.loads((O/'context.json').read_text());P=Path(C['package']);R=Path('/home/lee/clifv');L=P/'.lake/build/lib/lean';LOG=O/'provider-kernels-v1';LOG.mkdir();lock=(O/'kernel-owner.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='892-joint-12G'
env=dict(os.environ)
for k in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','FV_LAKE_CACHE','LAKE_CACHE_DIR','LAKE_ARTIFACT_CACHE','LAKE_RESTORE_ARTIFACTS','FV_MEMCAP_OFF']:env.pop(k,None)
env.update(FV_MEMCAP='12G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',PYTHONDONTWRITEBYTECODE='1',FV_ROOT=str(P),LEAN_PATH=str(L)+':'+C['toolchain_library'])
memcap=R/'.worktrees/stock-extending-production-20261031/scripts/memcap.sh';records=[]
def sha(f):
 d=hashlib.sha256()
 with Path(f).open('rb') as q:
  for b in iter(lambda:q.read(1048576),b''):d.update(b)
 return d.hexdigest()
for rel,h in C['source_hashes'].items():assert sha(P/rel)==h,rel
for rel,item in C['reused'].items():
 for suf,x in item['outputs'].items():assert sha(str(L/Path(rel).with_suffix(''))+suf)==x['sha256']
for i,rel in enumerate(C['kernel_queue']):
 stem=L/Path(rel).with_suffix('');stem.parent.mkdir(parents=True,exist_ok=True)
 for f in stem.parent.glob(stem.name+'.*'):
  if f.is_file() or f.is_symlink():f.unlink()
 log=LOG/(str(i)+'-'+Path(rel).stem+'.log');stats=log.with_suffix('.mem');child=dict(env,FV_MEMCAP_UNIT='worker-o-892-joint-v2-'+str(i),FV_MEMCAP_STATS=str(stats))
 cmd=[C['lean_executable'],'-j2','--root='+str(P),str(P/rel),'-o',str(stem)+'.olean','-i',str(stem)+'.ilean','-c',str(stem)+'.c'];start=time.monotonic();threads=0
 dep_hashes={d:sha(L/Path(d).with_suffix('.olean')) for d in C['imports'].get(rel,[]) if d.startswith(('FV/','FVTest/'))}
 with log.open('w') as out:
  proc=subprocess.Popen(['nice','-n','10',str(memcap),*cmd],cwd=P,env=child,stdout=out,stderr=subprocess.STDOUT)
  while proc.poll() is None:
   try:
    for x in psutil.Process(proc.pid).children(recursive=True):
     if x.name()=='lean':threads=max(threads,x.num_threads())
   except (psutil.NoSuchProcess,psutil.AccessDenied):pass
   time.sleep(1)
 outputs={}
 if proc.returncode==0:
  for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir','.c']:
   f=Path(str(stem)+suffix)
   if f.exists():outputs[suffix]={'sha256':sha(f),'bytes':f.stat().st_size}
 rec={'index':i,'source':rel,'source_sha256':sha(P/rel),'direct_import_output_sha256':dep_hashes,'command':cmd,'exit':proc.returncode,'elapsed_seconds':time.monotonic()-start,'max_os_threads':threads,'memstats':stats.read_text() if stats.exists() else 'missing','log_sha256':sha(log),'outputs':outputs};records.append(rec)
 (LOG/'progress.json').write_text(json.dumps({'records':records},indent=2)+'\n')
 if proc.returncode:
  (O/'providers-state-v1.json').write_text(json.dumps({'status':'stopped_at_first_failure','failed':rec,'passed':len(records)-1,'full_goal_complete':False,'automatic_retry':False},indent=2)+'\n');raise SystemExit(proc.returncode if proc.returncode>0 else 1)
 print('PASSED',i,rel,round(rec['elapsed_seconds'],1),flush=True)
result={'status':'passed','joint_tree':C['joint_tree'],'source_hashes':C['source_hashes'],'reused':len(C['reused']),'new_kernels':len(records),'records':records,'full_goal_complete':False,'normalkeys':'Direct kernels; fullnormalkey/importer gate remains mandatory','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(O/'providers-state-v1.json').write_text(json.dumps(result,indent=2)+'\n');print('ALL JOINT PROVIDERS PASSED',flush=True)
