from pathlib import Path
import json,hashlib,subprocess,os,time,psutil,datetime,fcntl,shutil
O=Path(__file__).resolve().parent;C=json.loads((O/'context.json').read_text());P=Path(C['package']);R=Path('/home/lee/clifv');E=O.parent;OLD=E/'892-current-main-context-v1';assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='892-joint-12G'
assert json.loads((O/'normal-handoff-boundary-v1.json').read_text())['status']=='active_module_preserved_controller_released'
lock=(O/'kernel-owner.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
def sha(p):
 d=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):d.update(b)
 return d.hexdigest()
for rel,h in C['source_hashes'].items():assert sha(P/rel)==h,rel
# Preserve every source context that supplies a hardlink. Only this package becomes writable.
materialized=[]
for p in (P/'.lake/build').rglob('*'):
 if p.is_file() and p.stat().st_nlink>1:
  before=sha(p);tmp=p.with_name(p.name+'.owned-normal-copy');shutil.copy2(p,tmp);os.replace(tmp,p);assert sha(p)==before;materialized.append({'path':str(p.relative_to(P)),'sha256':before})
(O/'normal-materialized-imports-v1.json').write_text(json.dumps(materialized,indent=2)+'\n')
scheduler=P/'scripts/lake-serial-build.py';canonical=scheduler.read_text();(O/'canonical-lake-serial-build.py').write_text(canonical)
needle='                if rc != 0:\n                    archive_failed_attempt(out, m, mods[m], unit, c, rc, dt)\n'
assert needle in canonical
patched=canonical.replace(needle,needle+'                    raise RuntimeError(f"Stop at first failed normal-key module: {m} rc={rc}")\n')
scheduler.write_text(patched)
env=dict(os.environ)
for key in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(key,None)
env.update(PATH=str(Path(C['lean_executable']).parent)+':'+env['PATH'],FV_ROOT=str(P),FV_MEMCAP='12G',LAKE_CACHE_DIR=str(OLD/'package/.lake/ci-cache'),LAKE_ARTIFACT_CACHE='true',LAKE_RESTORE_ARTIFACTS='true',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',CARGO_BUILD_JOBS='2',PYTHONDONTWRITEBYTECODE='1')
modules=(O/'normal-provider-targets.txt').read_text().splitlines();logs=O/'normal-providers-v1';logs.mkdir();cmd=['python3',str(scheduler),'--root',str(P),'--out',str(logs),'--budget','12G','--max-jobs','1','--min-cap','12G','--default-cap','12G','--max-cap','12G','--heavy','16G','--no-dedup',*modules]
with (O/'normal-scheduler-v1.log').open('w') as log:
 process=subprocess.Popen(cmd,cwd=P,env=env,stdout=log,stderr=subprocess.STDOUT);observed={}
 while process.poll() is None:
  try:
   for child in psutil.Process(process.pid).children(recursive=True):
    if child.name()=='lean':
     args=child.cmdline();assert '-j2' in args,('Unbounded Lean thread command',args)
     item=observed.setdefault(str(child.pid),{'command':args,'max_threads':0});item['max_threads']=max(item['max_threads'],child.num_threads())
  except (psutil.NoSuchProcess,psutil.AccessDenied):pass
  time.sleep(1)
(O/'normal-thread-observations-v1.json').write_text(json.dumps(observed,indent=2)+'\n')
if process.returncode:
 (O/'normal-providers-state-v1.json').write_text(json.dumps({'status':'stopped_at_first_failure','exit':process.returncode,'log_sha256':sha(O/'normal-scheduler-v1.log'),'full_goal_complete':False},indent=2)+'\n');raise SystemExit(process.returncode)
# Lake's own completed scheduler already runs the final no-build source-key check.
outputs={}
for mod in modules:
 stem=P/'.lake/build/lib/lean'/mod.replace('.','/');assert Path(str(stem)+'.trace').exists(),mod
 outputs[mod]={suf:sha(str(stem)+suf) for suf in ['.olean','.olean.private','.olean.server','.ilean','.trace'] if Path(str(stem)+suf).exists()}
result={'status':'passed','joint_tree':C['joint_tree'],'source_hashes':C['source_hashes'],'normal_project_targets':len(modules),'outputs':outputs,'normal_scheduler_log_sha256':sha(O/'normal-scheduler-v1.log'),'shared_cache':'Existing owned CI staging cache; no global cache writes','raw_successes_preserved_in_handoff':True,'explicit_j2':True,'full_goal_complete':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(O/'normal-providers-state-v1.json').write_text(json.dumps(result,indent=2)+'\n')
# Consumer harness accepts this real normal-key provider success without claiming every target rebuilt.
raw=json.loads((O/'provider-kernels-v1/progress.json').read_text())['records'];(O/'providers-state-v1.json').write_text(json.dumps({'status':'passed','joint_tree':C['joint_tree'],'provider_kind':'Real Lake normal-key scheduler','normal_provider_receipt_sha256':sha(O/'normal-providers-state-v1.json'),'records':raw,'full_goal_complete':False},indent=2)+'\n')
print('ALL CURRENT PROVIDERS PASS REAL NORMAL KEYS',len(modules),flush=True)
lock.close()
raise SystemExit(subprocess.call(['python3',str(O/'run-consumers-v1.py'),'--attempt','current-head-normal-v1'],env=dict(env,WORKER_O_PROOF_SLOT_GRANTED='892-joint-12G')))
