"""Observe the existing healthy normal scheduler after its original observer exited."""
from pathlib import Path
import json,psutil,subprocess,os,time,hashlib,fcntl,re,datetime
O=Path(__file__).resolve().parent;C=json.loads((O/'context.json').read_text());P=Path(C['package']);scheduler=326832;process=psutil.Process(scheduler);birth=process.create_time();lock=(O/'kernel-owner.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='892-joint-12G';records={};races=0;policy=[];last_save=0;exit_status=None
while True:
 try:
  process=psutil.Process(scheduler)
  if process.create_time()!=birth:break
  if process.status()==psutil.STATUS_ZOMBIE:
   stat=Path(f'/proc/{scheduler}/stat').read_text().rsplit(')',1)[1].split();exit_status=int(stat[49]);break
 except psutil.NoSuchProcess:break
 for child in process.children(recursive=True):
  try:
   if child.status()==psutil.STATUS_ZOMBIE or child.name()!='lean':continue
   args=child.cmdline()
   if not args:races+=1;continue
   if not child.is_running() or child.status()==psutil.STATUS_ZOMBIE:continue
   if '-j2' not in args:policy.append({'pid':child.pid,'command':args});continue
   rec=records.setdefault(str(child.pid),{'command':args,'max_threads':0});rec['max_threads']=max(rec['max_threads'],child.num_threads())
  except (psutil.NoSuchProcess,psutil.ZombieProcess,psutil.AccessDenied):races+=1
 if time.monotonic()-last_save>10:
  (O/'normal-observer-v5-progress.json').write_text(json.dumps({'scheduler':scheduler,'birth':birth,'status':'observing_same_live_job','empty_or_vanished_process_observations':races,'records':records,'policy_issues':policy},indent=2)+'\n');last_save=time.monotonic()
 time.sleep(1)
log=O/'normal-scheduler-v4.log';text=log.read_text();end=re.findall(r'END (\d+)/(\d+) ok, (\d+) built',text)
assert end and end[-1][0]==end[-1][1]==str(C['project_modules']),('Scheduler did not report complete normal success',text[-1800:])
assert exit_status in [None,0],('Observed scheduler nonzeroexit',exit_status)
assert not policy,('Review actual live thread-policy issues',policy)
env=dict(os.environ)
for key in ['FV_MEMCAP_OFF','FV_LAKE_CACHE','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(key,None)
env.update(PATH=str(Path(C['lean_executable']).parent)+':'+env['PATH'],FV_ROOT=str(P),FV_MEMCAP='12G',FV_MEMCAP_UNIT='worker-o-892-observed-final-keys-v5',FV_MEMCAP_STATS=str(O/'normal-observer-final-keycheck-v5.mem'),LAKE_CACHE_DIR=str(O.parent/'892-current-main-context-v1/package/.lake/ci-cache'),LAKE_ARTIFACT_CACHE='true',LAKE_RESTORE_ARTIFACTS='true',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',PYTHONDONTWRITEBYTECODE='1')
modules=(O/'normal-provider-targets.txt').read_text().splitlines()
with (O/'normal-observer-final-keycheck-v5.log').open('w') as stream:rc=subprocess.call([str(P/'scripts/memcap.sh'),'lake','build','--no-build',*modules],cwd=P,env=env,stdout=stream,stderr=subprocess.STDOUT)
assert rc==0,'Inspect final actual no-build key check; no compiler was allowed'
def sha(f):return hashlib.sha256(Path(f).read_bytes()).hexdigest()
outputs={}
for mod in modules:
 stem=P/'.lake/build/lib/lean'/mod.replace('.','/');assert Path(str(stem)+'.trace').exists();outputs[mod]={suffix:sha(str(stem)+suffix) for suffix in ['.olean','.olean.private','.olean.server','.ilean','.trace'] if Path(str(stem)+suffix).exists()}
result={'status':'passed','joint_tree':C['joint_tree'],'current_base':C['base'],'source_hashes':C['source_hashes'],'normal_project_targets':len(modules),'outputs':outputs,'same_scheduler_pid':scheduler,'scheduler_end':end[-1],'observed_scheduler_raw_exit_status':exit_status,'scheduler_returncode_not_fabricated':True,'authoritative_final_no_build_exit':rc,'new_compiler_started_by_observer':False,'previous_observer_failure':'Emptycmdline process-exit race; original log preserved','thread_observations':records,'empty_or_vanished_process_observations':races,'full_goal_complete':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(O/'normal-providers-state-v1.json').write_text(json.dumps(result,indent=2)+'\n');(O/'providers-state-v1.json').write_text(json.dumps({'status':'passed','joint_tree':C['joint_tree'],'provider_kind':'RealLake normalkeys plus authoritative final no-buildcheck','normal_provider_receipt_sha256':sha(O/'normal-providers-state-v1.json'),'records':[],'full_goal_complete':False},indent=2)+'\n');print('SAME NORMAL SCHEDULER COMPLETED; ACTUAL FINAL NO-BUILD CHECK PASSED',len(modules),flush=True);lock.close()
raise SystemExit(subprocess.call(['python3',str(O/'run-consumers-v2.py'),'--attempt','current-head-normal-v1'],env=dict(env,WORKER_O_PROOF_SLOT_GRANTED='892-joint-12G')))
