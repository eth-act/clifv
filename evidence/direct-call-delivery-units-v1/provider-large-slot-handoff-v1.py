from pathlib import Path
import datetime,fcntl,json,os,psutil,signal,subprocess,time
D=Path(__file__).resolve().parent;E=D.parent;S=json.loads((D/'current-foundation-snapshot-v1.json').read_text());P=Path(S['package']);L=D/'provider-large-slot-v1';L.mkdir();lock=(D/'current-gate.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='foundation-priority-12G';pid=326832;proc=psutil.Process(pid);birth=proc.create_time();args=proc.cmdline();assert args[0].endswith('python3') and args[1].endswith('/scripts/lake-serial-build.py') and '--max-jobs' in args and str(E/'892-joint-current-context-v2/package') in args
observer=psutil.Process(456502);assert any('892-same-normal-observer-and-consumers-v5' in a for a in observer.cmdline());assert proc.status() not in ['zombie','stopped']
state={'status':'handoff_in_progress','scheduler':pid,'scheduler_birth':birth,'scheduler_args':args,'observer':observer.pid,'signals_to_compilers':[],'original_proof_unchanged':True,'normal_provider':'FV.Backend.Proof.StockSourceCallWitness','cap':'12G','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
def save(): (L/'state.json').write_text(json.dumps(state,indent=2)+'\n')
paused=False
try:
 # Only the scheduler controller stops. Its separate compiler process continues normally.
 os.kill(pid,signal.SIGSTOP);paused=True;state['controller_paused']=True;state['children_at_pause']=[{'pid':p.pid,'args':p.cmdline()} for p in proc.children(recursive=True) if p.status()!='zombie'];save()
 while True:
  assert proc.create_time()==birth and proc.status()=='stopped'
  children=[]
  for p in proc.children(recursive=True):
   try:
    if p.status()!='zombie':children.append({'pid':p.pid,'args':p.cmdline()})
   except psutil.NoSuchProcess:pass
  if not children:break
  time.sleep(1)
 state['all_children_finished_normally_before_slot']=True;state['slot_start_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save();print('Controller stopped; all original children finished; assigning existing12GiB slot',flush=True)
 env=dict(os.environ)
 for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(k,None)
 env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(P),FV_MEMCAP='12G',FV_MEMCAP_UNIT='worker-o-foundation-source-witness-12g-v1',FV_MEMCAP_STATS=str(L/'scope.mem'),LAKE_CACHE_DIR=str(E/'892-current-main-context-v1/package/.lake/ci-cache'),LAKE_ARTIFACT_CACHE='true',LAKE_RESTORE_ARTIFACTS='true',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1')
 with (L/'kernel.log').open('w') as out:rc=subprocess.call(['/home/lee/clifv/.worktrees/stock-extending-production-20261031/scripts/memcap.sh','lake','build','FV.Backend.Proof.StockSourceCallWitness'],cwd=P,env=env,stdout=out,stderr=subprocess.STDOUT)
 state.update(status='passed' if rc==0 else 'failed',exit=rc,memstats=(L/'scope.mem').read_text() if (L/'scope.mem').exists() else None);save();print('Unchanged current-normal witness exit',rc,flush=True)
finally:
 if paused:
  assert psutil.Process(pid).create_time()==birth
  os.kill(pid,signal.SIGCONT);state['same_controller_resumed']=True;state['resume_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save();print('Same scheduler resumed',pid,flush=True)
lock.close()
assert state['status']=='passed','Inspect exact diagnostic and resource evidence before another action'
