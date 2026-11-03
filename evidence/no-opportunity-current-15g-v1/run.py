from pathlib import Path
import ast,datetime,fcntl,hashlib,json,os,psutil,re,select,signal,subprocess,sys,time
D=Path(__file__).resolve().parent;E=D.parent;B=Path('/home/lee/clifv');N=E/'stock-current-main-full-gate-v6';P=E/'892-joint-current-context-v2/package';MOD='FV.Backend.Proof.StockNoOpportunityTable';KEY='0588c5a3979a99d1'
lock=(D/'owner.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);assert not (D/'state.json').exists()
ns=json.loads((N/'execution-state.json').read_text());assert ns['status']=='running_normal';pid=ns['active_scheduler'];proc=psutil.Process(pid);birth=proc.create_time();assert str(E/'broad-two-job-scheduling-proposal-v1/lake-serial-build-drain.py') in proc.cmdline()
scope=Path(f'/sys/fs/cgroup/user.slice/user-{os.getuid()}.slice/user@{os.getuid()}.service/clifv.slice');assert scope.is_dir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def live(p):
 try:return p.is_running() and p.status()!=psutil.STATUS_ZOMBIE
 except psutil.NoSuchProcess:return False
def wait(p):
 try:fd=os.pidfd_open(p.pid)
 except ProcessLookupError:return
 try:select.select([fd],[],[])
 finally:os.close(fd)
dag={};hashes={};order=[]
def visit(m):
 if m in dag:return
 p=P/(m.replace('.','/')+'.lean');assert p.is_file(),p
 dag[m]=[x for x in re.findall(r'^import\s+([\w.]+)',p.read_text(),re.M) if x.startswith(('FV.','FVTest.'))];hashes[m]=sha(p)
 for dep in dag[m]:visit(dep)
 order.append(m)
visit(MOD);ready=[m for m in order if m!=MOD]
state={'status':'arming_guard','owner':os.getpid(),'owner_birth':psutil.Process().create_time(),'scheduler':pid,'scheduler_birth':birth,'scope_parent':str(scope),'target':MOD,'expected_key':KEY,'budget':'15GiB sole compiler; total O16GiB','worker_releases':{'source_guarantees':'2GiB explicitly released; no compiler/verifier','investigate_513':'1GiB explicitly released; no compiler/verifier'},'source_hashes':hashes,'records':[],'signals_to_compilers':[],'same_controller_resumed':False,'full_goal_complete':False}
def save():
 state['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();tmp=D/'state.tmp';tmp.write_text(json.dumps(state,indent=2)+'\n');os.replace(tmp,D/'state.json')
def busy():
 for f in scope.glob('worker-o-noopp15-*.scope/cgroup.procs'):
  try:
   if f.read_text().strip():return True
  except FileNotFoundError:pass
 return False
save();subprocess.run(['ai-coord','watch','--label','no-opportunity-current-resume-guard-v1','--','python3',str(D/'guard.py')],cwd=B,check=True)
for unused in range(100):
 if (D/'guard-armed.json').exists():break
 time.sleep(.1)
else:raise RuntimeError('Independent guard did not arm')
paused=False;signal.signal(signal.SIGTERM,lambda *_:sys.exit(143))
try:
 initial=[p for p in proc.children() if live(p)];state['boundary_jobs']=[{'pid':p.pid,'args':p.cmdline()} for p in initial];state['status']='waiting_natural_boundary';save()
 for child in initial:wait(child)
 assert proc.is_running() and proc.create_time()==birth
 os.kill(pid,signal.SIGSTOP);paused=True;state['controller_paused']=True;save()
 while True:
  direct=[p for p in proc.children() if live(p)]
  queries=[]
  for child in direct:
   try:
    args=child.cmdline()
    if '--no-build' in args or 'query' in args:queries.append(child)
   except psutil.NoSuchProcess:pass
  if queries:
   os.kill(pid,signal.SIGCONT);paused=False
   for child in queries:wait(child)
   os.kill(pid,signal.SIGSTOP);paused=True
   continue
  children=[p for p in proc.children(recursive=True) if live(p)]
  if not children:break
  for child in children:wait(child)
 assert proc.status()==psutil.STATUS_STOPPED
 for f in scope.glob(f'fvb-{pid}-*.scope/cgroup.procs'):
  try:assert not f.read_text().strip(),str(f)
  except FileNotFoundError:pass
 sys.path.insert(0,str(N));from preflight import check
 check(P,N/'release.json');assert all(sha(P/(m.replace('.','/')+'.lean'))==h for m,h in hashes.items())
 env=proc.environ()
 for k in ['FV_MEMCAP_OFF','FV_LAKE_CACHE']:env.pop(k,None)
 env.update(FV_MEMCAP='15G',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LEAN_NUM_THREADS='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false')
 def run(label,args):
  env.update(FV_MEMCAP_UNIT='worker-o-noopp15-'+label,FV_MEMCAP_STATS=str(D/(label+'.mem')))
  with (D/(label+'.log')).open('w') as out:rc=subprocess.call([str(P/'scripts/memcap.sh'),'lake',*args],cwd=P,env=env,stdout=out,stderr=subprocess.STDOUT)
  rec={'label':label,'argv':['lake',*args],'exit':rc,'log_sha256':sha(D/(label+'.log')),'memory':(D/(label+'.mem')).read_text() if (D/(label+'.mem')).exists() else None};state['records'].append(rec);save();assert rc==0,(label,rc)
 run('dependencies',['build','--no-build',*ready])
 run('key-before',['query','--no-build','+'+MOD+':depHash'])
 keys=re.findall(r'^[0-9a-f]{16}$',(D/'key-before.log').read_text(),re.M);assert keys and keys[-1]==KEY,keys
 prior={}
 for m in ready:
  stem=P/'.lake/build/lib/lean'/Path(m.replace('.','/'))
  for suffix in ['.trace','.olean','.ilean']:
   p=Path(str(stem)+suffix)
   if p.exists():prior[str(p.relative_to(P))]=sha(p)
 (D/'preserved-dependencies.json').write_text(json.dumps(prior,indent=2)+'\n')
 state['status']='compiling_exact_current_NoOpportunityTable';save()
 run('leaf',['build','+'+MOD+':leanArts'])
 run('complete',['build','--no-build',*order])
 trace=P/'.lake/build/lib/lean/FV/Backend/Proof/StockNoOpportunityTable.trace';t=json.loads(trace.read_text());assert t.get('synthetic') is not True and t.get('inputs');assert t['depHash']==KEY,t['depHash']
 assert all(sha(P/name)==h for name,h in prior.items()),'A dependency output changed'
 check(P,N/'release.json');state['status']='passed';state['native_key']=t['depHash'];state['native_trace_sha256']=sha(trace);state['target_output_sha256']=sha(trace.with_suffix('.olean'));save();print('Exact current NoOpportunityTable passed',KEY,flush=True)
except BaseException as exc:
 state.update(status='failed_inspect_exact_diagnostic',error=repr(exc));save();raise
finally:
 if paused:
  while busy():time.sleep(1)
  assert psutil.Process(pid).create_time()==birth
  os.kill(pid,signal.SIGCONT);state['same_controller_resumed']=True;state['resume_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save();print('Resumed original normal scheduler',pid,flush=True)
