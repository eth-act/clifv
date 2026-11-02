from pathlib import Path
import datetime,fcntl,hashlib,json,os,psutil,re,select,signal,subprocess,sys,time
D=Path(__file__).resolve().parent;E=D.parent;P=E/'892-joint-current-context-v2/package';Q=E/'513-shared-gate-queue-v5';R=E/'broad-two-job-scheduling-proposal-v1';B=Path('/home/lee/clifv');pid=1713178
lock=(D/'owner.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);assert not (D/'state.json').exists()
proc=psutil.Process(pid);birth=proc.create_time();assert str(R/'lake-serial-build-drain.py') in proc.cmdline();assert proc.status()!=psutil.STATUS_STOPPED
inventory=json.loads((E/'fence-w-provider-readiness-v2/reviewable-summary-v2.json').read_text());missing=set(inventory['complete_missing_broad_closure']);assert len(missing)==18
roots=['FV.E2E.RegLevelWrites','FV.E2E.DeadCleanupRealizesW','FV.E2E.DeadCleanupRegLevelW'];dag={};hashes={};order=[]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(2**20),b''):h.update(block)
 return h.hexdigest()
def visit(n):
 if n in dag:return
 p=P/(n.replace('.','/')+'.lean');text=p.read_text();dag[n]=[x for x in re.findall(r'^import\s+([\w.]+)',text,re.M) if x.startswith(('FV.','FVTest.'))];hashes[n]=sha(p)
 for x in dag[n]:visit(x)
 order.append(n)
for n in roots:visit(n)
assert len(dag)==248 and missing.issubset(dag)
ready=[n for n in order if n not in missing];assert len(ready)==230
scope=Path(f'/sys/fs/cgroup/user.slice/user-{os.getuid()}.slice/user@{os.getuid()}.service/clifv.slice');assert scope.is_dir()
state={'status':'waiting_for_natural_boundary','owner':os.getpid(),'owner_birth':psutil.Process().create_time(),'scheduler':pid,'scheduler_birth':birth,'scope_parent':str(scope),'source_sha256':hashes,'missing_order':[n for n in order if n in missing],'records':[],'signals_to_compilers':[],'same_controller_resumed':False,'budget':'sole broad12GiB slot; sequential targets','full_goal_complete':False}
def save():
 tmp=D/'state.tmp';tmp.write_text(json.dumps(state,indent=2)+'\n');os.replace(tmp,D/'state.json')
def live(p):
 try:return p.is_running() and p.status()!=psutil.STATUS_ZOMBIE
 except psutil.NoSuchProcess:return False
def wait(p):
 try:fd=os.pidfd_open(p.pid)
 except ProcessLookupError:return
 try:select.select([fd],[],[])
 finally:os.close(fd)
def busy():
 for f in scope.glob('worker-o-wprio-v1-*.scope/cgroup.procs'):
  try:
   if f.read_text().strip():return True
  except FileNotFoundError:pass
 return False
save();subprocess.run(['ai-coord','watch','--label','fence-w-priority-resume-guard-v1','--','python3',str(D/'guard-v1.py')],cwd=B,check=True)
for _ in range(100):
 if (D/'guard-armed.json').exists():break
 time.sleep(.1)
else:raise RuntimeError('Independent resume guard did not arm')
paused=False
signal.signal(signal.SIGTERM,lambda *_:sys.exit(143))
try:
 initial=[p for p in proc.children() if live(p)];assert initial
 state['boundary_jobs']=[{'pid':p.pid,'args':p.cmdline()} for p in initial];save()
 for p in initial:wait(p)
 assert proc.is_running() and proc.create_time()==birth
 os.kill(pid,signal.SIGSTOP);paused=True;state['controller_paused']=True;save()
 # Drain a boundary launch race naturally. The stopped controller cannot start more work.
 while True:
  children=[p for p in proc.children(recursive=True) if live(p)]
  if not children:break
  for p in children:wait(p)
 assert proc.status()==psutil.STATUS_STOPPED
 for f in scope.glob(f'fvb-{pid}-*.scope/cgroup.procs'):
  try:assert not f.read_text().strip(),str(f)
  except FileNotFoundError:pass
 sys.path.insert(0,str(Q));from preflight import check
 check(str(P),str(Q/'release.json'),'combined')
 assert all(sha(P/(n.replace('.','/')+'.lean'))==v for n,v in hashes.items())
 preserved={}
 for n in ready:
  stem=Path(n.replace('.','/'))
  for area in ['lib/lean','ir']:
   p=P/'.lake/build'/area/stem
   for f in p.parent.glob(p.name+'.*'):
    if f.is_file():preserved[str(f.relative_to(P))]=sha(f)
 (D/'preserved230outputs.json').write_text(json.dumps(preserved,indent=2)+'\n')
 env=psutil.Process(1713176).environ();env.update(FV_MEMCAP='12G',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LEAN_NUM_THREADS='2')
 def run(label,args):
  env.update(FV_MEMCAP_UNIT='worker-o-wprio-v1-'+label,FV_MEMCAP_STATS=str(D/(label+'.mem')))
  with (D/(label+'.log')).open('w') as out:rc=subprocess.call([str(P/'scripts/memcap.sh'),'lake',*args],cwd=P,env=env,stdout=out,stderr=subprocess.STDOUT)
  state['records'].append({'label':label,'exit':rc,'log_sha256':sha(D/(label+'.log')),'memory':(D/(label+'.mem')).read_text() if (D/(label+'.mem')).exists() else None});save();assert rc==0,(label,rc)
 run('ready230',['build','--no-build',*ready])
 state['status']='building_priority_providers';save()
 for i,n in enumerate(state['missing_order']):
  run('deps-'+str(i),['build','--no-build',*dag[n]])
  run('leaf-'+str(i),['build',n])
 run('complete248',['build','--no-build',*order])
 assert all(sha(P/n)==h for n,h in preserved.items()),'A prior normal output changed; inspect exact context'
 check(str(P),str(Q/'release.json'),'combined');state['status']='passed';state['prior230outputs_exact']=True;save();print('W priority batch passed18providers and complete248normal',flush=True)
except BaseException as exc:
 state.update(status='failed_inspect_exact_diagnostics',error=repr(exc));save();raise
finally:
 if paused:
  while busy():time.sleep(1)
  assert psutil.Process(pid).create_time()==birth
  os.kill(pid,signal.SIGCONT);state['same_controller_resumed']=True;state['resume_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save();print('Resumed original scheduler',pid,flush=True)
