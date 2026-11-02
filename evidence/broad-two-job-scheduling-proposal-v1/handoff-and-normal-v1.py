from pathlib import Path
import atexit,fcntl,datetime,hashlib,json,math,os,re,select,signal,subprocess,sys,time,psutil
R=Path(__file__).resolve().parent;E=R.parent;Q=E/'513-shared-gate-queue-v5';P=E/'892-joint-current-context-v2/package'
OLD=1496812;OLD_PHASE=1496809;OLD_WATCH=1496808
S=Q/'runs/combined/normal/v5-initial/scheduler'
lock=(R/'handoff-owner.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
assert not (R/'handoff-state-v1.json').exists(),'Inspect the existing owner before retry'
state={'status':'waiting_for_natural_module_exit','old_scheduler':OLD,'old_phase':OLD_PHASE,'old_watcher':OLD_WATCH,'compiler_signals_sent':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
def save():
 (R/'handoff-state-v1.json').write_text(json.dumps(state,indent=2)+'\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def live(p):
 try:return p.is_running() and p.status()!=psutil.STATUS_ZOMBIE
 except psutil.NoSuchProcess:return False
def wait_exit(p):
 fd=os.pidfd_open(p.pid)
 try:select.select([fd],[],[])
 finally:os.close(fd)
def job(p):
 a=p.cmdline();assert 'lake-time.py' in ' '.join(a),a
 m=a[-1];assert (S/(m+'.time')).resolve() in [Path(x).resolve() for x in a if x.endswith('.time')]
 return m
def completed(m):
 t=(S/(m+'.time')).read_text();assert re.search(r'Exit status: 0\s*$',t),('Module did not finish successfully',m,t)
 paths=[S/(m+'.'+suffix) for suffix in ['time','log','mem']]
 return {'module':m,'files':{str(p):sha(p) for p in paths if p.exists()},'time_text':t,'memory_text':(S/(m+'.mem')).read_text()}
def restore_old_controller():
 try:
  old=psutil.Process(OLD)
  if old.status()==psutil.STATUS_STOPPED and str(Q/'helpers/lake-serial-build-stopfirst.py') in old.cmdline():
   os.kill(OLD,signal.SIGCONT)
 except psutil.NoSuchProcess:pass
atexit.register(restore_old_controller)
signal.signal(signal.SIGTERM,lambda *_:sys.exit(143))
policy=json.loads((R/'proposal.json').read_text());assert policy['handoff_approved'];assert sha(R/'lake-serial-build-drain.py')==policy['helper_sha256'];assert sha(R/'run-normal-two-job.py')==policy['runner_sha256']
proc=psutil.Process(OLD);assert str(Q/'helpers/lake-serial-build-stopfirst.py') in proc.cmdline()
children=[p for p in proc.children() if live(p)];assert len(children)==1,[(p.pid,p.cmdline()) for p in children]
first=children[0];first_module=job(first);state['first_job']={'pid':first.pid,'module':first_module};save();print('Waiting for normal module exit:',first_module,first.pid,flush=True)
wait_exit(first)
# Stop only the idle controller after its module job exits. A launch race is drained below.
os.kill(OLD,signal.SIGSTOP)
for _ in range(50):
 if proc.status()==psutil.STATUS_STOPPED:break
 time.sleep(.02)
assert proc.status()==psutil.STATUS_STOPPED
finished=[completed(first_module)]
for p in proc.children():
 if live(p):
  m=job(p);print('Drain a boundary launch race without signals:',m,p.pid,flush=True);wait_exit(p);finished.append(completed(m))
assert not any(live(p) for p in proc.children(recursive=True))
cgroup=Path(f'/sys/fs/cgroup/user.slice/user-{os.getuid()}.slice/user@{os.getuid()}.service/clifv.slice')
for f in cgroup.glob(f'fvb-{OLD}-*.scope/cgroup.procs'):assert not f.read_text().strip(),str(f)
state.update(status='controller_paused_all_module_jobs_exited_normally',completed_at_boundary=finished,no_live_compiler_or_artifact_writer=True);save()
# Preserve the exact normal traces before the replacement can write any output.
traces={str(p.relative_to(P)):sha(p) for p in (P/'.lake/build').rglob('*.trace') if p.is_file()}
(R/'normal-traces-before-handoff-v1.json').write_text(json.dumps(traces,indent=2)+'\n');state['preserved_trace_count']=len(traces)
# The profile fields are MiB, as load_profile multiplies them by 1024**2.
profiles=[P/'scripts/lake-module-peaks.tsv',P/'.lake/lake-module-peaks.tsv'];rows={}
for p in profiles:
 for l in p.read_text().splitlines():
  if l.startswith('#'):continue
  f=l.split('\t')
  if len(f)<3:continue
  prior=rows.get(f[0],(0,0));rows[f[0]]=(max(prior[0],int(f[1])),max(prior[1],float(f[2])))
for r in finished:
 rss=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',r['time_text']).group(1));peak=int(re.search(r'peak (\d+)',r['memory_text']).group(1));seconds=float(re.search(r'Elapsed seconds: ([0-9.]+)',r['time_text']).group(1));prior=rows.get(r['module'],(0,0));rows[r['module']]=(max(prior[0],math.ceil(rss/1024),math.ceil(peak/2**20)),max(prior[1],seconds))
(R/'conservative-peaks.tsv').write_text('# Maximum real cold/local recorded peaks in MiB.\n'+'\n'.join(f'{n}\t{v[0]}\t{v[1]}' for n,v in sorted(rows.items()))+'\n')
policy['profile_inputs']={str(p):sha(p) for p in profiles};policy['profile_sha256']=sha(R/'conservative-peaks.tsv');policy['profile_units_verified']='MiB';policy['boundary_harvest']=finished;(R/'proposal.json').write_text(json.dumps(policy,indent=2)+'\n')
# The old helper can now terminate without a live child. No compiler receives a signal.
os.kill(OLD,signal.SIGTERM);os.kill(OLD,signal.SIGCONT)
for pid in [OLD,OLD_PHASE]:
 try:
  p=psutil.Process(pid)
  if live(p):wait_exit(p)
 except psutil.NoSuchProcess:pass
state.update(status='old_controller_released_expected_SIGTERM',old_module_jobs_success=True,old_parent_watcher_exit_expected=True);save()
# Recheck the immutable source/release guards before starting the same normal queue.
argv=[sys.executable,str(R/'run-normal-two-job.py'),'--root',str(P),'--release',str(Q/'release.json'),'--stage','combined','--phase','normal','--attempt','v5-twojob-v1']
env=dict(os.environ,WORKER_O_FULL_GATE_GRANTED='513-production-shared',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2')
child=subprocess.Popen(argv,cwd='/home/lee/clifv',env=env)
state.update(status='replacement_normal_runner_started',new_runner=child.pid,new_attempt='v5-twojob-v1',profile_sha256=policy['profile_sha256'],helper_sha256=policy['helper_sha256']);save();print('Replacement runner:',child.pid,flush=True)
new_scheduler=None;samples=0;peak=0;max_caps=0
while child.poll() is None:
 if new_scheduler is None:
  try:descendants=psutil.Process(child.pid).children(recursive=True)
  except psutil.NoSuchProcess:descendants=[]
  for p in descendants:
   try:
    if str(R/'lake-serial-build-drain.py') in p.cmdline():new_scheduler=p.pid;state['new_scheduler']=new_scheduler;save();print('Replacement scheduler:',new_scheduler,flush=True);break
   except psutil.NoSuchProcess:pass
 if new_scheduler:
  groups=[]
  for d in cgroup.glob(f'fvb-{new_scheduler}-*.scope'):
   try:
    if not (d/'cgroup.procs').read_text().strip():continue
    caps=(d/'memory.max').read_text().strip();assert caps!='max'
    groups.append({'scope':d.name,'cap':int(caps),'current':int((d/'memory.current').read_text()),'peak':int((d/'memory.peak').read_text())})
   except FileNotFoundError:pass
  caps=sum(x['cap'] for x in groups);current=sum(x['current'] for x in groups);peak=max(peak,current);max_caps=max(max_caps,caps)
  if caps>12*2**30:
   state['aggregate_cap_violation']=groups;save();raise AssertionError('Actual scheduler caps exceed the approved12GiB budget')
  if groups:
   with (R/'aggregate-memory-samples-v1.jsonl').open('a') as f:f.write(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'active_caps':caps,'current':current,'groups':groups})+'\n')
   samples+=1
 time.sleep(2)
state.update(status='replacement_normal_passed' if child.returncode==0 else 'replacement_normal_failed_inspect_diagnostics',exit=child.returncode,aggregate_sample_peak_bytes=peak,aggregate_max_active_caps_bytes=max_caps,aggregate_samples=samples);save();print(json.dumps(state),flush=True);sys.exit(child.returncode)
