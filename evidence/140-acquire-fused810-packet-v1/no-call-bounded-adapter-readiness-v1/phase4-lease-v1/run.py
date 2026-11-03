from common import *
import fcntl,subprocess,sys,signal
B=Path('/home/lee/clifv');lock=(D/'owner.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
assert not (D/'state.json').exists()
scope=Path(f'/sys/fs/cgroup/user.slice/user-{os.getuid()}.slice/user@{os.getuid()}.service/clifv.slice');assert scope.is_dir()
state={'status':'arming','owner':os.getpid(),'owner_birth':psutil.Process().create_time(),'scope_parent':str(scope),'allocation':'broad12/phase1_3/orchestration1','signals_to_compilers':[]}
save(D/'state.json',state)
child=None
signal.signal(signal.SIGTERM,lambda *_:sys.exit(143))
try:
 subprocess.run(['ai-coord','watch','--label','acquire810-phase4-config-and-share-restoration-phase4-v1','--','python3',str(D/'guard.py')],cwd=B,check=True)
 for _ in range(100):
  if (D/'guard-armed.json').exists():break
  time.sleep(.1)
 else:raise RuntimeError('Independent guard did not arm')
 state['status']='guarded_waiting_explicit_start';save(D/'state.json',state)
 while not (D/'start-approved.json').exists():
  if (D/'cancel.json').exists():raise RuntimeError('Cancelled before any consumer')
  time.sleep(.2)
 canonical=(D/'canonical-lakefile.toml').read_bytes();projected=(D/'projected-lakefile.toml').read_bytes();assert (F/'lakefile.toml').read_bytes()==canonical
 state['config_projection_planned']=True;save(D/'state.json',state)
 tmp=F/'.lakefile.projected-phase4-v1.toml';tmp.write_bytes(projected);os.replace(tmp,F/'lakefile.toml')
 state['config_projection_active']=True;save(D/'state.json',state)
 child=subprocess.Popen([sys.executable,str(D/'launch.py')],cwd=B,stdout=(D/'consumer-command.log').open('w'),stderr=subprocess.STDOUT)
 for _ in range(100):
  if (D/'consumer-identity.json').exists():break
  time.sleep(.1)
 else:raise RuntimeError('Consumer identity did not appear')
 state.update(status='running',consumer=json.loads((D/'consumer-identity.json').read_text()));save(D/'state.json',state)
 save(D/'permit.json',{'approved':True,'parent_proposal':'3b38b40190229785daaf06be488e068130b97055651b5a901664a884c75bf40c'})
 rc=child.wait();state.update(exit=rc,status='passed' if rc==0 else 'failed');save(D/'state.json',state)
 if rc:raise SystemExit(rc)
finally:
 if child is not None and child.poll() is None:
  if not (D/'permit.json').exists():save(D/'cancel.json',{'cancelled':True})
  child.wait()
 while busy(state):time.sleep(.2)
 restore('phase4 owner all-exit finally after all consumers and scopes exit')
