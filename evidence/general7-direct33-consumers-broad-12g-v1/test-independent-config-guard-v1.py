from pathlib import Path
import subprocess,os,signal,time,json,hashlib,shutil,psutil
D=Path(__file__).resolve().parent;T=D/'guard-exit-tests-v1';T.mkdir();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();records=[]
for case in ['owner_and_consumer_kill','normal_exit']:
 L=T/case;L.mkdir();G=L/'fake-G';G.mkdir();scope=L/'fake-cgroups';scope.mkdir();original=b'weakLeanArgs = ["-Dtest=false"]\n';(G/'lakefile.toml').write_bytes(original.replace(b'weakLeanArgs = [',b'weakLeanArgs = ["-j1",',1));(L/'original-G-lakefile.toml').write_bytes(original);(L/'config-restoration.json').write_text(json.dumps({'G':str(G),'original_sha256':hashlib.sha256(original).hexdigest()}));
 for name in ['guard.py','restore_config.py']:shutil.copyfile(D/name,L/name);assert sha(D/name)==sha(L/name)
 controller=subprocess.Popen(['python3','-c','import time; time.sleep(60)']);owner=subprocess.Popen(['python3','-c','import time; time.sleep(60)']);consumer=subprocess.Popen(['python3','-c','import time; time.sleep(60)']);guard=None
 try:
  cp=psutil.Process(controller.pid);op=psutil.Process(owner.pid);con=psutil.Process(consumer.pid)
  state={'owner':op.pid,'owner_birth':op.create_time(),'scheduler':cp.pid,'scheduler_birth':cp.create_time(),'scope_parent':str(scope),'same_controller_resumed':case=='normal_exit','config_plan_sha256':sha(L/'config-restoration.json')};(L/'state.json').write_text(json.dumps(state));(L/'consumer-identity.json').write_text(json.dumps({'pid':con.pid,'birth':con.create_time()}));group=scope/'worker-o-General7-consumer33-test.scope';group.mkdir();(group/'cgroup.procs').write_text(str(con.pid)+'\n' if case!='normal_exit' else '')
  if case!='normal_exit':os.kill(cp.pid,signal.SIGSTOP)
  with (L/'guard.log').open('w') as out:guard=subprocess.Popen(['python3',str(L/'guard.py')],stdout=out,stderr=subprocess.STDOUT)
  limit=time.monotonic()+5
  while not(L/'guard-armed.json').exists():
   assert time.monotonic()<limit and guard.poll() is None;time.sleep(.02)
  waited=False
  if case!='normal_exit':
   owner.kill();owner.wait();time.sleep(.15);assert (G/'lakefile.toml').read_bytes()!=original;assert cp.status()==psutil.STATUS_STOPPED;assert guard.poll() is None;waited=True;consumer.kill();consumer.wait();(group/'cgroup.procs').write_text('')
  assert guard.wait(timeout=10)==0;assert (G/'lakefile.toml').read_bytes()==original;assert cp.status() not in [psutil.STATUS_STOPPED,psutil.STATUS_ZOMBIE];r=json.loads((L/'guard-receipt.json').read_text());assert r['configuration_restoration']['original_config_restored'];records.append({'case':case,'guard_exit':0,'waited_for_consumer_and_cgroup_end':waited,'original_config_restored':True,'same_controller_running':True,'receipt_sha256':sha(L/'guard-receipt.json'),'fake_processes_only':True})
 finally:
  for p in [guard,owner,consumer,controller]:
   if p is not None and p.poll() is None:
    try:os.kill(p.pid,signal.SIGCONT)
    except ProcessLookupError:pass
    p.terminate();p.wait(timeout=10)
(T/'receipt.json').write_text(json.dumps({'status':'PASSED_INDEPENDENT_CONFIG_AND_SCHEDULER_EXIT_TESTS','records':records,'production_guard_sha256':sha(D/'guard.py'),'production_restorer_sha256':sha(D/'restore_config.py'),'production_sources_unmodified':True,'no_real_compiler_signalled':True},indent=2)+'\n');print(sha(T/'receipt.json'))
