from pathlib import Path
import json,psutil,os,signal,time,hashlib,subprocess,datetime
O=Path(__file__).resolve().parent;S=json.loads((O/'late-stage-exclusive-handoff-v1.json').read_text());C=json.loads((O/'context.json').read_text());P=Path(C['package']);OLD=O.parent/'892-current-main-context-v1';cmdpid=S['active_command'];scheduler=S['scheduler'];cache=OLD/'package/.lake/ci-cache'
assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='892-joint-12G'
def sha(path):
 h=hashlib.sha256()
 with Path(path).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
if cmdpid:
 while True:
  state=Path(f'/proc/{cmdpid}/stat').read_text().rsplit(')',1)[1].split()
  if state[0]=='Z':break
  time.sleep(1)
 assert int(state[49])==0,('Current normal Lake command failed',int(state[49]))
 module=S['active_command_argv'][-1];stem=P/'.lake/build/lib/lean'/module.replace('.','/');assert Path(str(stem)+'.trace').exists()
 S.update(last_module=module,last_module_exit=0,last_trace_sha256=sha(Path(str(stem)+'.trace')))
 S['last_outputs']={suffix:sha(Path(str(stem)+suffix)) for suffix in ['.olean','.ilean','.olean.private','.olean.server'] if Path(str(stem)+suffix).exists()}
 for suffix in ['log','mem','time']:
  f=O/'normal-providers-v2'/(module+'.'+suffix)
  if f.exists():S['last_'+suffix]={'sha256':sha(f),'text':f.read_text() if suffix=='mem' else None}
assert psutil.Process(scheduler).status()=='stopped';os.kill(scheduler,signal.SIGTERM);os.kill(scheduler,signal.SIGCONT)
for _ in range(300):
 try:
  p=psutil.Process(S['old_outer_controller'])
  if p.status()==psutil.STATUS_ZOMBIE:break
 except psutil.NoSuchProcess:break
 time.sleep(.1)
else:raise RuntimeError('Old normal owner did not release')
# Every owned-cache Lake reader/writer from the old provider is gone before native unstage.
for p in psutil.process_iter(['pid','name']):
 if p.info['name'] in ['lake','lake.orig','lean']:
  try:assert Path(p.cwd())!=P.resolve(),('Unexpected live ownedpackage reader/writer',p.pid)
  except (psutil.NoSuchProcess,psutil.AccessDenied):pass
recovery=json.loads((O/'late-ci-stage-recovery-v1.json').read_text());assert recovery['status']=='passed' and recovery['head']=='3a6719b44b0e6b38e24cd0de82655f93b78272a9'
assert subprocess.check_output(['git','show',recovery['head']+':lean-toolchain'],cwd='/home/lee/clifv')==(P/'lean-toolchain').read_bytes()
records=[];env=dict(os.environ)
for key in ['FV_MEMCAP_OFF','FV_LAKE_CACHE','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(key,None)
env.update(PATH=str(Path(C['lean_executable']).parent)+':'+env['PATH'],LAKE_CACHE_DIR=str(cache),LAKE_ARTIFACT_CACHE='true',LAKE_RESTORE_ARTIFACTS='true',FV_ROOT=str(P),FV_MEMCAP='1G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',PYTHONDONTWRITEBYTECODE='1')
memcap=P/'scripts/memcap.sh'
for i,entry in enumerate(recovery['records']):
 assert entry['producer']['status']=='completed' and entry['producer']['conclusion']=='success'
 assert entry['artifact']['workflow_run']['head_sha']==recovery['head']
 assert entry['artifact']['digest']=='sha256:'+entry['archive_sha256']
 stage=Path(entry['stage'])
 for rel,h in entry['mapping_hashes'].items():assert sha(stage/rel)==h
 assert len(list(stage.rglob('outputs.jsonl')))==1
 lines=(stage/'outputs.jsonl').read_text().splitlines();assert json.loads(lines[0])=='2026-03-17'
 for line in lines[1:]:
  key,value=json.loads(line);assert isinstance(key,str) and isinstance(value,str);assert '/' not in value and (stage/value).is_file()
 log=O/('exclusive-unstage-'+str(i)+'.log');stats=log.with_suffix('.mem');child=dict(env,FV_MEMCAP_STATS=str(stats),FV_MEMCAP_UNIT='worker-o-892-exclusive-unstage-v1-'+str(i))
 with log.open('w') as out:rc=subprocess.call([str(memcap),'lake','cache','unstage',str(stage)],cwd=P,env=child,stdout=out,stderr=subprocess.STDOUT)
 records.append({'stage':str(stage),'exit':rc,'overwrite':False,'mapping_hashes':entry['mapping_hashes'],'producer':entry['producer']['id'],'artifact':entry['artifact']['id'],'archive_sha256':entry['archive_sha256'],'log_sha256':sha(log),'memstats':stats.read_text() if stats.exists() else None})
 assert rc==0,('Exclusive native unstage failed',rc,str(log))
S.update(status='native_unstage_passed_old_normal_owner_released',unstage=records,cache_scope=str(cache),no_global_cache_writes=True,no_live_import_library_writes=True,old_scheduler_exit='Planned SIGTERM after current Lake command exit0; not a compiler failure',utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(O/'late-stage-exclusive-handoff-v1.json').write_text(json.dumps(S,indent=2)+'\n')
prior=O/'normal-providers-state-v1.json'
if prior.exists():(O/'normal-providers-state-attempt-v2.json').write_bytes(prior.read_bytes())
print('EXCLUSIVE NATIVE UNSTAGE PASSED; resume normal keys; lastmodule',S.get('last_module'),flush=True)
raise SystemExit(subprocess.call(['python3',str(O/'run-normal-providers-v3.py')],env=dict(os.environ)))
