from pathlib import Path
import json,os,psutil,subprocess,time,datetime,fcntl
O=Path(__file__).resolve().parent;owner=4163534
assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='892-joint-12G'
process=psutil.Process(owner);birth=process.create_time()
while True:
 try:
  process=psutil.Process(owner)
  if process.create_time()!=birth or process.status()==psutil.STATUS_ZOMBIE:break
 except psutil.NoSuchProcess:break
 time.sleep(5)
result=O/'providers-state-v1.json'
if not result.exists() or json.loads(result.read_text()).get('status')!='passed':
 (O/'consumer-continuation-stopped-v1.json').write_text(json.dumps({'status':'stopped','reason':'Provider owner ended without successful gate','no_consumer_run':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},indent=2)+'\n');raise SystemExit(1)
with (O/'kernel-owner.lock').open('a+') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
# The provider is gone. The consumer harness holds its own exclusive writer lock.
(O/'consumer-slot-handoff-v1.json').write_text(json.dumps({'status':'provider_to_consumer','provider_owner':owner,'provider_exit_confirmed':True,'slot':'same12GiB explicit-j2','no_new_worktree_cache':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},indent=2)+'\n')
print('Provider owner exited successfully; running actual consumers',flush=True)
raise SystemExit(subprocess.call(['python3',str(O/'run-consumers-v1.py'),'--attempt','current-head-v1'],env=dict(os.environ)))
