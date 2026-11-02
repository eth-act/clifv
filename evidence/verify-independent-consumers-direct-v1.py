from pathlib import Path
import datetime,fcntl,json,os,subprocess
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029';r=b/'.worktrees/stock-extending-production-20261031'
# The original broad proof owner holds the source view and waits on this exclusive resource lock.
lock=(e/'main870-cache-import.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
assert b'captured-symbolic-packet-after-importers-v1' in Path('/proc/3507911/cmdline').read_bytes()
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()
ready=json.loads((e/'post-importer-direct-dependency-readiness-v5.json').read_text());assert ready['status']=='ready' and ready['head']==head
assert subprocess.check_output(['git','status','--porcelain'],cwd=r,text=True)==''
env=dict(os.environ);env.update(json.loads((e/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None)
env.update(FV_ROOT=str(r),LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',FV_MEMCAP='1G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2')
with (e/'independent-consumers-direct-readiness-v1.log').open('w') as log:
 subprocess.run(['nice','-n','10',str(r/'scripts/memcap.sh'),'lake','build','--no-build',*ready['roots']],cwd=r,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
results=[]
groups=[['verify-return-pin-routed-packet-v1-early-v1.py'],['verify-sret-exec-result-bytes-v1-early-v1.py','verify-sret-exec-result-bytes-packet-v1-early-v1.py'],['verify-return-pin-checks-with-v1-early-v1.py','verify-return-pin-checks-packet-v1-early-v1.py']]
for group in groups:
 for name in group:
  print('START',name,flush=True)
  c=subprocess.run(['python3',str(e/name)],cwd=b,env=env)
  results.append(dict(script=name,returncode=c.returncode));print('DONE',name,'rc='+str(c.returncode),flush=True)
  if c.returncode:break
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()==head
receipt=dict(status='passed' if all(x['returncode']==0 for x in results) else 'inspect_failures',head=head,results=results,full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(e/'independent-consumers-direct-state-v1.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
assert receipt['status']=='passed','Inspect the individual logs. Preserve every independent successful gate.'
