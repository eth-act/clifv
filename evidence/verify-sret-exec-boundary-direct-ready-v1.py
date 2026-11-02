from pathlib import Path
import fcntl,hashlib,json,os,subprocess
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029';r=b/'.worktrees/stock-extending-production-20261031'
lock=(e/'main870-cache-import.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
assert b'captured-symbolic-packet-after-importers-v1' in Path('/proc/3507911/cmdline').read_bytes()
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip();assert head=='a4c0726d46c5908b4ac06cf797ee939af8644703'
assert subprocess.check_output(['git','status','--porcelain'],cwd=r,text=True)==''
env=dict(os.environ);env.update(json.loads((e/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None)
env.update(FV_ROOT=str(r),LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',FV_MEMCAP='1G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2')
with (e/'sret-exec-boundary-direct-readiness-v1.log').open('w') as log:
 subprocess.run(['nice','-n','10',str(r/'scripts/memcap.sh'),'lake','build','--no-build','FV.E2E.SemanticBinary'],cwd=r,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
entry=json.loads((e/'sret-exec-entry-packet-state-v1.json').read_text());assert entry['status']=='passed'
heap=json.loads((e/'sret-symbolic-heap-packet-reviewed-v4-early-v1.json').read_text());assert heap['status']=='reviewed_pass' and heap['head']==head
for n,h in heap['artifact_hashes'].items():assert hashlib.sha256((r/n).read_bytes()).hexdigest()==h
print('Direct dependencies pass. Run the original gates sequentially at3GiB.',flush=True)
print('START verify-sret-exec-boundary-v2-early-v1.py',flush=True)
subprocess.run(['python3',str(e/'verify-sret-exec-boundary-v2-early-v1.py')],cwd=b,env=env,check=True)
print('START verify-sret-exec-boundary-packet-v1-early-v1.py',flush=True)
subprocess.run(['python3',str(e/'verify-sret-exec-boundary-packet-v1-early-v1.py')],cwd=b,env=env,check=True)
print('START verify-sret-captured-entry-v2-early-v1.py',flush=True)
subprocess.run(['python3',str(e/'verify-sret-captured-entry-v2-early-v1.py')],cwd=b,env=env,check=True)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()==head
print('Early executable boundary sequence passed at '+head,flush=True)
