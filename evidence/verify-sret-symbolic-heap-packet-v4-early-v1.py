from pathlib import Path
import fcntl,json,os,re,subprocess,time
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029';r=b/'.worktrees/stock-extending-production-20261031'
# The existing proof owner holds the source view. Its later SH lock waits for this EX lock.
lock=(e/'main870-cache-import.lock').open('a+')
fcntl.flock(lock,fcntl.LOCK_EX)
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()
assert head=='a4c0726d46c5908b4ac06cf797ee939af8644703'
env=dict(os.environ);env.update(json.loads((e/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None)
env.update(FV_ROOT=str(r),LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',FV_MEMCAP='1G',FV_MEMCAP_UNIT='worker-o-heap-early-ready-v1',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2')
roots=['FV.Backend.Proof.IselMemArm','FV.E2E.Statement','FV.E2E.PreparedReturnPinCallsWitness','FV.E2E.SrcScopeDefs','FV.Backend.Proof.StockMemorySretCopyBodyWitness']
last=None
while True:
 assert b'captured-symbolic-packet-after-importers-v1' in Path('/proc/3507911/cmdline').read_bytes(),'Source owner exited. Inspect the view before continuing.'
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()==head
 c=subprocess.run(['nice','-n','10',str(r/'scripts/memcap.sh'),'lake','build','--no-build',*roots],cwd=r,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 missing=re.findall(r'Building (FV\.[\w.]+)',c.stdout)
 if missing!=last:
  print('DEPENDENCIES',json.dumps(missing),'rc='+str(c.returncode),flush=True);last=missing
 if c.returncode==0:break
 assert c.returncode==3 and missing,c.stdout
 time.sleep(30)
assert subprocess.check_output(['git','status','--porcelain'],cwd=r,text=True)==''
print('Actual direct dependencies pass without a build or cache restore. Start the unchanged 3GiB packet gate.',flush=True)
subprocess.run(['python3',str(e/'verify-sret-symbolic-heap-packet-v4-early-core-v1.py')],cwd=b,env=env,check=True)
