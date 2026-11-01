from pathlib import Path
import datetime,fcntl,json,os,subprocess
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029'
env=dict(os.environ);env.update(json.loads((e/'author-env-v1.json').read_text()))
lock=(e/'main870-cache-import.lock').open('a+')
fcntl.flock(lock,fcntl.LOCK_SH)
results=[]
# These packets are independent. Keep the build budget sequential, but close each gate even if another fails.
for name in ['verify-sret-symbolic-heap-packet-v4-core.py','verify-sret-exec-boundary-v2.py','verify-return-pin-routed-packet-v1.py','verify-sret-exec-result-bytes-v1.py','verify-return-pin-checks-with-v1.py']:
 print('START',name,flush=True)
 completed=subprocess.run(['python3',str(e/name)],cwd=b,env=env)
 results.append(dict(script=name,returncode=completed.returncode))
 print('DONE',name,'rc='+str(completed.returncode),flush=True)
 if name == 'verify-sret-exec-boundary-v2.py' and completed.returncode == 0:
  canonical = subprocess.run(['python3',str(e/'verify-sret-exec-boundary-packet-v1.py')],cwd=b,env=env)
  results.append(dict(script='verify-sret-exec-boundary-packet-v1.py',returncode=canonical.returncode))
  print('CANONICAL executable boundary rc='+str(canonical.returncode),flush=True)
  if canonical.returncode == 0:
   captured = subprocess.run(['python3',str(e/'verify-sret-captured-entry-v2.py')],cwd=b,env=env)
   results.append(dict(script='verify-sret-captured-entry-v2.py',returncode=captured.returncode))
   print('CAPTURED symbolic executable entry rc='+str(captured.returncode),flush=True)
receipt=dict(status='passed' if all(row['returncode']==0 for row in results) else 'inspect_failures',
 results=results,full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(e/'post-importer-independent-packets-v1.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt),flush=True)
assert receipt['status']=='passed','Inspect individual packet logs and receipts. Preserve every successful independent result.'
