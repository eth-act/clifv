from pathlib import Path
import fcntl,os,json,subprocess
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029';r=b/'.worktrees/stock-extending-production-20261031'
lock=(e/'main870-cache-import.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
assert b'return-pin-call-consumer-recovery-v3' in Path('/proc/3477137/cmdline').read_bytes()
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip();assert head=='a4c0726d46c5908b4ac06cf797ee939af8644703'
env=dict(os.environ);env.update(json.loads((e/'author-env-v1.json').read_text()));env.update(FV_ROOT=str(r))
for name in ['verify-return-pin-checks-with-v1-early-v5.py','verify-return-pin-checks-packet-v1-early-v5.py']:
 print('START',name,flush=True);subprocess.run(['python3',str(e/name)],cwd=b,env=env,check=True)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()==head
