from pathlib import Path
import fcntl,json,os,subprocess
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029';r=b/'.worktrees/stock-extending-production-20261031'
lock=(e/'main870-cache-import.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
assert b'captured-symbolic-packet-after-importers-v1' in Path('/proc/3507911/cmdline').read_bytes()
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip();assert head=='a4c0726d46c5908b4ac06cf797ee939af8644703'
env=dict(os.environ);env.update(json.loads((e/'author-env-v1.json').read_text()));env.update(FV_ROOT=str(r))
subprocess.run(['python3',str(e/'verify-sret-captured-entry-packet-v1.py')],cwd=b,env=env,check=True)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()==head
