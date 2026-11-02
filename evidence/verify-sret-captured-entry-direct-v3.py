from pathlib import Path
import fcntl,json,os,subprocess
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029';r=b/'.worktrees/stock-extending-production-20261031'
lock=(e/'main870-cache-import.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
assert b'captured-symbolic-packet-after-importers-v1' in Path('/proc/3507911/cmdline').read_bytes()
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()
receipt=json.loads((e/'sret-exec-boundary-packet-state-v1-early-v2.json').read_text());assert receipt['status']=='passed' and receipt['head']==head
assert subprocess.check_output(['git','status','--porcelain'],cwd=r,text=True)==''
env=dict(os.environ);env.update(json.loads((e/'author-env-v1.json').read_text()));env.update(FV_ROOT=str(r))
subprocess.run(['python3',str(e/'verify-sret-captured-entry-v2-early-v3.py')],cwd=b,env=env,check=True)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()==head
print('The captured executable-entry witness passed at '+head,flush=True)
