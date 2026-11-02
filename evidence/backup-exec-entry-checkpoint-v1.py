from pathlib import Path
import datetime,fcntl,hashlib,json,os,subprocess
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029'
lock=(e/'captured-copy-remote-backup.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
patterns=['verify-sret-exec-boundary*.py','verify-sret-captured-entry*.py','sret-exec-boundary*.json','sret-captured-entry*.json','sret-exec-boundary-memory*.log','sret-captured-entry-memory*.log','WorkerOSretExecBoundaryDraftV*.lean','WorkerOSretCapturedEntryDraftV*.lean','sret-executable-entry-reviewed-v1.json','integer-production-status-current-v195.md','peer-review-878.diff','backup-exec-entry-checkpoint-v1.py']
files={}
for pattern in patterns:
 for p in e.glob(pattern):
  if p.is_file():files['evidence/'+p.name]=p.read_bytes()
for name in ['sret-exec-boundary-packet-v1','sret-exec-boundary-packet-v2','sret-exec-boundary-kernel-v2-early-v1','sret-exec-boundary-kernel-v2-early-v2','sret-exec-boundary-packet-kernel-v1-early-v2','sret-captured-entry-packet-v1','sret-captured-entry-kernel-v2-early-v2','sret-captured-entry-kernel-v2-early-v3','sret-captured-entry-packet-kernel-v1']:
 for p in (e/name).rglob('*'):
  if p.is_file() and not p.is_symlink():files['evidence/'+str(p.relative_to(e))]=p.read_bytes()
branch='agent/stock-cfg-body-progress-20261025T025359Z'
def git(*args,env=None,data=None):return subprocess.check_output(['git',*args],cwd=b,env=env,input=data).decode().strip()
parent=git('rev-parse',branch);idx=e/'exec-entry-checkpoint-backup-v1.index';assert not idx.exists();env=dict(os.environ,GIT_INDEX_FILE=str(idx));git('read-tree',parent,env=env)
for n,data in files.items():
 blob=git('hash-object','-w','--stdin',data=data);git('update-index','--add','--cacheinfo','100644,'+blob+','+n,env=env)
commit=git('commit-tree',git('write-tree',env=env),'-p',parent,'-m','Preserve checked executable-entry modules, corrected sources, and original failures')
git('update-ref','refs/heads/'+branch,commit,parent);subprocess.run(['git','push','origin',branch],cwd=b,check=True)
assert git('ls-remote','origin','refs/heads/'+branch).split()[0]==commit
for n,data in files.items():assert subprocess.check_output(['git','show',commit+':'+n],cwd=b)==data
idx.unlink();receipt=dict(commit=commit,remote_verified=True,files={n:hashlib.sha256(data).hexdigest() for n,data in files.items()},utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(e/'exec-entry-checkpoint-backup-v1.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(dict(commit=commit,remote_verified=True,files=len(files))))
