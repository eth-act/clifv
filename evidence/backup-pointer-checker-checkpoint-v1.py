from pathlib import Path
import datetime,fcntl,hashlib,json,os,subprocess
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029'
lock=(e/'captured-copy-remote-backup.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
patterns=['sret-entry-value-packet-v4*','sret-869-*','verify-sret-869*','verify-sret-entry-value-packet-v3*.py','WorkerOReturnPinChecksWithDraftV5.lean','return-pin-checks-*','verify-return-pin-checks*.py','integer-production-status-current-v198.md','sret-pointer-checker-reviewed-v1.json','peer-review-880.diff','backup-pointer-checker-checkpoint-v1.py']
files={}
for pattern in patterns:
 for p in e.glob(pattern):
  if p.is_file() and p.suffix in ['.json','.py','.log','.md','.lean','.diff']:files['evidence/'+p.name]=p.read_bytes()
  elif p.is_dir():
   assert not (p/'.lake').exists(),'Do not archive cache links'
   for q in p.rglob('*'):
    if q.is_file() and not q.is_symlink() and (q.suffix in ['.json','.py','.log','.md','.lean','.toml','.txt'] or q.name=='lean-toolchain'):files['evidence/'+str(q.relative_to(e))]=q.read_bytes()
branch='agent/stock-cfg-body-progress-20261025T025359Z'
def git(*args,env=None,data=None):return subprocess.check_output(['git',*args],cwd=b,env=env,input=data).decode().strip()
parent=git('rev-parse',branch);idx=e/'pointer-checker-checkpoint-backup-v1.index';assert not idx.exists();env=dict(os.environ,GIT_INDEX_FILE=str(idx));git('read-tree',parent,env=env)
for n,data in files.items():
 blob=git('hash-object','-w','--stdin',data=data);git('update-index','--add','--cacheinfo','100644,'+blob+','+n,env=env)
commit=git('commit-tree',git('write-tree',env=env),'-p',parent,'-m','Preserve complete paired pointer proofs and generated checker checkpoint')
git('update-ref','refs/heads/'+branch,commit,parent);subprocess.run(['git','push','origin',branch],cwd=b,check=True)
assert git('ls-remote','origin','refs/heads/'+branch).split()[0]==commit
for n,data in files.items():assert subprocess.check_output(['git','show',commit+':'+n],cwd=b)==data
idx.unlink();receipt=dict(commit=commit,remote_verified=True,files={n:hashlib.sha256(data).hexdigest() for n,data in files.items()},utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(e/'pointer-checker-checkpoint-backup-v1.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(dict(commit=commit,remote_verified=True,files=len(files))))
