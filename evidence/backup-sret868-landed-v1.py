from pathlib import Path
import datetime,fcntl,hashlib,json,os,subprocess
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029'
lock=(e/'captured-copy-remote-backup.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
patterns=['*sret-868*','merge-sret-868-independent*.py','sret-full-cfg-landed-v1.json','deliver-sret-full-cfg-v2*.py','integer-production-status-current-v197.md','abi-stagef-boundary-843-v2.md','peer-review-879.diff','WorkerOReturnPinChecksWithDraftV*.lean','verify-return-pin-checks*.py','return-pin-checks-*','verify-independent-consumers-direct-v1.py','independent-consumers-direct-state-v1.json','post-importer-independent-packets-v1.json','post-importer-direct-dependency-readiness-v5.*','sret-exec-result-bytes-*','backup-sret868-landed-v1.py']
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
parent=git('rev-parse',branch);idx=e/'sret868-landed-backup-v1.index';assert not idx.exists();env=dict(os.environ,GIT_INDEX_FILE=str(idx));git('read-tree',parent,env=env)
for n,data in files.items():
 blob=git('hash-object','-w','--stdin',data=data);git('update-index','--add','--cacheinfo','100644,'+blob+','+n,env=env)
commit=git('commit-tree',git('write-tree',env=env),'-p',parent,'-m','Preserve independently landed complete sret source proofs and delivery evidence')
git('update-ref','refs/heads/'+branch,commit,parent);subprocess.run(['git','push','origin',branch],cwd=b,check=True)
assert git('ls-remote','origin','refs/heads/'+branch).split()[0]==commit
for n,data in files.items():assert subprocess.check_output(['git','show',commit+':'+n],cwd=b)==data
idx.unlink();receipt=dict(commit=commit,remote_verified=True,files={n:hashlib.sha256(data).hexdigest() for n,data in files.items()},utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(e/'sret868-landed-backup-v1.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(dict(commit=commit,remote_verified=True,files=len(files))))
