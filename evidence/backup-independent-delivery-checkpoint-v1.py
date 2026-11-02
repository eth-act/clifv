from pathlib import Path
import datetime,fcntl,hashlib,json,os,subprocess
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029'
lock=(e/'captured-copy-remote-backup.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
patterns=['*860-independent*','*865-independent*','*866-independent*','*runtime-independent*','prepare-independent-packet-delivery-v*.py','merge-independent-packet-delivery-v1.py','independent-delivery-handoff-v1.py','deliver-void-call-file-v2*.py','deliver-link-image-extension-v2*.py','deliver-return-pin-runtime-v2*.py','publish-return-pin-runtime-v3*.py','return-pin-call-consumer-landed-v1.json','860-main-drift-20261102-0520.json','integer-production-status-current-v201.md','integer-production-status-current-v202.md','peer-review-881.diff','peer-review-882.diff','backup-independent-delivery-checkpoint-v1.py']
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
parent=git('rev-parse',branch);idx=e/'independent-delivery-checkpoint-backup-v1.index';assert not idx.exists();env=dict(os.environ,GIT_INDEX_FILE=str(idx));git('read-tree',parent,env=env)
for n,data in files.items():
 blob=git('hash-object','-w','--stdin',data=data);git('update-index','--add','--cacheinfo','100644,'+blob+','+n,env=env)
commit=git('commit-tree',git('write-tree',env=env),'-p',parent,'-m','Preserve landed ABI consumers and safe independent delivery gates')
git('update-ref','refs/heads/'+branch,commit,parent);subprocess.run(['git','push','origin',branch],cwd=b,check=True)
assert git('ls-remote','origin','refs/heads/'+branch).split()[0]==commit
for n,data in files.items():assert subprocess.check_output(['git','show',commit+':'+n],cwd=b)==data
idx.unlink();receipt=dict(commit=commit,remote_verified=True,files={n:hashlib.sha256(data).hexdigest() for n,data in files.items()},utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(e/'independent-delivery-checkpoint-backup-v1.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(dict(commit=commit,remote_verified=True,files=len(files))))
