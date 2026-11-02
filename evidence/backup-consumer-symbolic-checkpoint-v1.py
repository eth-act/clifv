from pathlib import Path
import datetime,fcntl,hashlib,json,os,subprocess
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029'
lock=(e/'captured-copy-remote-backup.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
patterns=['return-pin-consumer-isolated-*','verify-return-pin-consumer-isolated*.py','return-pin-generated-isolated-*','verify-return-pin-generated-isolated*.py','return-pin-generated-proof-packet-v*','verify-return-pin-generated-proof-packet-v1*.py','return-pin-executable-packet-v4*','verify-return-pin-executable-final-v1*.py','EmitReturnPinGeneratedWitnessV3.lean','WorkerOSretCapturedExecDraftV*.lean','sret-captured-exec-*','verify-sret-captured-exec*.py','consumer-symbolic-execution-reviewed-v1.json','stock-driver-reviewed-checkpoint-20261102-0514.md','integer-production-status-current-v199.md','integer-production-status-current-v200.md','backup-consumer-symbolic-checkpoint-v1.py']
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
parent=git('rev-parse',branch);idx=e/'consumer-symbolic-checkpoint-backup-v1.index';assert not idx.exists();env=dict(os.environ,GIT_INDEX_FILE=str(idx));git('read-tree',parent,env=env)
for n,data in files.items():
 blob=git('hash-object','-w','--stdin',data=data);git('update-index','--add','--cacheinfo','100644,'+blob+','+n,env=env)
commit=git('commit-tree',git('write-tree',env=env),'-p',parent,'-m','Preserve complete consumer integration, generated proofs, and symbolic linked execution')
git('update-ref','refs/heads/'+branch,commit,parent);subprocess.run(['git','push','origin',branch],cwd=b,check=True)
assert git('ls-remote','origin','refs/heads/'+branch).split()[0]==commit
for n,data in files.items():assert subprocess.check_output(['git','show',commit+':'+n],cwd=b)==data
idx.unlink();receipt=dict(commit=commit,remote_verified=True,files={n:hashlib.sha256(data).hexdigest() for n,data in files.items()},utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(e/'consumer-symbolic-checkpoint-backup-v1.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(dict(commit=commit,remote_verified=True,files=len(files))))
