from pathlib import Path
import datetime,fcntl,hashlib,json,os,subprocess
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029'
lock=(e/'captured-copy-remote-backup.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
patterns=['direct-call-arithmetic-live-packet-v1', '140-fence-integration-prep-v1', '140-fence-packet-v1', 'peer-reviews', 'integer-production-status-current-v223.md', 'worker-O-execution-handoff-current-v1.md', 'worker-O-execution-handoff-before-foundation-*', 'backup-consumer-delivery-checkpoint-v12.py']
files={}
for pattern in patterns:
 for p in e.glob(pattern):
  candidates=[p] if p.is_file() else p.rglob('*') if p.is_dir() else []
  for q in candidates:
   rel=q.relative_to(e)
   if '.lake' in rel.parts or q.is_symlink() or not q.is_file():continue
   if q.suffix not in ['.json','.py','.log','.md','.lean','.toml','.txt','.diff','.patch','.o','.elf','.clif','.bin','.sh','.mem','.trace'] and q.name!='lean-toolchain':continue
   assert q.name!='author-env-v1.json'
   if q.stat().st_size>32*1024*1024:continue
   files['evidence/'+str(rel)]=q.read_bytes()
branch='agent/stock-cfg-body-progress-20261025T025359Z'
def git(*args,env=None,data=None):return subprocess.check_output(['git',*args],cwd=b,env=env,input=data).decode().strip()
parent=git('rev-parse',branch);idx=e/'production-current-context-backup-v12.index';assert not idx.exists();env=dict(os.environ,GIT_INDEX_FILE=str(idx),GIT_CONFIG_COUNT='3',GIT_CONFIG_KEY_0='pack.threads',GIT_CONFIG_VALUE_0='2',GIT_CONFIG_KEY_1='pack.windowMemory',GIT_CONFIG_VALUE_1='32m',GIT_CONFIG_KEY_2='pack.deltaCacheSize',GIT_CONFIG_VALUE_2='32m');git('read-tree',parent,env=env)
for n,data in files.items():
 blob=git('hash-object','-w','--stdin',data=data);git('update-index','--add','--cacheinfo','100644,'+blob+','+n,env=env)
commit=git('commit-tree',git('write-tree',env=env),'-p',parent,'-m','Preserve live-call, universal fence and current-main delivery checkpoints')
git('update-ref','refs/heads/'+branch,commit,parent);subprocess.run(['git','-c','pack.threads=2','-c','pack.windowMemory=32m','-c','pack.deltaCacheSize=32m','push','origin',branch],cwd=b,check=True)
assert git('ls-remote','origin','refs/heads/'+branch).split()[0]==commit
for n,data in files.items():assert subprocess.check_output(['git','show',commit+':'+n],cwd=b)==data
idx.unlink();receipt=dict(commit=commit,remote_verified=True,files={n:hashlib.sha256(data).hexdigest() for n,data in files.items()},utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(e/'production-current-context-backup-v12.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(dict(commit=commit,remote_verified=True,files=len(files))))
