from pathlib import Path
import datetime,fcntl,hashlib,json,os,subprocess
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029'
lock=(e/'captured-copy-remote-backup.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
paths=[]
A=e/'140-acquire-fused810-packet-v1'
for n in range(56,67):
 matches=[p for p in A.glob('*-v'+str(n)) if (p/'state.json').exists()]
 assert len(matches)==1,(n,matches)
 paths.extend(matches)
paths.extend([e/'general7-remaining29-conditional-broad-12g-v1',e/'general7-main-candidate-v1/remaining29-conditional-cone-proposal-v1',e/'general7-main-candidate-v1/remaining-focused-roots-v2',e/'general7-main-candidate-v1/full1657-39-archive-provenance-v1',e/'general7-main-candidate-v1/actual-axiom-audit-v1',e/'general7-main-candidate-v1/actual-axiom-audit-v2',e/'direct-call-store-live-packet-v1/production-validated-return-trace-W-proposal-v2',e/'direct-call-store-live-packet-v1/production-result-call-return-trace-W-proposal-v1'])
files={}
def capture(q):
 if not q.is_file() or q.is_symlink() or '.lake' in q.parts:return
 if q.suffix not in ['.json','.log','.mem','.lean','.py','.md','.diff']:return
 if q.name=='author-env-v1.json':return
 assert q.stat().st_size<32*1024*1024
 files['evidence/'+str(q.relative_to(e))]=q.read_bytes()
for p in paths:
 assert p.is_dir(),p
 for q in p.rglob('*'):capture(q)
capture(e/'integer-production-status-current-v290.md')
assert sum(map(len,files.values()))<128*1024*1024
print("Captured bytes",sum(map(len,files.values())),flush=True)
branch='agent/stock-cfg-body-progress-20261025T025359Z'
def git(*args,env=None,data=None):return subprocess.check_output(['git',*args],cwd=b,env=env,input=data).decode().strip()
parent=git('rev-parse',branch);idx=e/'production-current-context-backup-v34.index';assert not idx.exists()
env=dict(os.environ,GIT_INDEX_FILE=str(idx));git('read-tree',parent,env=env)
entries=[]
for name,data in files.items():
 blob=git('hash-object','-w','--stdin',data=data);entries.append(('100644 '+blob+'\t'+name+'\0').encode())
git('update-index','-z','--index-info',env=env,data=b''.join(entries))
commit=git('commit-tree',git('write-tree',env=env),'-p',parent,'-m','Preserve live-frontier and fault-prefix proofs, current1657 completion, focused roots, and W proposals')
git('update-ref','refs/heads/'+branch,commit,parent)
subprocess.run(['git','-c','pack.threads=1','-c','pack.windowMemory=16m','-c','pack.deltaCacheSize=16m','push','origin',branch],cwd=b,check=True)
assert git('ls-remote','origin','refs/heads/'+branch).split()[0]==commit
for name,data in files.items():assert subprocess.check_output(['git','show',commit+':'+name],cwd=b)==data
idx.unlink();r={'commit':commit,'remote_verified':True,'files':{n:hashlib.sha256(d).hexdigest() for n,d in files.items()},'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(e/'production-current-context-backup-v34.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'commit':commit,'remote_verified':True,'files':len(files)}))
