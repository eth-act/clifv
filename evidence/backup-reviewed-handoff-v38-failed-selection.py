from pathlib import Path
import datetime,fcntl,hashlib,json,os,subprocess
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029'
lock=(e/'captured-copy-remote-backup.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
paths=[]
A=e/'140-acquire-fused810-packet-v1'
for n in range(81,90):
 matches=[p for p in A.glob('*-v'+str(n)) if (p/'state.json').exists()]
 assert len(matches)==1,(n,matches)
 paths.extend(matches)
G=e/'general7-main-candidate-v1';Q=e/'direct-call-store-live-packet-v1'
paths.append(G/'current8f-full-reverse-inventory-v1')
for name in ['current8f-ABIReadCfg-rebind-v1','production-arithmetic-return-trace-W-proposal-v1','production-pure-return-trace-W-proposal-v1','production-memory-return-trace-W-proposal-v1','production-result-call-return-trace-W-proposal-v1','production-memory-class-return-trace-W-proposal-v1','production-call-return-trace-W-proposal-v1','production-complete-return-trace-dispatcher-proposal-v1','production-internal-program-return-trace-proposal-v1','production-current8f-gate-lists-v1','production-current8f-CLI-activation-projection-v2','production-call-store-route-admission-proposal-v1']:
 paths.append(Q/name)
paths.append(A/'no-call-bounded-adapter-readiness-v1')
files={}
def capture(q):
 if not q.is_file() or q.is_symlink() or '.lake' in q.parts:return
 if q.suffix == '.log' and 'general7-remaining29-conditional-broad-12g-v1' in q.parts:return
 if q.name != 'logs-curated-v1.tar.gz' and q.suffix not in ['.json','.log','.mem','.lean','.py','.md','.diff','.stdout','.stderr','.txt']:return
 if q.name=='author-env-v1.json':return
 assert q.stat().st_size<32*1024*1024
 files['evidence/'+str(q.relative_to(e))]=q.read_bytes()
for p in paths:
 assert p.is_dir(),p
 for q in p.rglob('*'):capture(q)
capture(e/'integer-production-status-current-v306.md')
capture(e/'backup-reviewed-handoff-v38.py')
capture(e/'production-current-context-backup-v35.json')
capture(e/'general7-remaining29-conditional-broad-12g-v1/raw-log-cleanup-v1.json')
capture(e/'backup-reviewed-handoff-v34.py')
capture(e/'archive-completed-cone-logs-v1.py')
selection={'files':{n:len(d) for n,d in files.items()},'bytes':sum(map(len,files.values()))}
(e/'backup-v38-selection.json').write_text(json.dumps(selection,indent=2)+'\n')
assert selection['bytes']<128*1024*1024,selection['bytes']
print("Captured bytes",sum(map(len,files.values())),flush=True)
branch='agent/stock-cfg-body-progress-20261025T025359Z'
def git(*args,env=None,data=None):return subprocess.check_output(['git',*args],cwd=b,env=env,input=data).decode().strip()
parent=git('rev-parse',branch);idx=e/'production-current-context-backup-v38.index';assert not idx.exists()
env=dict(os.environ,GIT_INDEX_FILE=str(idx));git('read-tree',parent,env=env)
entries=[]
for name,data in files.items():
 blob=git('hash-object','-w','--stdin',data=data);entries.append(('100644 '+blob+'\t'+name+'\0').encode())
git('update-index','-z','--index-info',env=env,data=b''.join(entries))
commit=git('commit-tree',git('write-tree',env=env),'-p',parent,'-m','Preserve generic paired callbacks, coherent light providers, production W exports, and exact CLI projection')
git('update-ref','refs/heads/'+branch,commit,parent)
subprocess.run(['git','-c','pack.threads=1','-c','pack.windowMemory=16m','-c','pack.deltaCacheSize=16m','push','origin',branch],cwd=b,check=True)
assert git('ls-remote','origin','refs/heads/'+branch).split()[0]==commit
for name,data in files.items():assert subprocess.check_output(['git','show',commit+':'+name],cwd=b)==data
idx.unlink();r={'commit':commit,'remote_verified':True,'files':{n:hashlib.sha256(d).hexdigest() for n,d in files.items()},'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(e/'production-current-context-backup-v38.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'commit':commit,'remote_verified':True,'files':len(files)}))
