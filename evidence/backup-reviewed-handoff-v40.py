from pathlib import Path
import datetime,fcntl,hashlib,json,os,subprocess,sys
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029'
locks=[]
for lockname in ['broad-priority-exclusive.lock','captured-copy-remote-backup.lock']:
 lock=(e/lockname).open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);locks.append(lock)
A=e/'140-acquire-fused810-packet-v1';G=e/'general7-main-candidate-v1';Q=e/'direct-call-store-live-packet-v1'
prior=json.loads((e/'production-current-context-backup-v39.json').read_text());assert prior['remote_verified']
known={}
for receipt in sorted((p for p in e.glob('production-current-context-backup-v*.json') if p.stem.rsplit('v',1)[-1].isdigit()),key=lambda p:int(p.stem.rsplit('v',1)[-1])):
 data=json.loads(receipt.read_text())
 if data.get('remote_verified'):known.update(data.get('files',{}))
paths=[]
for p in A.glob('universal-*-checkpoint-v*'):
 version=p.name.rsplit('v',1)[-1]
 if version.isdigit() and 92<=int(version)<=106:paths.append(p)
for name in ['actual-map-rel-rw-proposal-v3','actual-map-rel-rw-proposal-v4','actual-map-rel-rw-proposal-v5','outside-avoids-extraction-proposal-v1','actual-result-image-bridge-v2','actual-map-rel-rw-proposal-v6','actual-results-ELF-lookup-proposal-v1','two-load-current8f-pipeline-proposal-v2','actual-public-entry-budget-proposal-v2','acquire-production-boundary-proposal-v1','acquire-production-boundary-proposal-v2']:
 paths.append(A/name)
for name in ['production-current8f-dispatcher-integration-v1','production-actual-input-return-trace-proposal-v1','production-checked-program-return-trace-proposal-v1','production-float-call-store-class-proposal-v1']:
 paths.append(Q/name)
M=Q/'production-memory-class-return-trace-W-proposal-v1'
for name in ['remaining-eight-fresh-R-run-v1','current8f-focused-v2','canonical-current8f-memory-W12-v1']:
 p=M/name
 if p.exists():paths.append(p)
for name in ['reverse-mixed1368-batch01-broad12-v1','reverse-mixed1368-batch01-broad12-v2','reverse-mixed1368-batch01-broad12-v3','reverse-mixed1368-batch02-broad12-v1','old23-fifteen-broad-12g-v1','old23-fifteen-broad-12g-v2']:
 paths.append(e/name)
D=G/'current8f-full-reverse-inventory-v1';paths.append(D)
unit='acquire'
files={};total=0
suffixes={'.json','.log','.mem','.lean','.py','.md','.diff','.stdout','.stderr','.txt','.toml'}
def capture(q,force=False):
 global total
 if not q.is_file() or q.is_symlink() or '.lake' in q.parts or '__pycache__' in q.parts:return
 if q.name=='author-env-v1.json':return
 if q.suffix not in suffixes and q.name!='lean-toolchain':return
 if q.suffix in {'.stdout','.stderr'} and 'kernel-' not in q.name and q.name not in ['0003-deps-0.stdout','0003-deps-0.stderr']:return
 if q.stat().st_size>=32*1024*1024:raise AssertionError(('single-file bound',str(q),q.stat().st_size))
 name='evidence/'+str(q.relative_to(e))
 kind='acquire' if name.startswith('evidence/140-acquire-fused810-packet-v1/') else 'production' if name.startswith('evidence/direct-call-store-live-packet-v1/') else 'reverse-and-guards'
 if not force and kind!=unit:return
 if name in files:return
 before=q.stat();data=q.read_bytes();after=q.stat();assert (before.st_size,before.st_mtime_ns)==(after.st_size,after.st_mtime_ns),('file changed during snapshot',str(q))
 h=hashlib.sha256(data).hexdigest()
 if known.get(name)==h:return
 total+=len(data)
 files[name]=data
for p in paths:
 assert p.is_dir(),p
 for q in p.rglob('*'):capture(q)
capture(e/'backup-reviewed-handoff-v40.py',True)
if unit=='reverse-and-guards':
 capture(e/'backup-v40-failed-selection-v1.json')
 capture(e/'backup-v40-failed-selection-script-v1.py')
 capture(e/'backup-v40-v42-split-plan.json')
selection={'files':{n:len(d) for n,d in files.items()},'bytes':sum(map(len,files.values()))}
(e/'backup-v40-acquire-selection.json').write_text(json.dumps(selection,indent=2)+'\n')
assert selection['bytes']<128*1024*1024,selection['bytes']
print("Captured bytes",sum(map(len,files.values())),flush=True)
if "--dry-run" in sys.argv: raise SystemExit(0)
branch='agent/stock-cfg-body-progress-20261025T025359Z'
def git(*args,env=None,data=None):return subprocess.check_output(['git',*args],cwd=b,env=env,input=data).decode().strip()
parent=git('rev-parse',branch);assert parent==prior['commit'],('unexpected backup parent',parent);idx=e/'production-current-context-backup-v40.index';assert not idx.exists()
env=dict(os.environ,GIT_INDEX_FILE=str(idx));git('read-tree',parent,env=env)
entries=[]
for name,data in files.items():
 blob=git('hash-object','-w','--stdin',data=data);entries.append(('100644 '+blob+'\t'+name+'\0').encode())
git('update-index','-z','--index-info',env=env,data=b''.join(entries))
commit=git('commit-tree',git('write-tree',env=env),'-p',parent,'-m','Preserve reviewed acquire evidence in bounded backup v40')
git('update-ref','refs/heads/'+branch,commit,parent)
subprocess.run(['git','-c','pack.threads=1','-c','pack.windowMemory=16m','-c','pack.deltaCacheSize=16m','push','origin',branch],cwd=b,check=True)
assert git('ls-remote','origin','refs/heads/'+branch).split()[0]==commit
for name,data in files.items():assert subprocess.check_output(['git','show',commit+':'+name],cwd=b)==data
idx.unlink();r={'commit':commit,'remote_verified':True,'files':{n:hashlib.sha256(d).hexdigest() for n,d in files.items()},'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(e/'production-current-context-backup-v40.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'commit':commit,'remote_verified':True,'files':len(files)}))
