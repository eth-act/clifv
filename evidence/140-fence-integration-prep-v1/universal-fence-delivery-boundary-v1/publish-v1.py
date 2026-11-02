from pathlib import Path
import datetime,fcntl,hashlib,json,os,subprocess
B=Path('/home/lee/clifv');D=Path(__file__).resolve().parent
M=json.loads((D/'manifest.json').read_text());R=json.loads((D/'coordinator-ready-v1.json').read_text())
assert R['status']=='approved_for_publication'
assert R['manifest_sha256']==hashlib.sha256((D/'manifest.json').read_bytes()).hexdigest()
assert R['gate_sha256']==hashlib.sha256((D/'current-gate-v1.json').read_bytes()).hexdigest()
lock=(D/'publication-owner.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
receipt=D/'published-v1.json';assert not receipt.exists(),'Inspect existing publication receipt'
def git(*args,data=None,env=None):return subprocess.check_output(['git',*args],cwd=B,input=data,env=env).decode().strip()
git('fetch','origin','main');base=git('rev-parse','origin/main')
assert base==subprocess.check_output(['gh','api','repos/eth-act/clifv/commits/main','--jq','.sha'],cwd=B,text=True).strip()
closure={}
for module,p in M['provider_source_projection'].items():
 n=p['path'];h=p['canonical_sha256']
 assert hashlib.sha256(subprocess.check_output(['git','show',base+':'+n],cwd=B)).hexdigest()==h,('Changed provider',n)
 closure[n]=h
for n in ['lakefile.toml','lake-manifest.json','lean-toolchain','scripts/axiom-audit.py','scripts/memcap.sh']:
 assert git('rev-parse',base+':'+n)==git('rev-parse',M['baseline']+':'+n),('Config changed',n)
branch='agent/stock-fence-refinement-20261102'
assert not git('ls-remote','origin','refs/heads/'+branch),'Remote publication already exists'
assert subprocess.run(['git','show-ref','--verify','--quiet','refs/heads/'+branch],cwd=B).returncode!=0
index=D/'publication-v1.index';assert not index.exists()
env=dict(os.environ,GIT_INDEX_FILE=str(index));git('read-tree',base,env=env)
for n,h in M['source_sha256'].items():
 assert subprocess.run(['git','cat-file','-e',base+':'+n],cwd=B,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode!=0,('Candidate file exists',n)
 data=(D/'source'/n).read_bytes();assert hashlib.sha256(data).hexdigest()==h,n
 blob=git('hash-object','-w','--stdin',data=data)
 git('update-index','--add','--cacheinfo','100644,'+blob+','+n,env=env);closure[n]=h
tree=git('write-tree',env=env);index.unlink();git('diff-tree','--check',base,tree)
assert set(git('diff-tree','--no-commit-id','--name-only','-r',base,tree).splitlines())==set(M['source_sha256'])
head=git('commit-tree',tree,'-p',base,'-m','Prove Stock fence selection, source effects and barrier ordering')
git('update-ref','refs/heads/'+branch,head,'0'*40)
git('push','origin','refs/heads/'+branch+':refs/heads/'+branch)
url=subprocess.check_output(['gh','pr','create','--repo','eth-act/clifv','--base','main','--head',branch,'--title','Prove Stock fence selection, source effects and barrier ordering','--body-file',str(D/'PR-body-v1.md')],cwd=B,text=True).strip()
state={'status':'published_pending_direct_review_and_exact_head_CI','pr':int(url.rstrip('/').split('/')[-1]),'url':url,'branch':branch,'head':head,'base':base,'tree':tree,'source_hashes':M['source_sha256'],'closure_source_hashes':closure,'gate_sha256':R['gate_sha256'],'manifest_sha256':R['manifest_sha256'],'standard_roots':33,'fixed_roots':2,'full_fence_closure':False,'full_goal_complete':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
receipt.write_text(json.dumps(state,indent=2)+'\n');print(json.dumps({k:state[k] for k in ['status','pr','url','head','base','tree']}),flush=True)
