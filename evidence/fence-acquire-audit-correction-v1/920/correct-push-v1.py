from pathlib import Path
import datetime,fcntl,hashlib,json,os,re,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';D=Path(__file__).resolve().parent;OLD=E/'140-acquire-fused810-packet-v1/delivery-boundary-v2';P=json.loads((OLD/'published-v1.json').read_text());G=json.loads((D/'current-gate-v1.json').read_text());M=json.loads((D/'manifest.json').read_text())
lock=(D/'publication-owner.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);assert not (D/'published-v1.json').exists()
def cmd(*args):return subprocess.check_output(args,cwd=B,text=True).strip()
def git(*args,data=None,env=None):return subprocess.check_output(['git',*args],cwd=B,input=data,env=env).decode().strip()
assert G['status']=='passed' and G['real_repository_auditor']['exit']==0 and G['old_axiom_sets_exact'];assert G['axioms']==json.loads((OLD/'current-gate-v1.json').read_text())['axioms']
state=json.loads(cmd('gh','pr','view','920','--repo','eth-act/clifv','--json','state,headRefOid'));assert state['state']=='OPEN' and state['headRefOid']==P['head'];assert git('rev-parse',P['branch'])==P['head']
fix=json.loads(cmd('gh','pr','view','921','--repo','eth-act/clifv','--json','state,mergeCommit'));assert fix['state']=='MERGED'
git('fetch','origin','main');base=git('rev-parse','origin/main');assert base==cmd('gh','api','repos/eth-act/clifv/commits/main','--jq','.sha');assert subprocess.run(['git','merge-base','--is-ancestor',fix['mergeCommit']['oid'],base],cwd=B).returncode==0
source=dict(P['source_hashes']);closure=dict(P['closure_source_hashes'])
def code(t):return [line.split('--',1)[0].strip() for line in t.splitlines() if line.split('--',1)[0].strip()]
for n,r in M['changes'].items():
 before=subprocess.check_output(['git','show',P['head']+':'+n],cwd=B);after=(D/'source'/n).read_bytes();assert hashlib.sha256(before).hexdigest()==r['old_sha256'];assert hashlib.sha256(after).hexdigest()==r['new_sha256'];assert code(before.decode())==code(after.decode()),n;source[n]=r['new_sha256'];closure[n]=r['new_sha256']
for n,h in closure.items():
 if n not in source:assert hashlib.sha256(subprocess.check_output(['git','show',base+':'+n],cwd=B)).hexdigest()==h,('Changed import',n)
mtree=git('merge-tree','--write-tree',P['head'],base).splitlines()[0];index=D/'publication-v1.index';assert not index.exists();env=dict(os.environ,GIT_INDEX_FILE=str(index));git('read-tree',mtree,env=env)
for n,h in G['source_hashes'].items():
 data=(D/'source'/n).read_bytes();assert hashlib.sha256(data).hexdigest()==h;blob=git('hash-object','-w','--stdin',data=data);git('update-index','--add','--cacheinfo','100644,'+blob+','+n,env=env)
tree=git('write-tree',env=env);index.unlink();git('diff-tree','--check',base,tree);assert set(git('diff-tree','--no-commit-id','--name-only','-r',base,tree).splitlines())==set(source)
head=git('commit-tree',tree,'-p',P['head'],'-p',base,'-m','Correct acquire witness markers and preserve the landed fence audit fix');git('update-ref','refs/heads/'+P['branch'],head,P['head']);git('push','origin','refs/heads/'+P['branch']+':refs/heads/'+P['branch'])
for n,h in closure.items():assert hashlib.sha256(subprocess.check_output(['git','show',head+':'+n],cwd=B)).hexdigest()==h,n
norm=json.loads((OLD/'publication-manifest-v1.json').read_text());norm.update(baseline=base,source_sha256=source,comment_only_correction=M['changes'],real_repository_audit_passed=True);(D/'publication-manifest-v1.json').write_text(json.dumps(norm,indent=2)+'\n');(D/'publication-current-gate-v1.json').write_bytes((D/'current-gate-v1.json').read_bytes());gate_sha=hashlib.sha256((D/'publication-current-gate-v1.json').read_bytes()).hexdigest();manifest_sha=hashlib.sha256((D/'publication-manifest-v1.json').read_bytes()).hexdigest();(D/'coordinator-ready-v1.json').write_text(json.dumps({'status':'approved_for_publication','manifest_sha256':manifest_sha,'gate_sha256':gate_sha,'real_repository_auditor_exit':0,'all_56_axiom_sets_exact':True,'source_context_rechecked_at':base,'comment_only':True},indent=2)+'\n')
pub=dict(P);pub.update(head=head,base=base,tree=tree,source_hashes=source,closure_source_hashes=closure,gate_sha256=gate_sha,manifest_sha256=manifest_sha,status='corrected_head_pending_explicit_peer_verdict_and_fresh_CI',previous_head=P['head'],normal_descendant=True,required_921_merge=fix['mergeCommit']['oid'],real_repository_audit_passed=True,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(D/'published-v1.json').write_text(json.dumps(pub,indent=2)+'\n');print(json.dumps({k:pub[k] for k in ['head','base','tree','previous_head','normal_descendant','real_repository_audit_passed']}),flush=True)
