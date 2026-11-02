from pathlib import Path
import datetime,fcntl,hashlib,json,subprocess,sys
B=Path('/home/lee/clifv');D=Path(__file__).resolve().parent;oldD=D/sys.argv[1];N=D/sys.argv[2];expected=sys.argv[3];assert not N.exists();N.mkdir()
lock=(D/'publication-owner.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
old=json.loads((oldD/'published-v1.json').read_text());review=json.loads((oldD/'peer-review-v1.json').read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=B,text=True).strip()
def sha(data):return hashlib.sha256(data).hexdigest()
state=json.loads(subprocess.check_output(['gh','pr','view','922','--repo','eth-act/clifv','--json','state,headRefOid,statusCheckRollup'],cwd=B,text=True));assert state['state']=='OPEN' and state['headRefOid']==old['head'];(N/'previous-exact-head-CI.json').write_text(json.dumps(state,indent=2)+'\n')
required={'Quick checks','Build and compare','Check lost matches','Publish PR result'};assert required.issubset({x.get('name') for x in state['statusCheckRollup'] if x.get('conclusion')=='SUCCESS'})
assert git('rev-parse','refs/heads/'+old['branch'])==old['head'];assert git('ls-remote','origin','refs/heads/'+old['branch']).split()[0]==old['head']
git('fetch','origin','main');base=git('rev-parse','origin/main');assert base==expected
for n,v in old['closure_source_hashes'].items():
 if n not in old['source_hashes']:assert sha(subprocess.check_output(['git','show',base+':'+n],cwd=B))==v,n
for n in ['lakefile.toml','lake-manifest.json','lean-toolchain','scripts/axiom-audit.py','scripts/memcap.sh']:assert git('rev-parse',base+':'+n)==git('rev-parse',old['base']+':'+n),n
tree=git('merge-tree','--write-tree',old['head'],base).splitlines()[0];assert set(git('diff-tree','--no-commit-id','--name-only','-r',base,tree).splitlines())==set(old['source_hashes'])
for n,v in old['source_hashes'].items():assert sha(subprocess.check_output(['git','show',tree+':'+n],cwd=B))==v,n
head=git('commit-tree',tree,'-p',old['head'],'-p',base,'-m','Reconcile call-store trap proofs with current main');git('update-ref','refs/heads/'+old['branch'],head,old['head']);git('push','origin','refs/heads/'+old['branch'])
for n in ['manifest.json','current-gate-v1.json','coordinator-ready-v1.json','PR-body-v1.md']:(N/n).write_bytes((oldD/n).read_bytes())
(N/'merge-v3.py').write_bytes((oldD/'merge-v3.py').read_bytes())
new=dict(old,head=head,base=base,tree=tree,previous_head=old['head'],normal_descendant=True,reviewed_implementation_unchanged=True,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(N/'published-v1.json').write_text(json.dumps(new,indent=2)+'\n')
review.update(head=head,reviewed_head='0715e9307b1e9bb035a990d27ddf53291e39d3da',carry_basis='All15originalreviewedfiles and1149imported sources/config remain exact; parent-only additive main reconciliation.');(N/'peer-review-v1.json').write_text(json.dumps(review,indent=2)+'\n')
(N/'reconciliation-receipt-v1.json').write_text(json.dumps({'status':'passed_additive_current_main_reconciliation','old_head':old['head'],'head':head,'base':base,'reviewed_source_count':len(old['source_hashes']),'closure_sources_exact':len(old['closure_source_hashes']),'config_exact':True,'old_CI_preserved':True,'fresh_CI_required':True,'full_goal_complete':False},indent=2)+'\n');print(json.dumps(dict(head=head,base=base,tree=tree)),flush=True)
