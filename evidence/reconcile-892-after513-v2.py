from pathlib import Path
import json,subprocess,hashlib,os,time,datetime
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029'
def run(*a,env=None):return subprocess.check_output(a,cwd=B,env=env,text=True).strip()
for _ in range(360):
 if (E/'513-recovered-landed-v1.json').exists():break
 time.sleep(10)
else:raise RuntimeError('Inspect513finaldelivery; no parent receipt arrived')
parent=json.loads((E/'513-recovered-landed-v1.json').read_text());assert parent['status']=='landed' and parent['tree_equal']
old=json.loads((E/'production-independent-delivery-prepared-v2.json').read_text())
run('git','fetch','origin','main');base=run('gh','api','repos/eth-act/clifv/commits/main','--jq','.sha');assert base==parent['merged'],'Inspect additional main drift'
assert run('git','ls-remote','origin','refs/heads/'+old['branch']).split()[0]==old['published_source']
idx=E/'892-after513-current.index';assert not idx.exists();env=dict(os.environ,GIT_INDEX_FILE=str(idx));run('git','read-tree',base,env=env)
for name,h in old['source_hashes'].items():
 data=subprocess.check_output(['git','show',old['published_source']+':'+name],cwd=B)
 assert hashlib.sha256(data).hexdigest()==h
 blob=run('git','rev-parse',old['published_source']+':'+name)
 run('git','update-index','--add','--cacheinfo','100644,'+blob+','+name,env=env)
tree=run('git','write-tree',env=env);idx.unlink()
assert set(run('git','diff','--name-only',base,tree).splitlines())==set(old['source_hashes'])
run('git','diff','--check',base,tree)
head=run('git','commit-tree',tree,'-p',base,'-p',old['published_source'],'-m','Reconcile production activation with stable outcome interfaces')
run('git','push','origin',head+':refs/heads/'+old['branch'])
r=dict(old);r.update(status='reconciled_pending_current_context',published_source=head,previous_source=old['published_source'],base=base,tree=tree,expected_main_tree=run('git','rev-parse',base+'^{tree}'),validated_source=base,parent='513-recovered-landed-v1.json',validation='892-current-main-context-v1/reviewed-state-v1.json',reviewed_implementation_unchanged=True,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(E/'production-independent-delivery-prepared-v3.json').write_text(json.dumps(r,indent=2)+'\n')
review=json.loads((E/'production-independent-peer-review-v2.json').read_text());review.update(published_source=head,reviewed_implementation_unchanged=True,carry_policy='All18reviewedimplementationfilesremainbyte-identical; currentcontext/CI/treegatesremainmandatory.')
(E/'production-independent-peer-review-v3.json').write_text(json.dumps(review,indent=2)+'\n')
c=json.loads((E/'production-independent-delivery-config-v2.json').read_text());c.update(prepared='production-independent-delivery-prepared-v3.json',parent=r['parent'],review='production-independent-peer-review-v3.json',validation=r['validation'],requires_validation_receipt=True)
(E/'production-independent-delivery-config-v3.json').write_text(json.dumps(c,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['published_source','base','tree','reviewed_implementation_unchanged']}),flush=True)
