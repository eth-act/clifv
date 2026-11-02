from pathlib import Path
import json,subprocess,hashlib,datetime
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029'
old=json.loads((E/'production-independent-delivery-prepared-v3.json').read_text())
migration=json.loads((E/'892-joint-current-context-v2/current-main-migration-v4/preparation-receipt.json').read_text())
def run(*a):return subprocess.check_output(a,cwd=B,text=True).strip()
run('git','fetch','origin','main');base=run('gh','api','repos/eth-act/clifv/commits/main','--jq','.sha');assert base==migration['actual_main'],'Inspect later main delta'
assert run('git','ls-remote','origin','refs/heads/'+old['branch']).split()[0]==old['published_source']
tree=run('git','merge-tree','--write-tree',old['published_source'],base).splitlines()[0]
assert tree==migration['new_joint_tree']
for n,h in old['source_hashes'].items():assert hashlib.sha256(subprocess.check_output(['git','show',tree+':'+n],cwd=B)).hexdigest()==h
assert set(run('git','diff','--name-only',base,tree).splitlines())==set(old['source_hashes'])
assert subprocess.check_output(['git','diff',base,tree],cwd=B)==subprocess.check_output(['git','diff',old['base'],old['tree']],cwd=B)
run('git','diff','--check',base,tree)
head=run('git','commit-tree',tree,'-p',base,'-p',old['published_source'],'-m','Reconcile default activation with landed control-flow proofs')
run('git','push','origin',head+':refs/heads/'+old['branch'])
r=dict(old);r.update(status='reconciled_pending_current_context',published_source=head,previous_source=old['published_source'],base=base,tree=tree,expected_main_tree=run('git','rev-parse',base+'^{tree}'),validated_source=base,validation='892-joint-current-context-v2/reviewed-publication-state-v4.json',reviewed_implementation_unchanged=True,shared_dependency_delta='884-shared-dependency-delta-v1.json',utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(E/'production-independent-delivery-prepared-v4.json').write_text(json.dumps(r,indent=2)+'\n')
review=json.loads((E/'production-independent-peer-review-v3.json').read_text());review.update(published_source=head,reviewed_implementation_unchanged=True,actual_source_context_pending=True)
(E/'production-independent-peer-review-v4.json').write_text(json.dumps(review,indent=2)+'\n')
c=json.loads((E/'production-independent-delivery-config-v3.json').read_text());c.update(prepared='production-independent-delivery-prepared-v4.json',review='production-independent-peer-review-v4.json',validation=r['validation'])
(E/'production-independent-delivery-config-v4.json').write_text(json.dumps(c,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['published_source','base','tree','reviewed_implementation_unchanged']}),flush=True)
