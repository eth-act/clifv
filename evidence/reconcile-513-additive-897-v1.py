from pathlib import Path
import json,subprocess,datetime,hashlib
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029'
old=json.loads((E/'513-independent-delivery-prepared-v4.json').read_text())
def run(*a):return subprocess.check_output(a,cwd=B,text=True).strip()
run('git','fetch','origin','main');base=run('git','rev-parse','origin/main')
assert base==run('gh','api','repos/eth-act/clifv/commits/main','--jq','.sha')
assert base=='7c979e18457fd49d96b6f88f5f364ef62490f94c', 'Inspect new main drift'
assert run('git','ls-remote','origin','refs/heads/'+old['branch']).split()[0]==old['published_source']
tree=run('git','merge-tree','--write-tree',old['published_source'],base).splitlines()[0]
for n,h in old['source_hashes'].items():
 assert hashlib.sha256(subprocess.check_output(['git','show',tree+':'+n],cwd=B)).hexdigest()==h
oldpatch=subprocess.check_output(['git','diff',old['base'],old['tree']],cwd=B)
assert subprocess.check_output(['git','diff',base,tree],cwd=B)==oldpatch
run('git','diff','--check',base,tree)
head=run('git','commit-tree',tree,'-p',base,'-p',old['published_source'],'-m','Reconcile stable outcomes with additive comparison proofs')
run('git','push','origin',head+':refs/heads/'+old['branch'])
r=dict(old);r.update(previous_source=old['published_source'],published_source=head,base=base,tree=tree,expected_main_tree=run('git','rev-parse',base+'^{tree}'),validated_source=base,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),reviewed_implementation_unchanged=True)
(E/'513-independent-delivery-prepared-v5.json').write_text(json.dumps(r,indent=2)+'\n')
review=json.loads((E/'513-independent-peer-review-v4.json').read_text());review.update(published_source=head,reviewed_implementation_unchanged=True)
(E/'513-independent-peer-review-v5.json').write_text(json.dumps(review,indent=2)+'\n')
c=json.loads((E/'513-independent-delivery-config-v4.json').read_text());c.update(prepared='513-independent-delivery-prepared-v5.json',review='513-independent-peer-review-v5.json')
(E/'513-independent-delivery-config-v5.json').write_text(json.dumps(c,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['published_source','base','tree','reviewed_implementation_unchanged']}))
