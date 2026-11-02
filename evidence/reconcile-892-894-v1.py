from pathlib import Path
import json,subprocess,hashlib,datetime
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';old=json.loads((E/'production-independent-delivery-prepared-v1.json').read_text())
def git(*args):return subprocess.check_output(['git',*args],cwd=B,text=True).strip()
assert not Path('/proc/2979547').exists(),'The old delivery owner must be terminal'
base=git('rev-parse','origin/main');assert base=='3a6719b44b0e6b38e24cd0de82655f93b78272a9'
changed=git('diff','--name-only',old['base'],base).splitlines()
def data(ref,n):return subprocess.check_output(['git','show',ref+':'+n],cwd=B)
def body(value):return b'\n'.join(l for l in value.splitlines() if not l.startswith(b'import '))
for n in changed:assert body(data(old['base'],n))==body(data(base,n)),('Non-import change requires review',n)
headold=old['published_source'];branch=old['branch'];assert git('ls-remote','origin','refs/heads/'+branch).split()[0]==headold
tree=git('merge-tree','--write-tree',headold,base).splitlines()[0];assert len(tree)==40
assert set(git('diff','--name-only',base,tree).splitlines())==set(old['source_hashes'])
for n,h in old['source_hashes'].items():assert hashlib.sha256(data(tree,n)).hexdigest()==h
head=git('commit-tree',tree,'-p',headold,'-p',base,'-m','Reconcile proved production consumers with current import cleanup')
git('merge-base','--is-ancestor',headold,head);subprocess.run(['git','push','origin',head+':refs/heads/'+branch],cwd=B,check=True)
r=dict(old,status='reconciled_pending_current_context',published_source=head,previous_source=headold,base=base,tree=tree,expected_main_tree=git('rev-parse',base+'^{tree}'),historical_validation=old['validation'],validation='892-current-main-context-v1/reviewed-state-v1.json',implementation_files_unchanged=True,import_only_base_delta=changed,requires_current_context=True,import_source_closure_equal=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(E/'production-independent-delivery-prepared-v2.json').write_text(json.dumps(r,indent=2)+'\n')
review=json.loads((E/'892-peer-review-historical-90c51c88-v1.json').read_text());review.update(published_source=head,reviewed_source=headold,historical_head=False,implementation_files_unchanged=True,base_delta_import_only=True,carry_policy='Root confirmed existing single direct review carries over unchanged18-file implementation and verified import-only base delta. Actual current-context and exact-head CI/tree gates remain mandatory.')
(E/'production-independent-peer-review-v2.json').write_text(json.dumps(review,indent=2)+'\n')
config=json.loads((E/'production-independent-delivery-config-v1.json').read_text());config.update(prepared='production-independent-delivery-prepared-v2.json',review='production-independent-peer-review-v2.json',validation=r['validation'],requires_validation_receipt=True)
(E/'production-independent-delivery-config-v2.json').write_text(json.dumps(config,indent=2)+'\n')
print(json.dumps(dict(status=r['status'],pr=892,head=head,base=base,tree=tree,implementation_files_unchanged=True,import_only_files=len(changed))),flush=True)
