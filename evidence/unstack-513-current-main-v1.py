from pathlib import Path
import json,os,subprocess,hashlib,datetime
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';old=json.loads((E/'513-recovered-publication-v2.json').read_text());hist=json.loads((E/'513-delivery-prepared-v1/prepared-state.json').read_text())
def git(*a,env=None):return subprocess.check_output(['git',*a],cwd=B,env=env,text=True).strip()
git('fetch','origin','main');base=git('rev-parse','origin/main');assert base==subprocess.check_output(['gh','api','repos/eth-act/clifv/commits/main','--jq','.sha'],cwd=B,text=True).strip()
assert git('ls-remote','origin','refs/heads/'+old['branch']).split()[0]==old['head']
idx=E/'513-standalone-current.index';assert not idx.exists();env=dict(os.environ,GIT_INDEX_FILE=str(idx));git('read-tree',base,env=env)
for n,h in old['source_hashes'].items():
 data=subprocess.check_output(['git','show',old['head']+':'+n],cwd=B);assert hashlib.sha256(data).hexdigest()==h
 blob=git('rev-parse',old['head']+':'+n);git('update-index','--add','--cacheinfo','100644,'+blob+','+n,env=env)
tree=git('write-tree',env=env);idx.unlink();assert tree=='115baa5cc12179216ffb6ef94cf61d1d1c993ba6','Match the independently prepared current validation tree'
assert set(git('diff','--name-only',base,tree).splitlines())==set(old['source_hashes'])
patch=subprocess.check_output(['git','diff',base,tree],cwd=B);assert patch==subprocess.check_output(['git','diff',hist['prospective_production_parent'],hist['prepared_head']],cwd=B)
git('diff','--check',base,tree)
head=git('commit-tree',tree,'-p',base,'-p',old['head'],'-m','Deliver stable outcome interfaces independently on current main')
git('merge-base','--is-ancestor',old['head'],head);git('push','origin',head+':refs/heads/'+old['branch'])
subprocess.run(['gh','pr','edit','513','--repo','eth-act/clifv','--base','main'],cwd=B,check=True)
r=dict(status='reconciled_pending_current_context',pr=513,branch=old['branch'],published_source=head,previous_source=old['head'],base=base,tree=tree,expected_main_tree=git('rev-parse',base+'^{tree}'),source_hashes=old['source_hashes'],validated_source=base,parent='sret-complete-execution-landed-v1.json',parent_is_baseline_anchor_not_892=True,implementation_dependency_on892=False,source_patch_identical=True,patch_sha256=hashlib.sha256(patch).hexdigest(),validation='513-independent-current-context-v1/reviewed-state-v1.json',import_source_scope='Fresh complete focused project context; full207-file affected validation remains a separate obligation.',full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(E/'513-independent-delivery-prepared-v4.json').write_text(json.dumps(r,indent=2)+'\n');review=json.loads((E/'513-peer-review-historical-e5a094f4-v1.json').read_text());review.update(published_source=head,reviewed_source=hist['prepared_head'],historical_head=False,source_patch_identical=True,patch_sha256=r['patch_sha256'],carry_policy='The complete reviewed207-file patch is byte-identical. Only normal ancestry/baseline reconciliation changed. Fresh context,CI and tree gates remain.');(E/'513-independent-peer-review-v4.json').write_text(json.dumps(review,indent=2)+'\n');config=dict(pr=513,prepared='513-independent-delivery-prepared-v4.json',parent=r['parent'],review='513-independent-peer-review-v4.json',validation=r['validation'],requires_validation_receipt=True,landed='513-recovered-landed-v1.json');(E/'513-independent-delivery-config-v4.json').write_text(json.dumps(config,indent=2)+'\n');print(json.dumps(dict(pr=513,head=head,base=base,tree=tree,reviewed_patch_identical=True,independent_of892=True)),flush=True)
