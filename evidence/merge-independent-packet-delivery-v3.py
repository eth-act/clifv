from pathlib import Path
import datetime,json,os,subprocess,sys,time
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031';config=json.loads(Path(sys.argv[1]).read_text());pre=json.loads((E/config['prepared']).read_text());pr_number=config['pr'];head=pre['published_source'];tree=pre['tree']
owner=dict(pid=os.getpid(),label='merge-independent-packet-delivery-v3.py',pr=pr_number,head=head,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(E/f'{pr_number}-independent-delivery-owner-v1.json').write_text(json.dumps(owner,indent=2)+'\n')
def run(*args):return subprocess.check_output(args,cwd=B,text=True).strip()
# Parent publication and direct review are gates. Elapsed time is not approval.
for poll in range(720):
 if (E/config['parent']).exists() and (E/config['review']).exists():break
 time.sleep(10)
else:raise RuntimeError('The actual parent receipt or direct review is absent; inspect the existing delivery.')
parent=json.loads((E/config['parent']).read_text());review=json.loads((E/config['review']).read_text());assert parent['status']=='landed' and parent['tree_equal'];assert review['published_source']==head and review['verdict']=='no blocking defect'
# A current-context receipt is mandatory for recovered production deliveries.
if config.get('requires_validation_receipt'):
 validation_path=E/config['validation']
 assert validation_path.is_file(), 'Current-context validation receipt is absent'
 validation=json.loads(validation_path.read_text())
 assert validation['status']=='passed', 'Current-context validation did not pass'
 assert validation['candidate_source']==head, 'Validation head differs from published head'
 assert validation['candidate_tree']==tree, 'Validation tree differs from tested tree'
 assert validation['baseline_tree']==pre['expected_main_tree'], 'Validation baseline differs from publication baseline'
 assert validation['source_hashes']==pre['source_hashes'], 'Validated implementation source hashes differ'
 assert validation['old_headers_exact'] and validation['old_axiom_sets_exact']
 assert validation['exact_context'] and validation['kernel_gate_passed']
 assert validation.get('full_goal_complete') is False
 validation_sha=__import__('hashlib').sha256(validation_path.read_bytes()).hexdigest()
else:
 raise RuntimeError('This controller requires explicit current-context validation policy')
base=run('gh','api','repos/eth-act/clifv/commits/main','--jq','.sha');run('git','fetch','origin','main');run('git','merge-base','--is-ancestor',parent['merged'],base)
assert run('git','rev-parse',base+'^{tree}')==pre['expected_main_tree'],'Inspect actual main drift before delivery'
assert run('git','merge-tree','--write-tree',head,base).splitlines()[0]==tree,'Current main must produce the exact tested candidate tree'
run('gh','pr','edit',str(pr_number),'--repo','eth-act/clifv','--base','main')
required={'Quick checks','Build and compare','Check lost matches','Publish PR result'};previous=None
for poll in range(180):
 pr=json.loads(run('gh','pr','view',str(pr_number),'--repo','eth-act/clifv','--json','state,headRefOid,statusCheckRollup,baseRefName'))
 assert pr['state']=='OPEN' and pr['headRefOid']==head and pr['baseRefName']=='main',pr
 byname={}
 for check in pr['statusCheckRollup']:
  name=check.get('name',check.get('context'))
  if name in required:
   old=byname.get(name)
   if old is None or check.get('startedAt','')>=old.get('startedAt',''):byname[name]=check
 states={n:(c.get('status',c.get('state')),c.get('conclusion')) for n,c in byname.items()}
 if states!=previous:print('CI',pr_number,json.dumps(states),flush=True);previous=states
 assert not [c for c in byname.values() if c.get('conclusion') in ['FAILURE','TIMED_OUT','ACTION_REQUIRED'] or c.get('state') in ['FAILURE','ERROR']]
 if required==set(byname) and all(c.get('conclusion')=='SUCCESS' or c.get('state')=='SUCCESS' for c in byname.values()):break
 time.sleep(20)
else:raise RuntimeError('Inspect the existing exact-head CI runs before retrying')
assert run('gh','api','repos/eth-act/clifv/commits/main','--jq','.sha')==base,'Main advanced during CI; inspect before merging'
assert run('git','rev-parse',head+'^{tree}')==tree
run('gh','pr','merge',str(pr_number),'--repo','eth-act/clifv','--squash','--match-head-commit',head)
pr=json.loads(run('gh','pr','view',str(pr_number),'--repo','eth-act/clifv','--json','state,mergeCommit,headRefOid'));assert pr['state']=='MERGED' and pr['headRefOid']==head;merged=pr['mergeCommit']['oid'];run('git','fetch','origin','main');assert run('git','rev-parse',merged+'^{tree}')==tree
receipt=dict(status='landed',pr=pr_number,branch=pre['branch'],source=head,published_source=head,validated_source=pre['validated_source'],base=base,merged=merged,tested_tree=tree,tree_equal=True,source_hashes=pre['source_hashes'],import_source_closure_equal=True,import_source_count=len(pre['import_source_closure']),validation=pre['validation'],peer_review=config['review'],checks=list(byname.values()),independent_delivery=True,full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());receipt.update(validation_receipt=config['validation'],validation_receipt_sha256=validation_sha);receipt.update({k:pre[k] for k in ['import_source_scope','focused_kernel_modules','exact_type_axiom_roots','old_headers_exact','consumer_bodies_exact','moved_declarations_exact','source_tree_unchanged'] if k in pre});(E/config['landed']).write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ['status','pr','source','merged','tested_tree','tree_equal','import_source_count']}),flush=True)
