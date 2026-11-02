from pathlib import Path
import datetime,json,subprocess,time
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031'
def run(*args):return subprocess.check_output(args,cwd=B,text=True).strip()
pre=json.loads((E/'860-independent-delivery-prepared-v1.json').read_text());review=json.loads((E/'860-independent-peer-review-v1.json').read_text());head=pre['publication_source'];source=pre['source'];base=pre['base'];tree=pre['tree'];assert review['publication_source']==head and review['verdict']=='no blocking defect' and pre['import_source_closure_equal']
assert run('git','-C',str(V),'rev-parse','HEAD')==source and not run('git','-C',str(V),'status','--porcelain')
required={'Quick checks','Build and compare','Check lost matches','Publish PR result'};previous=None
for poll in range(180):
 pr=json.loads(run('gh','pr','view','860','--repo','eth-act/clifv','--json','state,headRefOid,statusCheckRollup'))
 assert pr['state']=='OPEN' and pr['headRefOid']==head,pr
 checks=pr['statusCheckRollup'];byname={}
 for check in checks:
  name=check.get('name',check.get('context'))
  if name in required:
   prior=byname.get(name)
   if prior is None or check.get('startedAt','')>=prior.get('startedAt',''):byname[name]=check
 states={n:(c.get('status',c.get('state')),c.get('conclusion')) for n,c in byname.items()}
 if states!=previous:print('CI',json.dumps(states),flush=True);previous=states
 bad=[c for c in byname.values() if c.get('conclusion') in ['FAILURE','TIMED_OUT','ACTION_REQUIRED'] or c.get('state') in ['FAILURE','ERROR']];assert not bad,bad
 if required==set(byname) and all(c.get('conclusion')=='SUCCESS' or c.get('state')=='SUCCESS' for c in byname.values()):break
 time.sleep(20)
else:raise RuntimeError('Inspect the actual existing CI runs before retrying.')
assert run('gh','api','repos/eth-act/clifv/commits/main','--jq','.sha')==base,'Inspect main drift before merging'
# This remote-only publication leaves the healthy local snapshot unchanged.
assert run('git','-C',str(V),'rev-parse','HEAD')==source and not run('git','-C',str(V),'status','--porcelain')
assert run('git','rev-parse',head+'^{tree}')==tree
assert run('git','ls-remote','origin','refs/heads/'+pre['branch']).split()[0]==head
run('gh','pr','merge','860','--repo','eth-act/clifv','--squash','--match-head-commit',head)
pr=json.loads(run('gh','pr','view','860','--repo','eth-act/clifv','--json','state,mergeCommit,mergedAt'));assert pr['state']=='MERGED';merged=pr['mergeCommit']['oid'];run('git','fetch','origin','main');assert run('git','rev-parse',merged+'^{tree}')==tree
receipt=dict(status='landed',pr=860,source=source,source_role='Validated frozen proof source and legacy delivery handoff head; published_source identifies the exact PR head.',published_source=head,base=base,merged=merged,tested_tree=tree,tree_equal=True,import_source_closure_equal=True,import_source_count=len(pre['import_source_closure']),checks=list(byname.values()),peer_review='860-independent-peer-review-v1.json',importer_receipt='return-pin-call-consumer-current-main-state-recovery12-r1.json',independent_delivery=True,full_local_gate='Healthy recovery3477137 continues on the frozen validated snapshot. Its eventual stale push cannot overwrite the newer remote ref. The existing dependent queue waits for its actual exit and verifies this source head before starting865.',full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(E/'return-pin-call-consumer-landed-v1.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ['status','pr','source','published_source','merged','tested_tree','tree_equal','import_source_count']}),flush=True)
assert run('git','-C',str(V),'rev-parse','HEAD')==source and not run('git','-C',str(V),'status','--porcelain')
