from pathlib import Path
import datetime,hashlib,json,shutil,subprocess,time
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029'
p=json.loads((e/'sret-868-independent-publication-v1.json').read_text());v=json.loads((e/p['proof_validation']).read_text());assert v['status']=='passed' and v['original_axiom_sets_exact']==12
head=p['source'];base=p['base'];tree=p['tree']
def run(*args):return subprocess.check_output(args,cwd=b,text=True).strip()
last=None
for poll in range(180):
 pr=json.loads(run('gh','pr','view','868','--repo','eth-act/clifv','--json','state,baseRefName,headRefOid,statusCheckRollup'))
 assert pr['state']=='OPEN' and pr['baseRefName']=='main'
 if pr['headRefOid']!=head:
  assert poll<6,'Remote head differs from the published candidate';time.sleep(10);continue
 checks=pr['statusCheckRollup'];states=[(x.get('name',x.get('context')),x.get('status',x.get('state')),x.get('conclusion')) for x in checks]
 if states!=last:print('CI',json.dumps(states),flush=True);last=states
 assert not [x for x in checks if x.get('conclusion') in ['FAILURE','CANCELLED','TIMED_OUT','ACTION_REQUIRED'] or x.get('state') in ['FAILURE','ERROR']],states
 if len(checks)>=4 and all(x.get('conclusion')=='SUCCESS' or x.get('state')=='SUCCESS' for x in checks):break
 time.sleep(20)
else:raise RuntimeError('The exact-head CI did not finish. Inspect existing runs before retrying.')
assert run('gh','api','repos/eth-act/clifv/commits/main','--jq','.sha')==base,'Main advanced. Reconcile the same packet before merging.'
assert run('git','rev-parse',head+'^{tree}')==tree
for name,digest in p['source_hashes'].items():assert hashlib.sha256(subprocess.check_output(['git','show',head+':'+name],cwd=b)).hexdigest()==digest
subprocess.run(['gh','pr','merge','868','--repo','eth-act/clifv','--squash','--match-head-commit',head],cwd=b,check=True)
pr=json.loads(run('gh','pr','view','868','--repo','eth-act/clifv','--json','state,mergeCommit'));assert pr['state']=='MERGED';merged=pr['mergeCommit']['oid']
subprocess.run(['git','fetch','origin','main'],cwd=b,check=True);assert run('git','rev-parse',merged+'^{tree}')==tree
receipt=dict(status='landed',pr=868,source=head,base=base,merged=merged,tested_tree=tree,tree_equal=True,source_hashes=p['source_hashes'],checks=checks,generic_roots=10,fixed_roots=2,proof_validation=p['proof_validation'],independent_delivery=True,full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(e/'sret-full-cfg-landed-v1.json').write_text(json.dumps(receipt,indent=2)+'\n')
root=Path(v['isolated_package']);assert root==e/'sret-868-independent-package-v1'
artifacts={str(f.relative_to(root)):hashlib.sha256(f.read_bytes()).hexdigest() for name in v['modules'] for ext in ['.olean','.ilean','.c'] if (f:=root/'.lake/build/lib/lean'/Path(name).with_suffix(ext)).exists()}
(e/'sret-868-independent-artifacts-v1.json').write_text(json.dumps(dict(artifacts=artifacts,cleanup='Only this isolated package build directory. Shared cache and source views remain.'),indent=2)+'\n')
shutil.rmtree(root/'.lake');print(json.dumps({k:receipt[k] for k in ['status','pr','source','merged','tested_tree','tree_equal']}),flush=True)
