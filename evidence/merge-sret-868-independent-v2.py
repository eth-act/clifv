from pathlib import Path
import datetime,hashlib,json,shutil,subprocess,time
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029'
p=json.loads((e/'sret-868-independent-publication-v1.json').read_text());v=json.loads((e/p['proof_validation']).read_text());assert v['status']=='passed' and v['original_axiom_sets_exact']==12
head=p['source'];base=p['base'];tree=p['tree']
def run(*args):return subprocess.check_output(args,cwd=b,text=True).strip()
last=None
pinned={41389500606:{'Quick checks'},41389500586:{'Build and compare','Check lost matches','Publish PR result'}}
for poll in range(180):
 pr=json.loads(run('gh','pr','view','868','--repo','eth-act/clifv','--json','state,baseRefName,headRefOid'))
 assert pr['state']=='OPEN' and pr['baseRefName']=='main' and pr['headRefOid']==head
 checks=[];finished=True
 for run_id,names in pinned.items():
  workflow=json.loads(run('gh','api',f'repos/eth-act/clifv/actions/runs/{run_id}'))
  assert workflow['head_sha']==head and workflow['event']=='pull_request'
  assert any(x['number']==868 and x['base']['ref']=='main' and x['base']['sha']==base and x['head']['sha']==head for x in workflow['pull_requests'])
  if workflow['status']=='completed':assert workflow['conclusion']=='success',workflow['conclusion']
  else:finished=False
  jobs=json.loads(run('gh','api',f'repos/eth-act/clifv/actions/runs/{run_id}/jobs','--paginate'))['jobs']
  selected=[x for x in jobs if x['name'] in names]
  if {x['name'] for x in selected}!=names:finished=False
  for job in selected:
   assert job['status']!='completed' or job['conclusion']=='success',(job['name'],job['conclusion'])
   if job['status']!='completed':finished=False
   checks.append(dict(name=job['name'],status=job['status'].upper(),conclusion=(job['conclusion'] or '').upper(),detailsUrl=job['html_url'],run_id=run_id))
 states=[(x['name'],x['status'],x['conclusion']) for x in checks]
 if states!=last:print('CI',json.dumps(states),flush=True);last=states
 if finished and len(checks)==4:break
 time.sleep(20)
else:raise RuntimeError('The pinned exact-head CI did not finish. Inspect these same runs before retrying.')
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
