from pathlib import Path
import json,hashlib,subprocess,datetime
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';D=E/'513-standalone-current-main-v1'
def run(*a):return subprocess.check_output(a,cwd=B,text=True).strip()
pre=json.loads((E/'513-independent-delivery-prepared-v5.json').read_text())
state=json.loads((D/'state-ci-v4.json').read_text());ctx=json.loads((D/'context-ci-v4.json').read_text())
assert state['status']=='passed' and state['candidate_kernels']==7
assert state['exact_elaborated_types']==8 and state['exact_axiom_sets']==8
assert state['old_public_headers']==372 and state['consumer_bodies']==203 and state['moved_declarations']==8
assert run('gh','pr','view','513','--json','headRefOid','--jq','.headRefOid')==pre['published_source']
assert run('gh','api','repos/eth-act/clifv/commits/main','--jq','.sha')==pre['base']
assert run('git','rev-parse',pre['published_source']+'^{tree}')==pre['tree']
closure={}
for stage,ref in [('baseline',pre['base']),('candidate',pre['published_source'])]:
 sources=ctx['stages'][stage]['source_hashes'];closure[stage]={}
 for name,h in sources.items():
  if not name.startswith('FV/'):continue
  data=subprocess.check_output(['git','show',ref+':'+name],cwd=B)
  assert hashlib.sha256(data).hexdigest()==h,(stage,name)
  closure[stage][name]=h
for name,h in pre['source_hashes'].items():
 assert hashlib.sha256(subprocess.check_output(['git','show',pre['published_source']+':'+name],cwd=B)).hexdigest()==h
out=dict(status='passed',candidate_source=pre['published_source'],candidate_tree=pre['tree'],baseline_tree=pre['expected_main_tree'],source_hashes=pre['source_hashes'],exact_context=True,kernel_gate_passed=True,old_headers_exact=True,old_axiom_sets_exact=True,full_goal_complete=False,scope=state['scope'],kernel_receipt='513-standalone-current-main-v1/state-ci-v4.json',kernel_receipt_sha256=hashlib.sha256((D/'state-ci-v4.json').read_bytes()).hexdigest(),context_source_hashes=closure,exact_type_axiom_roots=8,old_headers=372,consumer_bodies=203,moved_declarations=8,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
path=E/'513-independent-current-context-v1/reviewed-state-v1.json';path.parent.mkdir(exist_ok=True);assert not path.exists();path.write_text(json.dumps(out,indent=2)+'\n')
pre.update(import_source_closure=closure['candidate'],import_source_scope=state['scope'],focused_kernel_modules=7,exact_type_axiom_roots=8,old_headers_exact=372,consumer_bodies_exact=203,moved_declarations_exact=8,source_tree_unchanged=True)
(E/'513-independent-delivery-prepared-v5.json').write_text(json.dumps(pre,indent=2)+'\n')
print(json.dumps({'status':'passed','head':pre['published_source'],'candidate_sources':len(closure['candidate']),'full_goal_complete':False}))
