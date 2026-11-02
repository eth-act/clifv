from pathlib import Path
import datetime,fcntl,hashlib,json,os,subprocess,time
D=Path(__file__).resolve().parent;B=Path('/home/lee/clifv');P=json.loads((D/'standalone-class-published-v1.json').read_text());head=P['head'];base=P['base'];tree=P['tree'];pr=P['pr'];L=D/'standalone-class-landed-v1.json';assert not L.exists();lock=(D/'merge-owner.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
def cmd(*argv):return subprocess.check_output(argv,cwd=B,text=True).strip()
G=json.loads((D/'standalone-current-gate-v1/receipt.json').read_text());assert G['status']=='passed' and G['normal_provider_check'] and G['all_candidates_normal_keys'];assert hashlib.sha256((D/'standalone-current-gate-v1/receipt.json').read_bytes()).hexdigest()==P['current_context_gate_sha256'];assert G['owned_sources']==P['new_source_hashes'];assert G['source_hashes']==P['closure_source_hashes'];assert G['standard_roots']==44 and G['fixed_roots']==3
review=D/'standalone-class-peer-review-v1.json'
for _ in range(360):
 if review.exists():break
 time.sleep(10)
else:raise RuntimeError('The one direct review is absent; elapsed time is not approval')
R=json.loads(review.read_text());assert R['head']==head and R['verdict']=='no blocking defect';assert R['method']=='ONE QUICK, DIRTY, CHEAP direct peer review; no builds or review agents'
required={'Quick checks','Build and compare','Check lost matches','Publish PR result'};last=None
for _ in range(360):
 state=json.loads(cmd('gh','pr','view',str(pr),'--repo','eth-act/clifv','--json','state,headRefOid,baseRefName,statusCheckRollup'));assert state['state']=='OPEN' and state['headRefOid']==head and state['baseRefName']=='main'
 by={}
 for c in state['statusCheckRollup']:
  n=c.get('name',c.get('context'))
  if n in required and (n not in by or c.get('startedAt','')>=by[n].get('startedAt','')):by[n]=c
 current={n:(c.get('status',c.get('state')),c.get('conclusion')) for n,c in by.items()}
 if current!=last:print('CI',pr,json.dumps(current),flush=True);last=current
 assert not any(c.get('conclusion') in ['FAILURE','TIMED_OUT','ACTION_REQUIRED'] or c.get('state') in ['FAILURE','ERROR'] for c in by.values()),'Inspect current exact-head CI failures'
 if required==set(by) and all(c.get('conclusion')=='SUCCESS' or c.get('state')=='SUCCESS' for c in by.values()):break
 time.sleep(15)
else:raise RuntimeError('Inspect exact-head CI; no merge occurred')
cmd('git','fetch','origin','main');assert cmd('gh','api','repos/eth-act/clifv/commits/main','--jq','.sha')==base,'Actual main advanced; reconcile normally and refresh CI before merging';assert cmd('git','rev-parse','origin/main')==base
assert cmd('git','merge-tree','--write-tree',head,base).splitlines()[0]==tree;assert cmd('git','rev-parse',head+'^{tree}')==tree
for n,h in P['closure_source_hashes'].items():assert hashlib.sha256(subprocess.check_output(['git','show',head+':'+n],cwd=B)).hexdigest()==h,n
cmd('gh','pr','merge',str(pr),'--repo','eth-act/clifv','--squash','--match-head-commit',head)
state=json.loads(cmd('gh','pr','view',str(pr),'--repo','eth-act/clifv','--json','state,headRefOid,mergeCommit'));assert state['state']=='MERGED' and state['headRefOid']==head;merged=state['mergeCommit']['oid'];cmd('git','fetch','origin','main');assert cmd('git','rev-parse',merged+'^{tree}')==tree
receipt={'status':'landed','pr':pr,'source':head,'base':base,'merged':merged,'tested_tree':tree,'tree_equal':True,'import_source_count':len(P['closure_source_hashes']),'current_gate_sha256':P['current_context_gate_sha256'],'source_hashes':P['new_source_hashes'],'checks':list(by.values()),'direct_review':R,'old_source_files_unchanged':True,'production_activation':False,'full_goal_complete':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};L.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ['status','pr','source','merged','tested_tree','tree_equal','import_source_count']}),flush=True)
