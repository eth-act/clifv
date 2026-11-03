from pathlib import Path
import datetime,fcntl,hashlib,json,subprocess,time
D=Path(__file__).resolve().parent;B=Path('/home/lee/clifv');P=json.loads((D/'published-v1.json').read_text());head=P['head'];base=P['base'];tree=P['tree'];pr=935
lock=(D/'merge-owner.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);assert not (D/'landed-v1.json').exists()
def cmd(*args):return subprocess.check_output(args,cwd=B,text=True).strip()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
M=json.loads((D/'manifest.json').read_text());C=D.parent/'canonical-v1/manifest.json';G=json.loads(C.read_text());assert sha(C)==M['canonical_checkpoint_sha256'];assert G['status']=='passed-current-c4f-source-transport' and G['base']==base and len(G['source_hashes'])==156 and G['new_standard_roots']==4
review=json.loads((D/'peer-review-v1.json').read_text());assert review['head']==head and review['verdict']=='no blocking defect';assert review['method']=='ONE QUICK, DIRTY, CHEAP direct peer review; no builds or review agents'
required={'Quick checks','Build and compare','Check lost matches','Publish PR result'};last=None
for unused in range(480):
 state=json.loads(cmd('gh','pr','view',str(pr),'--repo','eth-act/clifv','--json','state,headRefOid,baseRefName,statusCheckRollup'));assert state['state']=='OPEN' and state['headRefOid']==head and state['baseRefName']=='main',state
 by={}
 for check in state['statusCheckRollup']:
  name=check.get('name',check.get('context'))
  if name in required and (name not in by or check.get('startedAt','')>=by[name].get('startedAt','')):by[name]=check
 now={n:(c.get('status',c.get('state')),c.get('conclusion')) for n,c in by.items()}
 if now!=last:print('CI',pr,json.dumps(now),flush=True);last=now
 assert not any(c.get('conclusion') in ['FAILURE','TIMED_OUT','ACTION_REQUIRED','CANCELLED'] or c.get('state') in ['FAILURE','ERROR'] for c in by.values()),'Inspect exact-head CI failure; no merge'
 if required==set(by) and all(c.get('conclusion')=='SUCCESS' or c.get('state')=='SUCCESS' for c in by.values()):break
 time.sleep(15)
else:raise RuntimeError('CI did not finish; no merge')
cmd('git','fetch','origin','main');assert cmd('gh','api','repos/eth-act/clifv/commits/main','--jq','.sha')==base,'Main advanced; reconcile normally';assert cmd('git','rev-parse','origin/main')==base
assert cmd('git','merge-tree','--write-tree',head,base).splitlines()[0]==tree;assert cmd('git','rev-parse',head+'^{tree}')==tree
for name,h in {**G['source_hashes'],**P['source_hashes']}.items():assert hashlib.sha256(subprocess.check_output(['git','show',head+':'+name],cwd=B)).hexdigest()==h,name
cmd('git','fetch','origin',f'refs/pull/{pr}/merge:refs/ai-coord/pr-{pr}-tested-merge');tested=cmd('git','rev-parse',f'refs/ai-coord/pr-{pr}-tested-merge');parents=cmd('git','rev-list','--parents','-n','1',tested).split()[1:];assert set(parents)=={base,head},parents;assert cmd('git','rev-parse',tested+'^{tree}')==tree
cmd('gh','pr','merge',str(pr),'--repo','eth-act/clifv','--squash','--match-head-commit',head)
s=json.loads(cmd('gh','pr','view',str(pr),'--repo','eth-act/clifv','--json','state,headRefOid,mergeCommit'));assert s['state']=='MERGED' and s['headRefOid']==head;merged=s['mergeCommit']['oid'];cmd('git','fetch','origin','main');assert cmd('git','rev-parse',merged+'^{tree}')==tree
receipt={'status':'landed','pr':pr,'source':head,'base':base,'merged':merged,'tested_merge':tested,'tested_tree':tree,'tree_equal':True,'import_source_count':156,'source_hashes':P['source_hashes'],'canonical_sha256':sha(C),'checks':list(by.values()),'direct_review':review,'complete_full_program_mapping':False,'production_activation':False,'full_goal_complete':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(D/'landed-v1.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ['status','pr','source','merged','tested_tree','tree_equal','import_source_count']}),flush=True)
