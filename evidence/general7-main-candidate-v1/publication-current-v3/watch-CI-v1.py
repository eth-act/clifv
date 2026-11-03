from pathlib import Path
import datetime,json,subprocess,time,hashlib,re
D=Path(__file__).resolve().parent;G=Path('/home/lee/clifv/.worktrees/loop-20261102');H='775f257026bb159c8b5feed2475446c56db3778b';base='2c6008540ece15aa8e2ae2813322247f0d67e48b';wanted={'Quick checks','Build and compare','Check lost matches','Publish PR result'};observed=[];previous=None;deadline=time.monotonic()+21600
run=lambda args:subprocess.check_output(args,cwd=G,text=True).strip()
try:
 while time.monotonic()<deadline:
  view=json.loads(run(['gh','pr','view','949','--repo','eth-act/clifv','--json','state,headRefOid,baseRefOid,statusCheckRollup,mergeable,url']));assert view['headRefOid']==H,('Head changed',view);assert view['state']=='OPEN',('PR state changed',view);assert view['baseRefOid']==base,('Actual PR base changed; reconcile normally',view['baseRefOid'])
  checks={}
  for r in view['statusCheckRollup']:
   if r.get('name') not in wanted:continue
   n=r['name']
   if n not in checks or r.get('startedAt','')>checks[n].get('startedAt',''):checks[n]=r
  now={n:(r.get('status'),r.get('conclusion')) for n,r in checks.items()}
  if now!=previous:
   observed.append({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'PR_view':view});(D/'CI-observations-v1.json').write_text(json.dumps(observed,indent=2)+'\n');previous=now
  assert not any(r.get('status')=='COMPLETED' and r.get('conclusion')!='SUCCESS' for r in checks.values()),('Required exact-head check failed',now)
  if wanted==set(checks) and all(r.get('status')=='COMPLETED' and r.get('conclusion')=='SUCCESS' for r in checks.values()):
   actual=run(['gh','api','repos/eth-act/clifv/commits/main','--jq','.sha']);assert actual==base,('Actual main drift',actual);remote=json.loads(run(['gh','api','repos/eth-act/clifv/git/commits/'+H]));tree=run(['git','rev-parse',H+'^{tree}']);assert remote['tree']['sha']==tree and [p['sha'] for p in remote['parents']]==[base];merge_tree=run(['git','merge-tree','--write-tree',base,H]).splitlines()[0];assert merge_tree==tree;data={'status':'ALL_FOUR_EXACT_HEAD_CI_PASSED_AND_TESTED_TREE_BOUND;NO_MERGE','PR':949,'head':H,'base':base,'actual_main':actual,'tested_tree':tree,'remote_head_tree':remote['tree']['sha'],'candidate_merge_tree':merge_tree,'tree_equal':True,'checks':checks,'peer_review_required_separately':True,'mergeable':view['mergeable'],'manifest_sha256':hashlib.sha256((D/'manifest.json').read_bytes()).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(D/'CI-passed-v1.json').write_text(json.dumps(data,indent=2)+'\n');print('PR949 all four exact-head CI checks passed; tested tree',tree,flush=True);break
  time.sleep(15)
 else:raise TimeoutError('All four checks did not pass within21600 seconds; no merge')
except BaseException as e:
 (D/'CI-stopped-v1.json').write_text(json.dumps({'status':'STOPPED;NO_MERGE','head':H,'base':base,'error':repr(e),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},indent=2)+'\n');raise
