from pathlib import Path
import datetime,hashlib,json,subprocess
B=Path('/home/lee/clifv');D=Path(__file__).resolve().parent
head='775f257026bb159c8b5feed2475446c56db3778b';base='2c6008540ece15aa8e2ae2813322247f0d67e48b';tree='371ed73529b5828ea7a3278c21542579879c8778'
required={'Quick checks','Build and compare','Check lost matches','Publish PR result'}
def call(args):return subprocess.check_output(args,cwd=B,text=True,timeout=60).strip()
def view():return json.loads(call(['gh','pr','view','949','--repo','eth-act/clifv','--json','state,headRefOid,baseRefOid,mergeable,mergeStateStatus,statusCheckRollup,mergeCommit']))
def save(name,data):
 data['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();(D/name).write_text(json.dumps(data,indent=2)+'\n')
try:
 receipt=json.loads((D/'CI-passed-v1.json').read_text());peer=json.loads((D/'peer-review.json').read_text())
 assert peer['status']=='approved' and peer['head']==head
 assert receipt['head']==head and receipt['base']==base and receipt['tested_tree']==tree and receipt['tree_equal']
 p=view();assert p['state']=='OPEN' and p['headRefOid']==head and p['baseRefOid']==base
 assert p['mergeable']=='MERGEABLE' and p['mergeStateStatus']=='CLEAN'
 checks={x['name']:x for x in p['statusCheckRollup']};assert required<=checks.keys()
 assert all(checks[x]['status']=='COMPLETED' and checks[x]['conclusion']=='SUCCESS' for x in required)
 assert call(['git','ls-remote','origin','refs/heads/main']).split()[0]==base
 assert call(['git','rev-parse',head+'^{tree}'])==tree
 assert call(['git','merge-tree','--write-tree',base,head]).splitlines()[0]==tree
 save('squash-precheck-v1.json',{'head':head,'base':base,'tested_tree':tree,'checks':checks,'peer_approved':True,'window':'A accepted via root; explicit start sent','full326':'mandatory subsequent full validation; not replaced by direct33','full_goal_complete':False})
 save('squash-operation-v1.json',{'status':'REMOTE_MERGE_REQUEST_STARTING','head':head,'base':base})
 output=call(['gh','pr','merge','949','--repo','eth-act/clifv','--squash','--match-head-commit',head]);(D/'squash-command-v1.log').write_text(output+'\n')
 p=view();assert p['state']=='MERGED';merged=p['mergeCommit']['oid'];actual_tree=json.loads(call(['gh','api','repos/eth-act/clifv/git/commits/'+merged]))['tree']['sha'];assert actual_tree==tree
 assert call(['git','ls-remote','origin','refs/heads/main']).split()[0]==merged
 save('landed-v1.json',{'status':'MERGED_EXACT_TESTED_TREE','PR':949,'source_head':head,'recorded_base':base,'merge_commit':merged,'tested_tree':tree,'merged_tree':actual_tree,'all_four_CI_passed':True,'peer_approved':True,'normal_modules':1831,'focused_kernels':30,'consumer_kernels':33,'audit_standard':17,'audit_fixed':1,'old_statements_AX_exact':13,'acceptance_sets':'expanded for eight earlier providers','full326':'open mandatory full validation','Main_activation':False,'full_goal_complete':False})
 print(json.dumps({'status':'merged','commit':merged,'tree':actual_tree}),flush=True)
except BaseException as exc:
 save('squash-failure-v1.json',{'status':'STOP_INSPECT_AUTHORITATIVE_REMOTE_STATE','error':repr(exc),'head':head,'base':base,'full_goal_complete':False});raise
