from pathlib import Path
import json,subprocess,time,hashlib,datetime
D=Path(__file__).resolve().parent;L=D/'publication-v1';M=json.loads((L/'published.json').read_text());R=json.loads((L/'peer-review.json').read_text());assert R['status']=='approved' and R['head']==M['head'];deadline=time.monotonic()+21600
while not (L/'CI-passed.json').exists():
 assert not (L/'CI-failed.json').exists(),'Exact-head CI failed'
 assert time.monotonic()<deadline,'CI wait timeout;no merge attempted'
 time.sleep(10)
CI=json.loads((L/'CI-passed.json').read_text());assert CI['head']==M['head'] and CI['tree']==M['tree'];required={'Quick checks','Build and compare','Check lost matches','Publish PR result'};assert set(CI['checks'])==required
for x in CI['checks'].values():assert x['status']=='COMPLETED' and x['conclusion']=='SUCCESS'
def run(args):return subprocess.check_output(args,cwd='/home/lee/clifv',text=True).strip()
try:
 deadline=time.monotonic()+300
 while True:
  p=json.loads(run(['gh','pr','view','948','--repo','eth-act/clifv','--json','headRefOid,baseRefOid,state,mergeable,mergeCommit,statusCheckRollup']))
  assert p['state']=='OPEN' and p['headRefOid']==M['head'],p
  observed={x['name']:x for x in p['statusCheckRollup'] if x.get('name') in required};assert set(observed)==required;assert all(x.get('status')=='COMPLETED' and x.get('conclusion')=='SUCCESS' for x in observed.values()),observed
  actual=run(['gh','api','repos/eth-act/clifv/commits/main','--jq','.sha']);assert actual==M['base'] and p['baseRefOid']==M['base'],('Reconcile actual main drift',actual,p)
  if p['mergeable']=='MERGEABLE':break
  assert p['mergeable']=='UNKNOWN',p;assert time.monotonic()<deadline,'GitHub mergeability remains UNKNOWN';time.sleep(10)
 tested=run(['git','rev-parse',M['head']+'^{tree}']);assert tested==M['tree'];mt=run(['git','merge-tree','--write-tree',M['base'],M['head']]).splitlines()[0];assert mt==tested
 subprocess.run(['gh','pr','merge','948','--repo','eth-act/clifv','--squash','--match-head-commit',M['head']],check=True,cwd='/home/lee/clifv')
 p=json.loads(run(['gh','pr','view','948','--repo','eth-act/clifv','--json','state,mergeCommit,headRefOid,baseRefOid']));assert p['state']=='MERGED';merged=p['mergeCommit']['oid'];git=json.loads(run(['gh','api','repos/eth-act/clifv/git/commits/'+merged]));assert git['tree']['sha']==tested and [x['sha'] for x in git['parents']]==[M['base']],git
 receipt=dict(status='MERGED',pr=948,head=M['head'],base=M['base'],merge=merged,tested_tree=tested,merged_tree=git['tree']['sha'],tree_equal=True,checks=CI['checks'],review_sha256=hashlib.sha256((L/'peer-review.json').read_bytes()).hexdigest(),canonical_manifest_sha256=M['canonical_manifest_sha256'],source_hashes=M['source_hashes'],utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(L/'merged.json').write_text(json.dumps(receipt,indent=2)+'\n');print('MERGED',merged,'tree',tested,'all four checks passed',flush=True)
except BaseException as error:
 (L/'delivery-v3-stopped.json').write_text(json.dumps(dict(status='stopped',error=repr(error),head=M['head'],base=M['base']),indent=2)+'\n');raise
