from pathlib import Path
import json,subprocess,time,hashlib
D=Path(__file__).resolve().parent;L=D/'publication-v1';M=json.loads((L/'published.json').read_text());required={'Quick checks','Build and compare','Check lost matches','Publish PR result'};head=M['head'];prior=None;deadline=time.monotonic()+21600
while time.monotonic()<deadline:
 out=subprocess.check_output(['gh','pr','view','948','--repo','eth-act/clifv','--json','headRefOid,baseRefOid,state,mergeable,statusCheckRollup'],text=True);r=json.loads(out);assert r['headRefOid']==head,r['headRefOid'];assert r['state']=='OPEN',r['state'];checks={x['name']:x for x in r['statusCheckRollup'] if x.get('name') in required};state={n:(x.get('status'),x.get('conclusion')) for n,x in checks.items()};(L/'CI-current.json').write_text(json.dumps(r,indent=2)+'\n')
 if state!=prior:print(state,flush=True);prior=state
 failed={n:v for n,v in state.items() if v[0]=='COMPLETED' and v[1]!='SUCCESS'}
 if failed:
  (L/'CI-failed.json').write_text(json.dumps(dict(head=head,failed=failed,snapshot=r),indent=2)+'\n');raise SystemExit(1)
 if set(checks)==required and all(x.get('status')=='COMPLETED' and x.get('conclusion')=='SUCCESS' for x in checks.values()):
  receipt=dict(status='passed-all-four-exact-head-checks',head=head,base=r['baseRefOid'],tree=M['tree'],checks=checks,snapshot_sha256=hashlib.sha256(out.encode()).hexdigest(),review_and_current_base_tree_gate='still required before squash delivery');(L/'CI-passed.json').write_text(json.dumps(receipt,indent=2)+'\n');print('all four checks passed',head,flush=True);break
 time.sleep(20)
else:raise SystemExit('CI timeout;no merge attempted')
