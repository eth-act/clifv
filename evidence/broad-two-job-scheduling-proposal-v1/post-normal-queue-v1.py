from pathlib import Path
import datetime,fcntl,hashlib,json,os,select,subprocess,sys
R=Path(__file__).resolve().parent; E=R.parent; Q=E/'513-shared-gate-queue-v5'; P=E/'892-joint-current-context-v2/package'
lock=(R/'post-normal-owner.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
state=R/'post-normal-state-v1.json';assert not state.exists()
record={'status':'waiting_for_existing_normal_owner','normal_owner':1683759,'normal_scheduler':1713178,'records':[],'full_goal_complete':False}
def save():state.write_text(json.dumps(record,indent=2)+'\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
save()
try:
 fd=os.pidfd_open(1683759)
 try:select.select([fd],[],[])
 finally:os.close(fd)
except ProcessLookupError:pass
normal=json.loads((R/'handoff-state-v1.json').read_text());assert normal['status']=='replacement_normal_passed' and normal['exit']==0, 'Inspect actual normal failure before continuation'
normal_receipt=Q/'runs/combined/normal/v5-twojob-v1/receipt.json';assert json.loads(normal_receipt.read_text())['status']=='passed'
record['normal_receipt_sha256']=sha(normal_receipt)
env=dict(os.environ,WORKER_O_FULL_GATE_GRANTED='513-production-shared',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2')
phases=['audits','tools','crates','e2e','comparison','runtime-encoder','examples','crate-parity','retained-matrices','nonmemory-matrices','configured-tests','binding-providers','preservation']
for phase in phases:
 record['status']='running_'+phase;save()
 argv=[sys.executable,str(Q/'run-phase.py'),'--root',str(P),'--release',str(Q/'release.json'),'--stage','combined','--phase',phase,'--attempt','v5-postnormal-v1']
 rc=subprocess.run(argv,env=env).returncode
 record['records'].append({'phase':phase,'exit':rc})
 if rc:
  record['status']='failed_'+phase;save();raise SystemExit(rc)
 receipt=Q/'runs/combined'/phase/'v5-postnormal-v1/receipt.json';record['records'][-1]['receipt_sha256']=sha(receipt);save()
# Preserve identities and exact axiom sets after actual phase execution.
base=Q/'runs/combined'; attempt='v5-postnormal-v1'
checks=[('required-axioms',[str(Q/'verify-required-axioms.py'),'--current',str(base/'audits'/attempt/'exact-axiom-sets.json'),'--out',str(R/'post-normal-required-axioms-v1.json')]),('identities',[str(Q/'verify-identities.py'),'--production',str(base/'comparison'/attempt/'lean-backend/results.json'),'--raw-stock',str(base/'comparison'/attempt/'raw-stock/results.json'),'--cleanup-e2e',str(base/'e2e'/attempt/'cleanup-identities.json'),'--legacy-e2e',str(base/'e2e'/attempt/'legacy-identities.json'),'--out',str(R/'post-normal-identities-v1.json')])]
for label,args in checks:
 record['status']='checking_'+label;save();rc=subprocess.run([sys.executable,*args],env=env).returncode
 record['records'].append({'check':label,'exit':rc});save()
 if rc:record['status']='failed_'+label;save();raise SystemExit(rc)
record['status']='all_queued_executions_passed_goal_still_incomplete';record['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save();print(json.dumps(record),flush=True)
