from pathlib import Path
import datetime,fcntl,hashlib,json,os,subprocess,sys,time
from preflight import OUT,PLAN,check
N=OUT;E=N.parent;P=Path(PLAN['existing_snapshot']);R=E/'broad-two-job-scheduling-proposal-v1';release=N/'release.json';statefile=N/'execution-state.json';assert not statefile.exists()
state={'status':'starting','revision':PLAN['target_revision'],'tree':PLAN['combined_tree'],'records':[],'full_goal_complete':False}
def save():state['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();statefile.write_text(json.dumps(state,indent=2)+'\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
check(P,release)
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()))
for k in ['FV_MEMCAP_OFF','FV_LAKE_CACHE','LEAN_SYSROOT','LEAN_SRC_PATH','BLESS']:env.pop(k,None)
env.update(WORKER_O_FULL_GATE_GRANTED='513-production-shared',FV_ROOT=str(P),FV_MEMCAP='12G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',CARGO_BUILD_JOBS='2',LAKE_CACHE_DIR=PLAN['existing_cache'],LAKE_ARTIFACT_CACHE='true',LAKE_RESTORE_ARTIFACTS='true',PYTHONDONTWRITEBYTECODE='1');env['PATH']='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+str(P/'rust/target/release')+':'+env['PATH'];env['LEAN_PATH']=str(P/'.lake/build/lib/lean')+':/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/lib/lean'
consumers=['FV.E2E.DeadCleanupExecTrap','FV.E2E.DeadCleanupExecTrapT','FV.E2E.LinkArmCallDecode','FV.E2E.LinkArmIniOf','FV.E2E.LinkTrapCallT','FV.E2E.LinkTrapCallWitness']
for label,targets in [('consumer-baseline',consumers),('normal',['FV','FVTest','Corpus'])]:
 lock=(N/'exclusive-shared-gate.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);check(P,release);logs=N/'runs/combined'/label/'current-v6';logs.mkdir(parents=True);state['status']='running_'+label;save()
 argv=[sys.executable,str(R/'lake-serial-build-drain.py'),'--root',str(P),'--budget','12G','--min-cap','4G','--default-cap','12G','--max-cap','12G','--heavy','16G','--max-jobs','2','--margin','2','--profile',str(N/'conservative-peaks.tsv'),'--no-dedup','--out',str(logs/'scheduler'),*targets]
 with (logs/'normal.log').open('w')as stream:
  child=subprocess.Popen(argv,cwd=P,env=env,stdout=stream,stderr=subprocess.STDOUT);state['active_scheduler']=child.pid;save();rc=child.wait()
 record={'phase':label,'exit':rc,'log_sha256':sha(logs/'normal.log')};state['records'].append(record);state.pop('active_scheduler',None);save();lock.close()
 if rc:state['status']='failed_'+label;save();raise SystemExit(rc)
 check(P,release);(logs/'receipt.json').write_text(json.dumps({'status':'passed','phase':label,'revision':PLAN['target_revision'],'tree':PLAN['combined_tree'],'full_goal_complete':False},indent=2)+'\n');print('PASSED',label,flush=True)
phases=['audits','tools','crates','e2e','comparison','runtime-encoder','examples','crate-parity','retained-matrices','nonmemory-matrices','configured-tests','binding-providers','preservation']
for phase in phases:
 state['status']='running_'+phase;save();rc=subprocess.call([sys.executable,str(N/'run-phase.py'),'--root',str(P),'--release',str(release),'--stage','combined','--phase',phase,'--attempt','current-v6'],env=env)
 state['records'].append({'phase':phase,'exit':rc});save()
 if rc:state['status']='failed_'+phase;save();raise SystemExit(rc)
base=N/'runs/combined';attempt='current-v6'
checks=[('required-axioms',[str(N/'verify-required-axioms.py'),'--current',str(base/'audits'/attempt/'exact-axiom-sets.json'),'--out',str(N/'required-axioms-current-v6.json')]),('identities',[str(N/'verify-identities.py'),'--production',str(base/'comparison'/attempt/'lean-backend/results.json'),'--raw-stock',str(base/'comparison'/attempt/'raw-stock/results.json'),'--cleanup-e2e',str(base/'e2e'/attempt/'cleanup-identities.json'),'--legacy-e2e',str(base/'e2e'/attempt/'legacy-identities.json'),'--out',str(N/'identities-current-v6.json')])]
for label,args in checks:
 state['status']='checking_'+label;save();rc=subprocess.call([sys.executable,*args],env=env);state['records'].append({'check':label,'exit':rc});save()
 if rc:state['status']='failed_'+label;save();raise SystemExit(rc)
state['status']='all_queued_executions_passed_goal_still_incomplete';save();print(json.dumps(state),flush=True)
