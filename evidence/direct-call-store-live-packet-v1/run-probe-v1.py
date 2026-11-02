from pathlib import Path
import datetime,hashlib,json,os,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';Q=Path(__file__).resolve().parent;J=E/'892-joint-current-context-v2/package';R=Q/'validation-package-v1';C=json.loads((Q/'probe-context-v1/context.json').read_text());L=Q/'probe-v1';L.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in C['source_hashes'].items():assert sha(R/n)==h,n
for n,h in C['effective_configs'].items():assert sha(R/n)==h,n
env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(R),FV_MEMCAP='2G',LAKE_CACHE_DIR=C['native_cache'],LAKE_ARTIFACT_CACHE='true',LAKE_RESTORE_ARTIFACTS='true',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1')
records=[]
for label,argv in [('proper-normal-providers',['lake','build','--no-build','FV.Backend.Lowering.StockArithmetic','FV.Backend.LinearScan','FV.Clif.Parse']),('original-call-store',['lake','env','lean','-j1','-DElab.async=false','--run',str(Q/'InspectCallStoreV1.lean')])]:
 env['FV_MEMCAP_UNIT']='worker-o-call-store-'+label;env['FV_MEMCAP_STATS']=str(L/(label+'.mem'))
 with (L/(label+'.log')).open('w') as stream:rc=subprocess.call([str(J/'scripts/memcap.sh'),*argv],cwd=R,env=env,stdout=stream,stderr=subprocess.STDOUT)
 records.append(dict(label=label,argv=argv,exit=rc,stats=(L/(label+'.mem')).read_text() if (L/(label+'.mem')).exists() else None));(L/'progress.json').write_text(json.dumps(dict(status='running' if rc==0 else 'failed',records=records),indent=2)+'\n');print(label,'exit',rc,flush=True)
 if rc:raise SystemExit(rc)
(Q/'probe-v1/receipt.json').write_text(json.dumps(dict(status='passed',records=records,source_context=C['source_context'],no_provider_compiler_started=True,fixture=json.loads((Q/'fixture-v1.json').read_text()),probe_sha256=sha(Q/'InspectCallStoreV1.lean'),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()),indent=2)+'\n')
