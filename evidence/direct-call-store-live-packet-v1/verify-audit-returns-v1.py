from pathlib import Path
import datetime,hashlib,json,os,re,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';Q=Path(__file__).resolve().parent;R=Q/'validation-package-v1';J=E/'892-joint-current-context-v2/package';L=Q/'audit-returns-v1';L.mkdir();contexts=[json.loads((Q/p).read_text()) for p in ['fault-v3/receipt.json','source-witness-v1/receipt.json','return-machine-v1/receipt.json','compiled-witness-v1/receipt.json']]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for C in contexts:
 assert C['status']=='passed'
 for n,h in C['source_hashes'].items():assert sha(R/n)==h,n
A=Q/'scripts/audit/stock-call-store-returns.lean';env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(R),FV_MEMCAP='2G',FV_MEMCAP_STATS=str(L/'audit.mem'),FV_MEMCAP_UNIT='worker-o-call-store-audit',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LEAN_PATH=str(R/'.lake/build/lib/lean')+':/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/lib/lean')
with (L/'summary.log').open('w') as stream:rc=subprocess.call([str(J/'scripts/memcap.sh'),'python3',str(Q/'axiom-audit-j1.py'),'--cwd',str(R),'--log-dir',str(L/'audit'),str(A)],cwd=R,env=env,stdout=stream,stderr=subprocess.STDOUT)
print('audit exit',rc,flush=True)
if rc:raise SystemExit(rc)
from axiom_records import parse_records
records=parse_records((L/'audit/stock-call-store-returns.log').read_text());axes=dict(records);std={'propext','Classical.choice','Quot.sound'};fixed=sum(any(a not in std for a in xs) for xs in axes.values());assert len(axes)==31 and fixed==3,(len(axes),fixed)
state=dict(status='passed',roots=31,standard_roots=28,fixed_roots=3,axiom_sets=axes,source_audit_sha256=sha(A),context_receipts={p:sha(Q/p) for p in ['fault-v3/receipt.json','source-witness-v1/receipt.json','published-917-origin-bridge-v1.json']},stats=(L/'audit.mem').read_text(),no_class_or_production_completion_claim=True,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(L/'receipt.json').write_text(json.dumps(state,indent=2)+'\n');print(json.dumps(state),flush=True)
