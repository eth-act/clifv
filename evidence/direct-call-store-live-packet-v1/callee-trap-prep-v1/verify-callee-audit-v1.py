from pathlib import Path
import hashlib,json,os,subprocess,sys,datetime
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';T=Path(__file__).resolve().parent;Q=T.parent;R=Q/'validation-package-v1';J=E/'892-joint-current-context-v2/package';L=T/'audit-v1';L.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
paths=['trap-tail-v2/receipt.json','trap-ready-v1/receipt.json']
for n in paths:
 C=json.loads((T/n).read_text());assert C['status']=='passed'
 for name,h in C['source_hashes'].items():assert sha(R/name)==h,name
A=T/'scripts/audit/stock-call-store-callee.lean';env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(R),FV_MEMCAP='2G',FV_MEMCAP_STATS=str(L/'audit.mem'),FV_MEMCAP_UNIT='worker-o-call-store-callee-audit',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LEAN_PATH=str(R/'.lake/build/lib/lean')+':/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/lib/lean')
with (L/'summary.log').open('w') as stream:rc=subprocess.call([str(J/'scripts/memcap.sh'),'python3',str(Q/'axiom-audit-j1.py'),'--cwd',str(R),'--log-dir',str(L/'audit'),str(A)],cwd=R,env=env,stdout=stream,stderr=subprocess.STDOUT)
print('audit exit',rc,flush=True)
if rc:raise SystemExit(rc)
sys.path.insert(0,str(Q));from axiom_records import parse_records
axes=dict(parse_records((L/'audit/stock-call-store-callee.log').read_text()));assert len(axes)==2 and all(set(xs)<={'propext','Classical.choice','Quot.sound'} for xs in axes.values()),axes
state=dict(status='passed',axiom_sets=axes,roots=2,standard_roots=2,receipts={n:sha(T/n) for n in paths},audit_sha256=sha(A),stats=(L/'audit.mem').read_text(),no_machine_or_linked_completion_claim=True,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(L/'receipt.json').write_text(json.dumps(state,indent=2)+'\n')
