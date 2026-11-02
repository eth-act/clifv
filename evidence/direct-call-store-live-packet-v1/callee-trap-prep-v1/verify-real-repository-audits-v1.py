from pathlib import Path
import datetime,hashlib,json,os,subprocess,sys
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';T=Path(__file__).resolve().parent;Q=T.parent;R=Q/'validation-package-v1';J=E/'892-joint-current-context-v2/package';L=T/'real-repository-audits-v1';L.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
A=J/'scripts/axiom-audit.py';published=subprocess.check_output(['git','show','37fc00cb91cf37557777f0664878a164c59587cf:scripts/axiom-audit.py'],cwd=B);assert A.read_bytes()==published
contexts=[Q/'current-main-class-source-bridge-v2.json',T/'first-trap-witness-v1/receipt.json',T/'trap-source-witness-v3/receipt.json']
for p in contexts:
 C=json.loads(p.read_text());items=C.get('source_hashes') or {n:d['sha256'] for n,d in C['sources'].items()}
 for n,h in items.items():assert sha(R/n)==h,n
old=Q/'standalone-class-canonical-v1/scripts/audit/stock-call-store-class-final.lean';new=T/'scripts/audit/stock-call-store-callee-final.lean'
env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LAKE_CACHE_DIR']:env.pop(k,None)
env.update(PATH=str(T/'tool-bin')+':/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],WORKER_O_AUDIT_COMMAND_LOG=str(L/'actual-lean-commands.jsonl'),FV_ROOT=str(R),FV_MEMCAP='2G',FV_MEMCAP_STATS=str(L/'audit.mem'),FV_MEMCAP_UNIT='worker-o-real-repository-audits',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false')
argv=['python3',str(A),'--cwd',str(R),'--log-dir',str(L/'audit'),str(old),str(new)]
with (L/'summary.log').open('w') as stream:rc=subprocess.call([str(J/'scripts/memcap.sh'),*argv],cwd=R,env=env,stdout=stream,stderr=subprocess.STDOUT)
state=dict(status='passed' if rc==0 else 'failed',real_exit=rc,actual_unchanged_repository_auditor=str(A),auditor_sha256=sha(A),argv=argv,resource_wrapper_sha256=sha(T/'tool-bin/lake'),wrapper_only_adds_j1=True,actual_lean_commands=[json.loads(x) for x in (L/'actual-lean-commands.jsonl').read_text().splitlines()],audits={str(p):sha(p) for p in [old,new]},stats=(L/'audit.mem').read_text() if (L/'audit.mem').exists() else None,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(L/'receipt.json').write_text(json.dumps(state,indent=2)+'\n');print('real repository auditor exit',rc,flush=True);print((L/'summary.log').read_text(),flush=True)
if rc:raise SystemExit(rc)
# This remains an independent exact-set comparison. It does not substitute for the repository gate.
sys.path.insert(0,str(Q));from axiom_records import parse_records
for label,path,expected in [('old',old,Q/'audit-class-v2/receipt.json'),('new',new,T/'audit-v2/receipt.json')]:
 actual=dict(parse_records((L/'audit'/(path.stem+'.log')).read_text()));assert actual==json.loads(expected.read_text())['axiom_sets'],label
(L/'exact-set-comparison.json').write_text(json.dumps(dict(status='passed-independent-exact-sets',old_roots=46,new_roots=56,repository_auditor_exit=rc),indent=2)+'\n')
