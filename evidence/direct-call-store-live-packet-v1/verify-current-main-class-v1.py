from pathlib import Path
import datetime,hashlib,json,os,subprocess,psutil
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';Q=Path(__file__).resolve().parent;R=Q/'validation-package-v1';J=E/'892-joint-current-context-v2/package';L=Q/'current-main-class-v1';L.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
C=json.loads((Q/'current-main-class-source-bridge-v2.json').read_text());head=C['main']
assert subprocess.check_output(['gh','api','repos/eth-act/clifv/commits/main','--jq','.sha'],cwd=B,text=True).strip()==head,'Current main drifted'
for n,d in C['sources'].items():assert sha(R/n)==d['sha256'],n
for n,d in C['configs'].items():assert sha(R/n)==d['used_sha256'],n
for n,h in {'original-caller.clif':'dd3a48bed0088809a32af0e148db48046ca403b990b702ec753f0083e54cca83','original-callee.clif':'97277383ff351de032d121fdcde17db75d67ccf2faccddb9ff8a88ea67bbb33a'}.items():assert sha(Q/n)==h,n
active=[]
for p in psutil.process_iter(['pid','name','cmdline','status']):
 try:
  if p.info['name']=='lean' and p.info['status']!='zombie' and any(str(R) in x for x in p.info['cmdline'] or []):active.append(p.pid)
 except psutil.Error:pass
assert not active,active
env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(R),FV_MEMCAP='2G',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false');records=[]
def run(label,argv):
 env['FV_MEMCAP_STATS']=str(L/(label+'.mem'));env['FV_MEMCAP_UNIT']='worker-o-call-store-current-'+label
 with (L/(label+'.log')).open('w') as stream:rc=subprocess.call([str(J/'scripts/memcap.sh'),*argv],cwd=R,env=env,stdout=stream,stderr=subprocess.STDOUT)
 records.append(dict(label=label,argv=argv,exit=rc,stats=(L/(label+'.mem')).read_text() if (L/(label+'.mem')).exists() else None));(L/'progress.json').write_text(json.dumps(dict(status='running' if rc==0 else 'failed',records=records),indent=2)+'\n');print(label,'exit',rc,flush=True)
 if rc:raise SystemExit(rc)
run('all-normal-keys',['lake','build','--no-build',*[n[:-5].replace('/','.') for n in C['owned_new_sources']]])
A=Q/'scripts/audit/stock-call-store-class-final.lean';env['LEAN_PATH']=str(R/'.lake/build/lib/lean')+':/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/lib/lean'
run('axiom-audit',['python3',str(Q/'axiom-audit-j1.py'),'--cwd',str(R),'--log-dir',str(L/'audit'),str(A)])
from axiom_records import parse_records
axes=dict(parse_records((L/'audit/stock-call-store-class-final.log').read_text()));old=json.loads((Q/'audit-class-v2/receipt.json').read_text())['axiom_sets'];assert axes==old,'The46AXsets changed'
receipt=dict(status='passed-current-main-source-projection-and-normal-keys',main=head,tree=C['main_tree'],sources=sha(Q/'current-main-class-source-bridge-v2.json'),owned_modules=len(C['owned_new_sources']),all_sources=len(C['sources']),records=records,audit_roots=46,standard_roots=39,fixed_roots=7,axiom_sets=axes,no_provider_rebuilt=True,no_shared_prefix_or_cache_writes=True,publication_ci_tree_gates_remain=True,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(L/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print('current-main class passed',flush=True)
