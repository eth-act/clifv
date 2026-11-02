from pathlib import Path
import datetime,hashlib,json,os,re,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';Q=E/'direct-call-arithmetic-live-packet-v1';P=E/'direct-call-production-class-packet-v1';R=Q/'validation-package-v1';C=json.loads((Q/'live-production-consumer-kernel-v2/receipt.json').read_text());L=Q/'live-exec-facades-v1';L.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
oldkeys=dict(C['dependency_keys']);new=['FV/E2E/StockLiveCallProvider.lean','FV/E2E/ResultCallExec.lean','FV/E2E/LiveCallExec.lean']
for n in new:
 p=Q/n if (Q/n).exists() else P/n;data=p.read_bytes();(R/n).write_bytes(data);snap=L/'sources'/n;snap.parent.mkdir(parents=True,exist_ok=True);snap.write_bytes(data);deps=[x.replace('.','/')+'.lean' for x in re.findall(r'^import\s+([\w.]+)',data.decode(),re.M) if x.startswith(('FV.','FVTest.'))];assert all(d in C['source_hashes'] for d in deps)
 C['source_hashes'][n]=sha(p);C['imports'][n]=deps;C['dependency_keys'][n]=hashlib.sha256(json.dumps([C['effective_configs'],sha(p),[(d,C['dependency_keys'][d]) for d in sorted(deps)]],sort_keys=True).encode()).hexdigest()
for n,k in oldkeys.items():assert C['dependency_keys'][n]==k,n
for n,h in C['source_hashes'].items():assert sha(R/n)==h,n
env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(R),FV_MEMCAP='2G',LAKE_CACHE_DIR=C['native_cache'],LAKE_ARTIFACT_CACHE='true',LAKE_RESTORE_ARTIFACTS='true',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1')
records=[]
for i,n in enumerate(new):
 label='facade-'+str(i);env['FV_MEMCAP_STATS']=str(L/(label+'.mem'));env['FV_MEMCAP_UNIT']='worker-o-live-'+label
 with (L/(label+'.log')).open('w') as stream:rc=subprocess.call([str(B/'.worktrees/stock-extending-production-20261031/scripts/memcap.sh'),'lake','build',n[:-5].replace('/','.')],cwd=R,env=env,stdout=stream,stderr=subprocess.STDOUT)
 records.append(dict(module=n,exit=rc,stats=(L/(label+'.mem')).read_text()));print(n,'exit',rc,flush=True)
 if rc:raise SystemExit(rc)
C.update(status='passed',facade_records=records,strict_extension_of='live-production-consumer-kernel-v2/receipt.json',all_previous_keys_exact=True);(L/'receipt.json').write_text(json.dumps(C,indent=2)+'\n')
# Runtime cases ran before this audit-only extension. No executed source or dependency key changed.
M=json.loads((Q/'actual-live-call-matrix-v2/executed-context.json').read_text());assert all(C['dependency_keys'].get(n)==k for n,k in M['dependency_keys'].items() if n in oldkeys)
(Q/'live-runtime-audit-extension-v1.json').write_text(json.dumps(dict(status='passed',previous_matrix='actual-live-call-matrix-v2/result.json',old_source_keys_exact=len(oldkeys),added_audit_only_roots=new,no_old_import_edge_to_added_root=all(not set(new)&set(ds) for n,ds in M['imports'].items()),runtime_support_keys_retained={n:k for n,k in M['dependency_keys'].items() if n not in oldkeys}),indent=2)+'\n')
