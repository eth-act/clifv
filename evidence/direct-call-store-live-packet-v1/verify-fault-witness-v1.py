from pathlib import Path
import datetime,hashlib,json,os,re,shutil,subprocess,psutil
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';Q=Path(__file__).resolve().parent;R=Q/'validation-package-v1';J=E/'892-joint-current-context-v2/package';L=Q/'fault-witness-v1';L.mkdir();base='45a70ee6e405d0a5e590603c320ec28799595f45';F=E/'140-fence-integration-prep-v1';fm=json.loads((F/'mixed-machine-state-v6.json').read_text());frozen=Path(fm['canonical_source']);foundation='de229a7e07f5ca737d9b27287f1cc64f5ae6a64e';foundation_files=set(subprocess.check_output(['git','diff-tree','--no-commit-id','--name-only','-r',foundation],cwd=B,text=True).splitlines());assert len(foundation_files)==22;owned={str(p.relative_to(Q)) for p in Q.glob('FV*/**/*.lean')};sources={};dag={};origins={};todo=['FV/E2E/StockCallStoreFaultWitness.lean']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
while todo:
 n=todo.pop()
 if n in sources:continue
 if n in owned:data=(Q/n).read_bytes();origin='owned new call/store source'
 elif n.startswith('FV/Backend/Proof/') and Path(n).name in fm['source_hashes']:
  data=(frozen/Path(n).name).read_bytes();assert hashlib.sha256(data).hexdigest()==fm['source_hashes'][Path(n).name],n;origin='immutable ordinary-access interface v6'
 elif n in foundation_files:data=subprocess.check_output(['git','show',foundation+':'+n],cwd=B);origin='verified merged916 foundation de229a7e'
 else:data=subprocess.check_output(['git','show',base+':'+n],cwd=B);assert (J/n).read_bytes()==data,n;origin='published main45a baseline'
 sources[n]=data;origins[n]=origin;dag[n]=[x.replace('.','/')+'.lean' for x in re.findall(r'^import\s+([\w.]+)',data.decode(),re.M) if x.startswith(('FV.','FVTest.'))];todo.extend(dag[n])
active=[]
for p in psutil.process_iter(['pid','name','cmdline','status']):
 try:
  if p.info['name']!='lean' or p.info['status']=='zombie':continue
  for arg in p.info['cmdline'] or []:
   if not arg.endswith('.lean') or not Path(arg).exists():continue
   candidates=[n for n in sources if n.endswith('/'+Path(arg).name)]
   for n in candidates:
    if sha(Path(arg))==hashlib.sha256(sources[n]).hexdigest():active.append(dict(pid=p.pid,path=arg,module=n))
 except(psutil.NoSuchProcess,psutil.AccessDenied):pass
assert not active,('Identical active provider; do not duplicate',active)
candidates={n for n in sources if origins[n]!='published main45a baseline'}
for n,data in sources.items():
 d=R/n;d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(data)
 if n in candidates:
  d=L/'source-snapshot'/n;d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(data);continue
 stem=Path(n).with_suffix('')
 for area in ['lib/lean','ir']:
  p=J/'.lake/build'/area/stem
  for src in p.parent.glob(p.name+'.*'):
   if not src.is_file():continue
   d=R/src.relative_to(J)
   if d.exists():continue
   d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,d)
configs={n:sha(R/n) for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']};keys={}
def key(n):
 if n not in keys:keys[n]=hashlib.sha256(json.dumps([configs,hashlib.sha256(sources[n]).hexdigest(),[(d,key(d)) for d in sorted(dag[n])]],sort_keys=True).encode()).hexdigest()
 return keys[n]
for n in sources:key(n)
context=dict(status='running',base=base,source_hashes={n:hashlib.sha256(d).hexdigest() for n,d in sources.items()},imports=dag,dependency_keys=keys,origins=origins,effective_configs=configs,source_context='Published main45a plus verified merged916 foundation, frozen unpublished917 ordinary access v6 and owned call/store sources; inner loop only',budget='2G-j1',no_shared_writes=True,no_duplicate_active_provider=True);(L/'context.json').write_text(json.dumps(context,indent=2)+'\n')
env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(R),FV_MEMCAP='2G',LAKE_CACHE_DIR=str(E/'892-current-main-context-v1/package/.lake/ci-cache'),LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='true',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1');records=[]
def run(label,argv):
 env['FV_MEMCAP_STATS']=str(L/(label+'.mem'));env['FV_MEMCAP_UNIT']='worker-o-call-store-'+label
 with (L/(label+'.log')).open('w') as stream:rc=subprocess.call([str(J/'scripts/memcap.sh'),*argv],cwd=R,env=env,stdout=stream,stderr=subprocess.STDOUT)
 records.append(dict(label=label,argv=argv,exit=rc,stats=(L/(label+'.mem')).read_text() if (L/(label+'.mem')).exists() else None));(L/'progress.json').write_text(json.dumps(dict(status='running' if rc==0 else 'failed',records=records),indent=2)+'\n');print(label,'exit',rc,flush=True)
 if rc:raise SystemExit(rc)
run('providers',['lake','build','--no-build',*[n[:-5].replace('/','.') for n in sources if n not in candidates]])
ordered=[];pending=set(candidates)
while pending:
 ready=sorted(n for n in pending if not set(dag[n])&pending);assert ready;ordered+=ready;pending.difference_update(ready)
for i,n in enumerate(ordered):run('kernel-'+str(i),['lake','build',n[:-5].replace('/','.')])
context.update(status='passed',records=records,ordered=ordered,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(L/'receipt.json').write_text(json.dumps(context,indent=2)+'\n')
