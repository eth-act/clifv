from pathlib import Path
import datetime,hashlib,json,os,re,shutil,subprocess,psutil
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';Q=Path(__file__).resolve().parent;R=Q/'validation-package-v1';J=E/'892-joint-current-context-v2/package';L=Q/'layout-v1';L.mkdir();base='45a70ee6e405d0a5e590603c320ec28799595f45';sources={};dag={};todo=['FV/E2E/StockCallStoreLayout.lean'];new={str(p.relative_to(Q)) for p in Q.glob('FV*/**/*.lean')}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
while todo:
 n=todo.pop()
 if n in sources:continue
 data=(Q/n).read_bytes() if n in new else subprocess.check_output(['git','show',base+':'+n],cwd=B)
 if n not in new:assert (J/n).read_bytes()==data,('Broad source changed',n)
 sources[n]=data;dag[n]=[x.replace('.','/')+'.lean' for x in re.findall(r'^import\s+([\w.]+)',data.decode(),re.M) if x.startswith(('FV.','FVTest.'))];todo.extend(dag[n])
active=[]
for p in psutil.process_iter(['pid','name','cmdline','status']):
 try:
  if p.info['name']!='lean' or p.info['status']=='zombie':continue
  for arg in p.info['cmdline'] or []:
   if arg.startswith(str(J)+'/') and arg.endswith('.lean') and str(Path(arg).relative_to(J)) in sources:active.append(dict(pid=p.pid,path=arg))
 except(psutil.NoSuchProcess,psutil.AccessDenied):pass
assert not active,('Active baseline provider; do not duplicate it',active)
for n,data in sources.items():
 p=R/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
 if n in new:continue
 stem=Path(n).with_suffix('')
 for area in ['lib/lean','ir']:
  p=J/'.lake/build'/area/stem
  for src in p.parent.glob(p.name+'.*'):
   if not src.is_file():continue
   dest=R/src.relative_to(J)
   if dest.exists():continue
   dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest)
configs={n:sha(R/n) for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']};keys={}
def key(n):
 if n not in keys:keys[n]=hashlib.sha256(json.dumps([configs,hashlib.sha256(sources[n]).hexdigest(),[(d,key(d)) for d in sorted(dag[n])]],sort_keys=True).encode()).hexdigest()
 return keys[n]
for n in sources:key(n)
context=dict(status='running',base=base,source_hashes={n:hashlib.sha256(data).hexdigest() for n,data in sources.items()},imports=dag,dependency_keys=keys,configs=configs,source_context='Published main45a source plus owned new foundation; inner loop, not publication',no_duplicate_active_provider=True,no_broad_writes=True,budget='2G-j1');(L/'context.json').write_text(json.dumps(context,indent=2)+'\n');(L/'source-before.lean').write_bytes(sources['FV/E2E/StockCallStoreLayout.lean'])
env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(R),FV_MEMCAP='2G',LAKE_CACHE_DIR=str(E/'892-current-main-context-v1/package/.lake/ci-cache'),LAKE_ARTIFACT_CACHE='true',LAKE_RESTORE_ARTIFACTS='true',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1');records=[]
for label,argv in [('providers',['lake','build','--no-build',*[n[:-5].replace('/','.') for n in sources if n not in new]]),('layout',['lake','build','FV.E2E.StockCallStoreLayout'])]:
 env['FV_MEMCAP_UNIT']='worker-o-call-store-'+label;env['FV_MEMCAP_STATS']=str(L/(label+'.mem'))
 with (L/(label+'.log')).open('w') as stream:rc=subprocess.call([str(J/'scripts/memcap.sh'),*argv],cwd=R,env=env,stdout=stream,stderr=subprocess.STDOUT)
 records.append(dict(label=label,argv=argv,exit=rc,stats=(L/(label+'.mem')).read_text() if (L/(label+'.mem')).exists() else None));(L/'progress.json').write_text(json.dumps(dict(status='running' if rc==0 else 'failed',records=records),indent=2)+'\n');print(label,'exit',rc,flush=True)
 if rc:raise SystemExit(rc)
context.update(status='passed',records=records,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(L/'receipt.json').write_text(json.dumps(context,indent=2)+'\n')
