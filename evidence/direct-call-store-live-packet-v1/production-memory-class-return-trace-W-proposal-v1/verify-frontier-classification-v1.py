from pathlib import Path
import json,hashlib,subprocess,os,psutil,re,shutil,importlib.util
D=Path(__file__).resolve().parent;Q=D.parent;E=Q.parent;R=Q/'validation-package-v1';P=E/'892-joint-current-context-v2/package';L=D/'complete-frontier-classification-v1';L.mkdir();I=json.loads((D/'current8f-kernel-manifest.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(D/'current8f-kernel-manifest.json')=='3c92e1b8f0b2dc1b036964eaaf99c4c6b206b7154479ead774b87d573c20f435';main='8f073980e9630c8d3cd9d6f6f77ab462474c7bcb';ordered=['FV.E2E.StockMemoryStoreCfgMachineW', 'FV.E2E.StockMemoryCapturedCopyNIW', 'FV.E2E.StockMemoryCfgMachineW', 'FV.E2E.StockMemoryCfgNIW', 'FV.E2E.StockMemoryCfgWorldXW', 'FV.E2E.StockMemoryExtLoadNIW', 'FV.E2E.StockMemoryIntegerNIW', 'FV.E2E.StockMemoryStoreMachineW', 'FV.E2E.StockMemoryLoadStoreNIW', 'FV.E2E.StockMemorySretCopyNIW', 'FV.E2E.StockMemoryStoreCfgNIW', 'FV.E2E.StockMemoryStoreNIW'];baseline=sorted(set(I['import_graph'])-set(ordered));assert len(baseline)==1357;staged={'FV/E2E/WorldReturnTraceCore.lean','FV/E2E/StockMemoryMachineReturnValueW.lean','FV/E2E/StockMemoryMachineW.lean','FV/E2E/StockMemoryWorldXW.lean'};origin={}
for rel,h in I['source_hashes'].items():
 n=rel[:-5].replace('/','.');p=D/'source'/rel if n in ordered else R/rel;assert sha(p)==h,rel
 if n in ordered:origin[rel]={'kind':'new owned export','sha256':h};continue
 if rel in staged:origin[rel]={'kind':'explicit approved staged W helper','sha256':h};continue
 data=subprocess.check_output(['git','show',main+':'+rel]);assert hashlib.sha256(data).hexdigest()==h,('Current main source differs',rel);origin[rel]={'kind':'exact current8f Git blob','sha256':h}
(L/'current-source-context.json').write_text(json.dumps({'main':main,'sources':origin,'graph':I['import_graph'],'source_closure':len(origin),'old_files_changed':[]},indent=2)+'\n')
for p in psutil.process_iter(['uids','name','status','cmdline']):
 try:
  if p.info['uids'].real!=os.getuid() or p.info['name'] not in ['lean','lake'] or p.info['status']=='zombie':continue
  assert not p.cwd().startswith(str(R)) and not any(str(R) in a for a in (p.info['cmdline'] or [])),('R writer',p.pid)
 except(psutil.NoSuchProcess,psutil.AccessDenied):pass
cfg={c:sha(R/c) for c in ['lakefile.toml','lean-toolchain','lake-manifest.json']};env=dict(os.environ)
for k in ['FV_MEMCAP_OFF','FV_LAKE_CACHE','LEAN_PATH','LEAN_SYSROOT','LEAN_SRC_PATH','LAKE_CACHE_DIR']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(R),FV_MEMCAP='2G',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1');records=[];outputs={}
def run(label,args,allowed=(0,)):
 e=dict(env,FV_MEMCAP_STATS=str(L/(label+'.mem')),FV_MEMCAP_UNIT='worker-o-memory-classes-W-'+label)
 with (L/(label+'.log')).open('w') as f:rc=subprocess.call([str(P/'scripts/memcap.sh'),*args],cwd=R,env=e,stdout=f,stderr=subprocess.STDOUT)
 records.append({'label':label,'argv':args,'exit':rc,'log_sha256':sha(L/(label+'.log')),'memory':(L/(label+'.mem')).read_text()});(L/'progress.json').write_text(json.dumps(records,indent=2)+'\n');print(label,rc,flush=True);assert rc in allowed,(label,rc);return rc

G=Path('/home/lee/clifv/.worktrees/loop-20261102'); roots=re.findall(r'✖ .* Building ([\w.]+)',(D/'current8f-proper-dependencies-v1/baseline1357.log').read_text());assert len(roots)==6
closure=lambda n:None
def cone(n):
 out=set();todo=[n]
 while todo:
  a=todo.pop()
  if a in out:continue
  out.add(a);todo.extend(I['import_graph'][a])
 return out
ancestry={n:sorted((cone(n)-{n})&set(roots)) for n in roots};affected=set(roots)
while True:
 new=affected|{n for n,ds in I['import_graph'].items() if any(x in affected for x in ds)}
 if new==affected:break
 affected=new
live=[]
for proc in psutil.process_iter(['uids','name','status','cmdline']):
 try:
  if proc.info['uids'].real!=os.getuid() or proc.info['name'] not in ['lean','lake'] or proc.info['status']=='zombie':continue
  args=proc.info['cmdline'] or []
  for n in roots:
   if any(n.replace('.','/')+'.lean' in a or n.replace('.','/')+'.c' in a for a in args):live.append({'pid':proc.pid,'module':n,'cwd':proc.cwd(),'argv':args})
 except(psutil.NoSuchProcess,psutil.AccessDenied):pass
report={}
def query(label,root,args):
 e=dict(env,FV_ROOT=str(root),FV_MEMCAP_STATS=str(L/(label+'.mem')),FV_MEMCAP_UNIT='worker-o-memory-frontier-'+label)
 with (L/(label+'.log')).open('w') as f:rc=subprocess.call([str(P/'scripts/memcap.sh'),*args],cwd=root,env=e,stdout=f,stderr=subprocess.STDOUT)
 records.append({'label':label,'cwd':str(root),'argv':args,'exit':rc,'log_sha256':sha(L/(label+'.log')),'memory':(L/(label+'.mem')).read_text()});(L/'progress.json').write_text(json.dumps(records,indent=2)+'\n');print(label,rc,flush=True);assert rc in (0,3);return rc
for i,n in enumerate(roots):
 keyrc=query('R-key'+str(i),R,['lake','query','--no-build','+'+n+':depHash']);keys=re.findall(r'^[0-9a-f]{16}$',(L/('R-key'+str(i)+'.log')).read_text(),re.M);expected=keys[0] if keyrc==0 and len(keys)==1 else None
 report[n]={'expected_key':expected,'failed_transitive_predecessors':ancestry[n],'closure_modules':len(cone(n)),'donors':{}}
 for label,donor in [('P',P),('G',G)]:
  src_bad=[]
  for mod in cone(n):
   rel=mod.replace('.','/')+'.lean';f=donor/rel
   if not f.exists() or sha(f)!=I['source_hashes'][rel]:src_bad.append(mod)
  rc=query(label+'-normal'+str(i),donor,['lake','build','--no-build',n]);tr=donor/'.lake/build/lib/lean'/Path(n.replace('.','/')+'.trace');md=json.loads(tr.read_text()) if tr.exists() else {};arts={}
  for area in ['lib/lean','ir']:
   stem=donor/'.lake/build'/area/n.replace('.','/')
   for f in stem.parent.glob(stem.name+'.*'):
    if f.is_file():arts[str(f.relative_to(donor))]=sha(f)
  report[n]['donors'][label]={'normal_exit':rc,'source_mismatch':src_bad,'native_key':md.get('depHash'),'trace_sha256':sha(tr) if tr.exists() else None,'inputs':bool(md.get('inputs')),'synthetic':md.get('synthetic'),'matches_current_key':expected is not None and expected==md.get('depHash'),'artifacts':arts}
(L/'receipt.json').write_text(json.dumps({'status':'CLASSIFICATION_ONLY;NO_COMPILER_OR_COPY','roots':report,'affected_cone':sorted(affected),'active_exact_writers':live,'records':records},indent=2)+'\n')
