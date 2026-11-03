from pathlib import Path
import json,hashlib,subprocess,os,psutil,re,shutil,importlib.util
D=Path(__file__).resolve().parent;Q=D.parent;E=Q.parent;R=Q/'validation-package-v1';P=E/'892-joint-current-context-v2/package';L=D/'two-proper-donor-reuse-v1';L.mkdir();I=json.loads((D/'current8f-kernel-manifest.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(D/'current8f-kernel-manifest.json')=='3c92e1b8f0b2dc1b036964eaaf99c4c6b206b7154479ead774b87d573c20f435';main='8f073980e9630c8d3cd9d6f6f77ab462474c7bcb';ordered=['FV.E2E.StockMemoryStoreCfgMachineW', 'FV.E2E.StockMemoryCapturedCopyNIW', 'FV.E2E.StockMemoryCfgMachineW', 'FV.E2E.StockMemoryCfgNIW', 'FV.E2E.StockMemoryCfgWorldXW', 'FV.E2E.StockMemoryExtLoadNIW', 'FV.E2E.StockMemoryIntegerNIW', 'FV.E2E.StockMemoryStoreMachineW', 'FV.E2E.StockMemoryLoadStoreNIW', 'FV.E2E.StockMemorySretCopyNIW', 'FV.E2E.StockMemoryStoreCfgNIW', 'FV.E2E.StockMemoryStoreNIW'];baseline=sorted(set(I['import_graph'])-set(ordered));assert len(baseline)==1357;staged={'FV/E2E/WorldReturnTraceCore.lean','FV/E2E/StockMemoryMachineReturnValueW.lean','FV/E2E/StockMemoryMachineW.lean','FV/E2E/StockMemoryWorldXW.lean'};origin={}
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

import tomllib
front=json.loads((D/'complete-frontier-classification-v1/receipt.json').read_text());roots=[n for n,v in front['roots'].items() if v['donors']['P']['normal_exit']==0 and v['donors']['P']['matches_current_key']];assert len(roots)==2
closure=set();todo=list(roots)
while todo:
 n=todo.pop()
 if n in closure:continue
 closure.add(n);todo+=I['import_graph'][n]
for n in closure:
 rel=n.replace('.','/')+'.lean';assert sha(P/rel)==sha(R/rel)==I['source_hashes'][rel],n
def strip(v):
 if isinstance(v,dict):return {k:strip(a) for k,a in v.items() if k!='weakLeanArgs'}
 if isinstance(v,list):return [strip(a) for a in v]
 return v
assert strip(tomllib.loads((P/'lakefile.toml').read_text()))==strip(tomllib.loads((R/'lakefile.toml').read_text()))
for c in ['lean-toolchain','lake-manifest.json']:assert sha(P/c)==sha(R/c)
for proc in psutil.process_iter(['uids','name','status','cmdline']):
 try:
  if proc.info['uids'].real!=os.getuid() or proc.info['name'] not in ['lean','lake'] or proc.info['status']=='zombie':continue
  for n in roots:assert not any(n.replace('.','/')+'.lean' in a or n.replace('.','/')+'.c' in a for a in (proc.info['cmdline'] or [])),('Exact writer',proc.pid,n)
 except(psutil.NoSuchProcess,psutil.AccessDenied):pass
# Require complete current proper donor normality without writing P.
def donor_check():
 label='P-complete-donor-closure';args=['lake','build','--no-build',*sorted(closure)];e=dict(env,FV_ROOT=str(P),FV_MEMCAP_STATS=str(L/(label+'.mem')),FV_MEMCAP_UNIT='worker-o-memory-two-donors')
 with (L/(label+'.log')).open('w') as f:rc=subprocess.call([str(P/'scripts/memcap.sh'),*args],cwd=P,env=e,stdout=f,stderr=subprocess.STDOUT)
 records.append({'label':label,'cwd':str(P),'argv':args,'exit':rc,'log_sha256':sha(L/(label+'.log')),'memory':(L/(label+'.mem')).read_text()});print(label,rc,flush=True);assert rc==0
 donor_inputs={}
 for n in sorted(closure-set(roots)):
  rel=Path(n.replace('.','/'));pt=P/'.lake/build/lib/lean'/rel.with_suffix('.trace');rt=R/'.lake/build/lib/lean'/rel.with_suffix('.trace');pm=json.loads(pt.read_text());rm=json.loads(rt.read_text());assert pm['depHash']==rm['depHash'],('dependency key differs',n)
  arts={}
  for area in ['lib/lean','ir']:
   stem=P/'.lake/build'/area/rel
   for f in stem.parent.glob(stem.name+'.*'):
    if not f.is_file() or f.name.endswith(('.trace','.c.o','.o','.bc')):continue
    dest=R/f.relative_to(P);assert dest.exists() and sha(dest)==sha(f),('dependency output differs',n,str(f));arts[str(f.relative_to(P))]=sha(f)
  donor_inputs[n]={'native_key':pm['depHash'],'artifacts':arts}
 (L/'coherent-full-dependencies.json').write_text(json.dumps(donor_inputs,indent=2)+'\n')
donor_check();copied={}
for i,n in enumerate(roots):
 run('R-deps'+str(i),['lake','build','--no-build',*I['import_graph'][n]]);run('R-key'+str(i),['lake','query','--no-build','+'+n+':depHash']);keys=re.findall(r'^[0-9a-f]{16}$',(L/('R-key'+str(i)+'.log')).read_text(),re.M);assert keys==[front['roots'][n]['expected_key']]
 tr=P/'.lake/build/lib/lean'/Path(n.replace('.','/')+'.trace');md=json.loads(tr.read_text());assert md['depHash']==keys[0] and md.get('inputs') and not md.get('synthetic');before=sha(tr);arts={}
 for area in ['lib/lean','ir']:
  stem=P/'.lake/build'/area/n.replace('.','/')
  for f in stem.parent.glob(stem.name+'.*'):
   if not f.is_file() or f.name.endswith(('.c.o','.o','.bc')):continue
   h=sha(f);dest=R/f.relative_to(P);assert not dest.is_symlink() and str(dest.parent.resolve()).startswith(str(R.resolve()))
   if dest.exists():
    assert dest.stat().st_uid==os.getuid() and dest.stat().st_nlink==1;saved=L/'preserved-old-outputs'/dest.relative_to(R);saved.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(dest,saved);assert sha(saved)==sha(dest);dest.unlink()
   dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dest);assert sha(f)==h and sha(dest)==h;arts[str(dest.relative_to(R))]=h
 assert sha(tr)==before;copied[n]={'native_key':keys[0],'trace_sha256':before,'artifacts':arts,'provenance':'proper full-input P native trace'};run('R-normal'+str(i),['lake','build','--no-build',n])
(L/'receipt.json').write_text(json.dumps({'status':'PASSED_TWO_COHERENT_PROPER_P_DONORS;FOUR_SHARED_ROOTS_PENDING_LOOP','copied':copied,'records':records,'complete_dependency_records_sha256':sha(L/'coherent-full-dependencies.json')},indent=2)+'\n')
