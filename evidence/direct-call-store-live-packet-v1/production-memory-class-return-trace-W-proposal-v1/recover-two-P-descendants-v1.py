from pathlib import Path
import json,hashlib,subprocess,os,psutil,re,shutil,importlib.util
D=Path(__file__).resolve().parent;Q=D.parent;E=Q.parent;R=Q/'validation-package-v1';P=E/'892-joint-current-context-v2/package';L=D/'P-two-descendant-recovery-v1';L.mkdir();I=json.loads((D/'current8f-kernel-manifest.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(D/'current8f-kernel-manifest.json')=='3c92e1b8f0b2dc1b036964eaaf99c4c6b206b7154479ead774b87d573c20f435';main='8f073980e9630c8d3cd9d6f6f77ab462474c7bcb';ordered=['FV.E2E.StockMemoryStoreCfgMachineW', 'FV.E2E.StockMemoryCapturedCopyNIW', 'FV.E2E.StockMemoryCfgMachineW', 'FV.E2E.StockMemoryCfgNIW', 'FV.E2E.StockMemoryCfgWorldXW', 'FV.E2E.StockMemoryExtLoadNIW', 'FV.E2E.StockMemoryIntegerNIW', 'FV.E2E.StockMemoryStoreMachineW', 'FV.E2E.StockMemoryLoadStoreNIW', 'FV.E2E.StockMemorySretCopyNIW', 'FV.E2E.StockMemoryStoreCfgNIW', 'FV.E2E.StockMemoryStoreNIW'];baseline=sorted(set(I['import_graph'])-set(ordered));assert len(baseline)==1357;staged={'FV/E2E/WorldReturnTraceCore.lean','FV/E2E/StockMemoryMachineReturnValueW.lean','FV/E2E/StockMemoryMachineW.lean','FV/E2E/StockMemoryWorldXW.lean'};origin={}
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
classification_path=D/'remaining-two-current-donor-checks-v1/receipt.json';assert sha(classification_path)=='f68d045e2ebd340fab3d965be8b69ad5dbc1b6cb66b209c90888c4e2c3306495';classification=json.loads(classification_path.read_text())
exception_path=D/'two-descendant-P-setup-input-review-v1.json';assert sha(exception_path)=='8b1a7b2375e0af2286e4ecdf6361475db8206b43ceade282b8d3ca212bc08f6f';exception=json.loads(exception_path.read_text());allowed_inputs=set(exception['exact_setup_inputs']);assert len(allowed_inputs)==2
proposal=json.loads((D/'ordinary2GiB-four-root-alternative-v1.json').read_text());previous=json.loads((D/'ordinary2GiB-four-root-run-v1/receipt.json').read_text());protected=dict(previous['protected_outputs'])
for entry in previous['passed_targets'].values():protected.update(entry['artifacts'])
for rel,h in protected.items():assert sha(R/rel)==h
setup_before={};copied={};coherence={}
def closure(n):
 found=set();todo=[n]
 while todo:
  a=todo.pop()
  if a in found:continue
  found.add(a);todo+=I['import_graph'][a]
 return found
def strip(v):
 if isinstance(v,dict):return {k:strip(a) for k,a in v.items() if k!='weakLeanArgs'}
 if isinstance(v,list):return [strip(a) for a in v]
 return v
def writers(prefix,nodes):
 found=[];names=set(nodes)
 for proc in psutil.process_iter(['uids','name','status','cmdline']):
  try:
   if proc.info['uids'].real!=os.getuid() or proc.info['name'] not in ['lean','lake'] or proc.info['status']=='zombie':continue
   args=proc.info['cmdline'] or [];cwd=proc.cwd()
   if not cwd.startswith(str(prefix)):continue
   if proc.info['name']=='lean':
    if any(str(prefix/source_path(n)) in args or str(source_path(n)) in args for n in names):found.append({'pid':proc.pid,'cwd':cwd,'argv':args})
   elif 'build' in args and '--no-build' not in args:
    if any(a.lstrip('+').split(':')[0] in names for a in args):found.append({'pid':proc.pid,'cwd':cwd,'argv':args})
  except(psutil.NoSuchProcess,psutil.AccessDenied):pass
 return found
def donor_normal(label,nodes):
 args=['lake','build','--no-build',*sorted(nodes)];e=dict(env,FV_ROOT=str(P),FV_MEMCAP_STATS=str(L/(label+'.mem')),FV_MEMCAP_UNIT='worker-o-P-recovery-'+label)
 with (L/(label+'.log')).open('w') as f:rc=subprocess.call([str(P/'scripts/memcap.sh'),*args],cwd=P,env=e,stdout=f,stderr=subprocess.STDOUT)
 memory=(L/(label+'.mem')).read_text();records.append({'label':label,'cwd':str(P),'argv':args,'exit':rc,'log_sha256':sha(L/(label+'.log')),'memory':memory});(L/'progress.json').write_text(json.dumps(records,indent=2)+'\n');print(label,rc,flush=True);assert rc==0 and 'oom 0\n' in memory and 'oom_kill 0\n' in memory
assert strip(tomllib.loads((P/'lakefile.toml').read_text()))==strip(tomllib.loads((R/'lakefile.toml').read_text()))
for c in ['lean-toolchain','lake-manifest.json']:assert sha(P/c)==sha(R/c)
for i,n in enumerate(classification['roots']):
 full=closure(n);deps=sorted(full-{n});assert not writers(P,full),writers(P,full)
 for node in full:
  rel=node.replace('.','/')+'.lean';assert sha(P/rel)==sha(R/rel)==I['source_hashes'][rel],node
 run('R-dependencies'+str(i),['lake','build','--no-build',*deps]);run('R-key'+str(i),['lake','query','--no-build','+'+n+':depHash']);keys=re.findall(r'^[0-9a-f]{16}$',(L/('R-key'+str(i)+'.log')).read_text(),re.M);assert keys==[classification['roots'][n]['current_R_key']]
 donor_normal('P-complete-normal'+str(i),full);tr=P/'.lake/build/lib/lean'/Path(n.replace('.','/')+'.trace');md=json.loads(tr.read_text());assert md['depHash']==keys[0] and md.get('inputs') and not md.get('synthetic');original_trace=sha(tr)
 changes=[];dep_records={}
 for node in deps:
  trel=Path('.lake/build/lib/lean')/Path(node.replace('.','/')+'.trace');pm=json.loads((P/trel).read_text());rm=json.loads((R/trel).read_text());assert pm['depHash']==rm['depHash'],('Dependency key mismatch',node);dep_records[node]={'native_key':pm['depHash'],'P_trace_sha256':sha(P/trel),'R_trace_sha256':sha(R/trel),'outputs':{}}
  for area in ['lib/lean','ir']:
   stem=P/'.lake/build'/area/node.replace('.','/')
   for f in stem.parent.glob(stem.name+'.*'):
    if not f.is_file() or f.name.endswith('.trace') or '.c.o' in f.name or f.name.endswith(('.o','.bc')):continue
    rel=str(f.relative_to(P));other=R/rel;assert other.exists(),rel;ph=sha(f);rh=sha(other)
    if ph!=rh:
     assert rel in allowed_inputs,('Unapproved difference',rel)
     normalized_R=json.loads(json.dumps(json.loads(other.read_text())).replace(str(R),'<OWNED_PREFIX>'));normalized_P=json.loads(json.dumps(json.loads(f.read_text())).replace(str(P),'<OWNED_PREFIX>'));assert normalized_R==normalized_P,rel;changes.append({'path':rel,'R_sha256':rh,'P_sha256':ph,'exception':'exact two-prefix substitution; every JSON field retained'})
    dep_records[node]['outputs'][rel]={'R_sha256':rh,'P_sha256':ph}
 for rel in allowed_inputs:setup_before.setdefault(rel,sha(R/rel))
 target_setup=Path('.lake/build/ir')/Path(n.replace('.','/')+'.setup.json')
 if (R/target_setup).exists():setup_before.setdefault(str(target_setup),sha(R/target_setup))
 assert not md['outputs']['m'] and len(md['outputs']['o'])==1
 required=[('.lake/build/lib/lean/'+n.replace('.','/'),'.olean'),('.lake/build/lib/lean/'+n.replace('.','/'),'.ilean'),('.lake/build/ir/'+n.replace('.','/'),'.c')]
 promote={str(Path('.lake/build/lib/lean')/Path(n.replace('.','/')+'.trace')):sha(tr)}
 for stem,ext in required:
  rel=stem+ext;assert (P/rel).is_file();promote[rel]=sha(P/rel)
  assert (P/(rel+'.hash')).is_file();promote[rel+'.hash']=sha(P/(rel+'.hash'))
 assert len(promote)==7
 for rel,h in promote.items():assert h==classification['roots'][n]['donors']['P']['target_artifacts'][rel],('Donor changed since classification',n,rel)
 assert not writers(P,full),writers(P,full)
 for rel,h in promote.items():
  dest=R/rel;src=P/rel;assert not dest.is_symlink() and str(dest.parent.resolve()).startswith(str(R.resolve()))
  if dest.exists():
   assert dest.stat().st_uid==os.getuid() and dest.stat().st_nlink==1
   old=L/'preserved-old-targets'/rel;old.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(dest,old);assert sha(old)==sha(dest);dest.unlink()
  dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest);assert sha(src)==h and sha(dest)==h
 assert sha(tr)==original_trace
 copied[n]={'native_key':keys[0],'trace_sha256':original_trace,'artifacts':promote,'all_R_setup_files_retained':True,'actual_producer':'full-input nonsynthetic P native trace'};coherence[n]={'full_dependency_records':dep_records,'exact_allowed_setup_differences':changes}
 run('R-recovered-normal'+str(i),['lake','build','--no-build',n]);(L/'passed-copies.json').write_text(json.dumps(copied,indent=2)+'\n')
 for rel,h in protected.items():assert sha(R/rel)==h
 for rel,h in setup_before.items():assert sha(R/rel)==h
(L/'coherence.json').write_text(json.dumps(coherence,indent=2)+'\n')
run('affected22-normal',['lake','build','--no-build',*proposal['affected_baseline22']]);run('baseline1357-normal',['lake','build','--no-build',*baseline])
for rel,h in protected.items():assert sha(R/rel)==h
for rel,h in setup_before.items():assert sha(R/rel)==h
for c,h in cfg.items():assert sha(R/c)==h
(L/'receipt.json').write_text(json.dumps({'status':'PASSED_EXACT_P_RECOVERY_TWO_DESCENDANTS_AFFECTED22_BASELINE1357','records':records,'copied':copied,'coherence_sha256':sha(L/'coherence.json'),'only_named_setup_input_exception_sha256':sha(exception_path),'R_setup_hashes_unchanged':setup_before,'all_protected_W_and_four_parent_outputs_unchanged':True,'new_kernels':[],'G_used':False,'twelve_new_memory_exports':'READY_FOR_SEPARATE_FOCUSED_GATES;NOT_PASSED'},indent=2)+'\n')
