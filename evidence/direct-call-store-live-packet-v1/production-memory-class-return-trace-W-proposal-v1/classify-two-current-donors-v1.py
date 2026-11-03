from pathlib import Path
import json,hashlib,subprocess,os,psutil,re,shutil,importlib.util
D=Path(__file__).resolve().parent;Q=D.parent;E=Q.parent;R=Q/'validation-package-v1';P=E/'892-joint-current-context-v2/package';L=D/'remaining-two-current-donor-checks-v1';L.mkdir();I=json.loads((D/'current8f-kernel-manifest.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(D/'current8f-kernel-manifest.json')=='3c92e1b8f0b2dc1b036964eaaf99c4c6b206b7154479ead774b87d573c20f435';main='8f073980e9630c8d3cd9d6f6f77ab462474c7bcb';ordered=['FV.E2E.StockMemoryStoreCfgMachineW', 'FV.E2E.StockMemoryCapturedCopyNIW', 'FV.E2E.StockMemoryCfgMachineW', 'FV.E2E.StockMemoryCfgNIW', 'FV.E2E.StockMemoryCfgWorldXW', 'FV.E2E.StockMemoryExtLoadNIW', 'FV.E2E.StockMemoryIntegerNIW', 'FV.E2E.StockMemoryStoreMachineW', 'FV.E2E.StockMemoryLoadStoreNIW', 'FV.E2E.StockMemorySretCopyNIW', 'FV.E2E.StockMemoryStoreCfgNIW', 'FV.E2E.StockMemoryStoreNIW'];baseline=sorted(set(I['import_graph'])-set(ordered));assert len(baseline)==1357;staged={'FV/E2E/WorldReturnTraceCore.lean','FV/E2E/StockMemoryMachineReturnValueW.lean','FV/E2E/StockMemoryMachineW.lean','FV/E2E/StockMemoryWorldXW.lean'};origin={}
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
G=Path('/home/lee/clifv/.worktrees/loop-20261102')
roots=['FV.Backend.Proof.StockMemoryOffsetEightStoreRecord','FV.Backend.Proof.StockMemoryOrdinarySourceContinuation']
prior=json.loads((D/'ordinary2GiB-four-root-run-v1/receipt.json').read_text())
for entry in prior['passed_targets'].values():
 for rel,h in entry['artifacts'].items():assert sha(R/rel)==h
assert len(prior['passed_targets'])==4
def closure(n):
 found=set();todo=[n]
 while todo:
  x=todo.pop()
  if x in found:continue
  found.add(x);todo+=I['import_graph'][x]
 return found
def strip(v):
 if isinstance(v,dict):return {k:strip(a) for k,a in v.items() if k!='weakLeanArgs'}
 if isinstance(v,list):return [strip(a) for a in v]
 return v
def donor_run(label,root,args):
 e=dict(env,FV_ROOT=str(root),FV_MEMCAP_STATS=str(L/(label+'.mem')),FV_MEMCAP_UNIT='worker-o-two-donor-'+label)
 with (L/(label+'.log')).open('w') as f:rc=subprocess.call([str(P/'scripts/memcap.sh'),*args],cwd=root,env=e,stdout=f,stderr=subprocess.STDOUT)
 records.append({'label':label,'cwd':str(root),'argv':args,'exit':rc,'log_sha256':sha(L/(label+'.log')),'memory':(L/(label+'.mem')).read_text()});(L/'progress.json').write_text(json.dumps(records,indent=2)+'\n');print(label,rc,flush=True);assert rc in (0,3);return rc
report={}
for i,n in enumerate(roots):
 full=closure(n);deps=sorted(full-{n});run('R-deps'+str(i),['lake','build','--no-build',*deps]);run('R-key'+str(i),['lake','query','--no-build','+'+n+':depHash']);keys=re.findall(r'^[0-9a-f]{16}$',(L/('R-key'+str(i)+'.log')).read_text(),re.M);assert len(keys)==1
 report[n]={'current_R_key':keys[0],'R_complete_dependencies_pass':True,'donors':{}}
 for label,donor in [('P',P),('G',G)]:
  config_ok=strip(tomllib.loads((donor/'lakefile.toml').read_text()))==strip(tomllib.loads((R/'lakefile.toml').read_text())) and all(sha(donor/c)==sha(R/c) for c in ['lean-toolchain','lake-manifest.json'])
  bad_sources=[];bad_keys=[];artifacts={};all_inputs={}
  for node in sorted(full):
   rel=node.replace('.','/')+'.lean';sp=donor/rel
   if not sp.exists() or sha(sp)!=I['source_hashes'][rel]:bad_sources.append(node)
   trrel=Path('.lake/build/lib/lean')/Path(node.replace('.','/')+'.trace');dt=donor/trrel;rt=R/trrel;dm=json.loads(dt.read_text()) if dt.exists() else {};rm=json.loads(rt.read_text()) if rt.exists() else {}
   all_inputs[node]={'donor_key':dm.get('depHash'),'R_stored_key':rm.get('depHash'),'donor_trace_sha256':sha(dt) if dt.exists() else None,'R_trace_sha256':sha(rt) if rt.exists() else None}
   if node!=n and dm.get('depHash')!=rm.get('depHash'):bad_keys.append(node)
  target_trace=donor/'.lake/build/lib/lean'/Path(n.replace('.','/')+'.trace');md=json.loads(target_trace.read_text());before=sha(target_trace)
  for area in ['lib/lean','ir']:
   stem=donor/'.lake/build'/area/n.replace('.','/')
   for f in stem.parent.glob(stem.name+'.*'):
    if f.is_file() and '.c.o' not in f.name and not f.name.endswith(('.o','.bc')):artifacts[str(f.relative_to(donor))]=sha(f)
  rc=donor_run(label+'-full-normal'+str(i),donor,['lake','build','--no-build',*sorted(full)]) if config_ok and not bad_sources else None
  assert sha(target_trace)==before,('Donor changed during check',label,n)
  key_ok=md.get('depHash')==keys[0];proper=bool(md.get('inputs')) and not md.get('synthetic')
  eligible=config_ok and not bad_sources and not bad_keys and rc==0 and key_ok and proper
  output_differences=[]
  if eligible:
   for node in deps:
    for area in ['lib/lean','ir']:
     stem=donor/'.lake/build'/area/node.replace('.','/')
     for f in stem.parent.glob(stem.name+'.*'):
      if not f.is_file() or f.name.endswith('.trace') or '.c.o' in f.name or f.name.endswith(('.o','.bc')):continue
      other=R/f.relative_to(donor)
      if not other.exists() or sha(other)!=sha(f):output_differences.append(str(f.relative_to(donor)))
   eligible=not output_differences
  report[n]['donors'][label]={'native_key':md.get('depHash'),'matches_current_R_key':key_ok,'full_input_nonsynthetic':proper,'source_mismatch':bad_sources,'config_equal_except_weak_args':config_ok,'native_dependency_key_mismatch':bad_keys,'complete_normal_exit':rc,'target_artifacts':artifacts,'trace_sha256':before,'dependency_output_differences':output_differences,'eligible_for_reviewed_reuse':eligible,'full_dependency_records':all_inputs}
for entry in prior['passed_targets'].values():
 for rel,h in entry['artifacts'].items():assert sha(R/rel)==h
(L/'receipt.json').write_text(json.dumps({'status':'CLASSIFICATION_COMPLETE;NO_COPY_OR_COMPILER','roots':report,'records':records,'four_passed_parent_artifacts_unchanged':True,'conditional_descendants':'All fourteen remain deferred until the two root rejections pass','descendant_kernels':[]},indent=2)+'\n')
