from pathlib import Path
import json,hashlib,subprocess,os,psutil,re,shutil,importlib.util
D=Path(__file__).resolve().parent;Q=D.parent;E=Q.parent;R=Q/'validation-package-v1';P=E/'892-joint-current-context-v2/package';L=D/'remaining-fourteen-classification-v1';L.mkdir();I=json.loads((D/'current8f-kernel-manifest.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(D/'current8f-kernel-manifest.json')=='3c92e1b8f0b2dc1b036964eaaf99c4c6b206b7154479ead774b87d573c20f435';main='8f073980e9630c8d3cd9d6f6f77ab462474c7bcb';ordered=['FV.E2E.StockMemoryStoreCfgMachineW', 'FV.E2E.StockMemoryCapturedCopyNIW', 'FV.E2E.StockMemoryCfgMachineW', 'FV.E2E.StockMemoryCfgNIW', 'FV.E2E.StockMemoryCfgWorldXW', 'FV.E2E.StockMemoryExtLoadNIW', 'FV.E2E.StockMemoryIntegerNIW', 'FV.E2E.StockMemoryStoreMachineW', 'FV.E2E.StockMemoryLoadStoreNIW', 'FV.E2E.StockMemorySretCopyNIW', 'FV.E2E.StockMemoryStoreCfgNIW', 'FV.E2E.StockMemoryStoreNIW'];baseline=sorted(set(I['import_graph'])-set(ordered));assert len(baseline)==1357;staged={'FV/E2E/WorldReturnTraceCore.lean','FV/E2E/StockMemoryMachineReturnValueW.lean','FV/E2E/StockMemoryMachineW.lean','FV/E2E/StockMemoryWorldXW.lean'};origin={}
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
G=Path('/home/lee/clifv/.worktrees/loop-20261102');proposal=json.loads((D/'ordinary2GiB-four-root-alternative-v1.json').read_text());recovered=json.loads((D/'P-two-descendant-recovery-v2/partial-receipt.json').read_text());nodes=sorted(set(proposal['conditional_baseline16'])-set(recovered['copied']));front=set(recovered['remaining_rejected_roots']);assert len(nodes)==14 and len(front)==3
profile_path=E/'stock-current-main-full-gate-v6/conservative-peaks.tsv';profiles={}
for line in profile_path.read_text().splitlines():
 parts=line.split('\t')
 if parts and parts[0] in nodes:profiles[parts[0]]=parts
for entry in recovered['copied'].values():
 for rel,h in entry['artifacts'].items():assert sha(R/rel)==h
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
def at(label,root,args):
 e=dict(env,FV_ROOT=str(root),FV_MEMCAP_STATS=str(L/(label+'.mem')),FV_MEMCAP_UNIT='worker-o-fourteen-'+label)
 with (L/(label+'.log')).open('w') as f:rc=subprocess.call([str(P/'scripts/memcap.sh'),*args],cwd=root,env=e,stdout=f,stderr=subprocess.STDOUT)
 memory=(L/(label+'.mem')).read_text();records.append({'label':label,'cwd':str(root),'argv':args,'exit':rc,'log_sha256':sha(L/(label+'.log')),'memory':memory});(L/'progress.json').write_text(json.dumps(records,indent=2)+'\n');print(label,rc,flush=True);assert rc in (0,3);return rc
report={};key_nodes=[]
for i,n in enumerate(nodes):
 blocked=sorted((closure(n)-{n})&front);rel=n.replace('.','/')+'.lean';entry={'source_sha256':I['source_hashes'][rel],'direct_imports':I['import_graph'][n],'failed_transitive_ancestors':blocked,'historical_profile':profiles.get(n),'profile_scope':'historical MiB estimate; current fit unknown','current_key':None,'donors':{}}
 if not blocked:
  deps=sorted(closure(n)-{n});rc=at('R-deps'+str(i),R,['lake','build','--no-build',*deps]);entry['R_dependency_exit']=rc
  if rc==0:
   rc=at('R-key'+str(i),R,['lake','query','--no-build','+'+n+':depHash']);keys=re.findall(r'^[0-9a-f]{16}$',(L/('R-key'+str(i)+'.log')).read_text(),re.M)
   if rc==0 and len(keys)==1:entry['current_key']=keys[0];key_nodes.append((i,n))
   ready=at('R-ready'+str(i),R,['lake','build','--no-build',n]);entry['R_actual_normal_exit']=ready
 else:entry['key_policy']='defer until actual failed ancestors are proper'
 report[n]=entry
for i,n in key_nodes:
 if report[n].get('R_actual_normal_exit')==0:continue
 full=closure(n)
 for label,donor in [('P',P),('G',G)]:
  source_bad=[];dep_keys_bad=[];dep_files_bad=[];inputs={}
  config_ok=strip(tomllib.loads((donor/'lakefile.toml').read_text()))==strip(tomllib.loads((R/'lakefile.toml').read_text())) and all(sha(donor/c)==sha(R/c) for c in ['lean-toolchain','lake-manifest.json'])
  for node in full:
   rel=node.replace('.','/')+'.lean';path=donor/rel
   if not path.exists() or sha(path)!=I['source_hashes'][rel]:source_bad.append(node)
   trrel=Path('.lake/build/lib/lean')/Path(node.replace('.','/')+'.trace');dt=donor/trrel;rt=R/trrel;dm=json.loads(dt.read_text()) if dt.exists() else {};rm=json.loads(rt.read_text()) if rt.exists() else {};inputs[node]={'donor_key':dm.get('depHash'),'R_key':rm.get('depHash'),'donor_trace_sha256':sha(dt) if dt.exists() else None,'R_trace_sha256':sha(rt) if rt.exists() else None}
   if node!=n and dm.get('depHash')!=rm.get('depHash'):dep_keys_bad.append(node)
  target_trace=donor/'.lake/build/lib/lean'/Path(n.replace('.','/')+'.trace');md=json.loads(target_trace.read_text()) if target_trace.exists() else {};arts={}
  for area in ['lib/lean','ir']:
   stem=donor/'.lake/build'/area/n.replace('.','/')
   for path in stem.parent.glob(stem.name+'.*'):
    if path.is_file() and '.c.o' not in path.name and not path.name.endswith(('.o','.bc')):arts[str(path.relative_to(donor))]=sha(path)
  normal=at(label+'-full-normal'+str(i),donor,['lake','build','--no-build',*sorted(full)]) if config_ok and not source_bad else None
  report[n]['donors'][label]={'native_key':md.get('depHash'),'matches_current_key':md.get('depHash')==report[n]['current_key'],'full_input_nonsynthetic':bool(md.get('inputs')) and not md.get('synthetic'),'source_mismatch':source_bad,'config_ok_except_weak_args':config_ok,'native_dependency_key_mismatch':dep_keys_bad,'actual_full_normal_exit':normal,'artifact_hashes':arts,'dependency_records':inputs,'readiness':'candidate only; output/writer/approved-origin checks remain before reuse'}
for entry in recovered['copied'].values():
 for rel,h in entry['artifacts'].items():assert sha(R/rel)==h
(L/'receipt.json').write_text(json.dumps({'status':'COMPLETE_FOURTEEN_NODE_CLASSIFICATION_ONLY;NO_COPY_OR_KERNEL','nodes':report,'current_frontier':sorted(front),'records':records,'prior_two_recoveries_unchanged':True,'four_parent_kernels_and_audit':'retained; no rerun','affected22_and_baseline1357':'OPEN'},indent=2)+'\n')
