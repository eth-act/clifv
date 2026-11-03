from pathlib import Path
import json,hashlib,subprocess,os,psutil,re,shutil,importlib.util
D=Path(__file__).resolve().parent;Q=D.parent;E=Q.parent;R=Q/'validation-package-v1';P=E/'892-joint-current-context-v2/package';L=D/'donor-complete-classification-v1';L.mkdir();I=json.loads((D/'current8f-kernel-manifest.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(D/'current8f-kernel-manifest.json')=='48c9e596dedc944d7df34034f5588f2216b478b38300fc9917f3c379d8d0da42';main='8f073980e9630c8d3cd9d6f6f77ab462474c7bcb';ordered=['FV.E2E.StockResultCallNIW'];baseline=sorted(set(I['import_graph'])-set(ordered));assert len(baseline)==775;staged={'FV/E2E/WorldReturnTraceCore.lean','FV/E2E/StockMemoryMachineReturnValueW.lean'};origin={}
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
 e=dict(env,FV_MEMCAP_STATS=str(L/(label+'.mem')),FV_MEMCAP_UNIT='worker-o-result-call-W-'+label)
 with (L/(label+'.log')).open('w') as f:rc=subprocess.call([str(P/'scripts/memcap.sh'),*args],cwd=R,env=e,stdout=f,stderr=subprocess.STDOUT)
 records.append({'label':label,'argv':args,'exit':rc,'log_sha256':sha(L/(label+'.log')),'memory':(L/(label+'.mem')).read_text()});(L/'progress.json').write_text(json.dumps(records,indent=2)+'\n');print(label,rc,flush=True);assert rc in allowed,(label,rc);return rc


nodes=['FV.E2E.StockResultCallSource','FV.E2E.StockResultCallRun','FV.E2E.StockResultCallPair','FV.E2E.StockResultCallLayout','FV.E2E.StockResultCallDomain']; report={}
def check(label,root,args):
 e=dict(env,FV_ROOT=str(root),FV_MEMCAP_STATS=str(L/(label+'.mem')),FV_MEMCAP_UNIT='worker-o-donor-classify-'+label)
 with (L/(label+'.log')).open('w') as out:rc=subprocess.call([str(P/'scripts/memcap.sh'),*args],cwd=root,env=e,stdout=out,stderr=subprocess.STDOUT)
 records.append({'label':label,'cwd':str(root),'argv':args,'exit':rc,'log_sha256':sha(L/(label+'.log')),'memory':(L/(label+'.mem')).read_text()});(L/'progress.json').write_text(json.dumps(records,indent=2)+'\n');print(label,rc,flush=True);assert rc in (0,3);return rc
for i,n in enumerate(nodes):
 closure=set();todo=[n]
 while todo:
  v=todo.pop()
  if v in closure:continue
  closure.add(v);todo.extend(I['import_graph'][v])
 rc=check('P-target'+str(i),P,['lake','build','--no-build',n]); different=[]
 for v in sorted(closure):
  rel=Path(v.replace('.','/')+'.trace');pt=P/'.lake/build/lib/lean'/rel;rt=R/'.lake/build/lib/lean'/rel
  pm=json.loads(pt.read_text()) if pt.exists() else {};rm=json.loads(rt.read_text()) if rt.exists() else {}
  if pm.get('depHash')!=rm.get('depHash'):different.append({'module':v,'Pkey':pm.get('depHash'),'Rkey':rm.get('depHash'),'P_synthetic':pm.get('synthetic'),'R_synthetic':rm.get('synthetic')})
 report[n]={'P_target_exit':rc,'closure':len(closure),'different_trace_keys':different}
(L/'complete-classification.json').write_text(json.dumps({'records':records,'targets':report,'no_outputs_changed':True},indent=2)+'\n')
