from pathlib import Path
import json,hashlib,subprocess,os,psutil,re,shutil,importlib.util
D=Path(__file__).resolve().parent;Q=D.parent;E=Q.parent;R=Q/'validation-package-v1';P=E/'892-joint-current-context-v2/package';L=D/'current8f-frontier-v1';L.mkdir();I=json.loads((D/'current8f-kernel-manifest.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(D/'current8f-kernel-manifest.json')=='48c9e596dedc944d7df34034f5588f2216b478b38300fc9917f3c379d8d0da42';main='8f073980e9630c8d3cd9d6f6f77ab462474c7bcb';ordered=['FV.E2E.StockResultCallNIW'];baseline=sorted(set(I['import_graph'])-set(ordered));assert len(baseline)==775;staged={'FV/E2E/WorldReturnTraceCore.lean','FV/E2E/StockMemoryMachineReturnValueW.lean'};origin={}
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

affected={'FV.E2E.StockResultCallSource','FV.E2E.StockResultCallRun','FV.E2E.StockResultCallPair','FV.E2E.StockResultCallLayout','FV.E2E.StockResultCallDomain'}
run('unaffected770',['lake','build','--no-build',*sorted(set(baseline)-affected)])
root='FV.E2E.StockResultCallSource'
run('source-deps',['lake','build','--no-build',*I['import_graph'][root]])
run('source-key',['lake','query','--no-build','+'+root+':depHash'])
expected=re.findall(r'^[0-9a-f]{16}$',(L/'source-key.log').read_text(),re.M);assert len(expected)==1
report={'affected_baseline':sorted(affected),'expected_source_key':expected[0],'donors':{}}
for donor in [P,Path('/home/lee/clifv/.worktrees/loop-20261102')]:
 tr=donor/'.lake/build/lib/lean/FV/E2E/StockResultCallSource.trace';md=json.loads(tr.read_text());report['donors'][str(donor)]={'trace_sha256':sha(tr),'native_key':md['depHash'],'synthetic':md.get('synthetic'),'inputs':bool(md.get('inputs')),'matches':md['depHash']==expected[0]}
(L/'frontier.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
