from pathlib import Path
import json,hashlib,subprocess,os,psutil,re,shutil,importlib.util
D=Path(__file__).resolve().parent;Q=D.parent;E=Q.parent;R=Q/'validation-package-v1';P=E/'892-joint-current-context-v2/package';L=D/'current8f-focused-v1';L.mkdir();I=json.loads((D/'current8f-kernel-manifest.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(D/'current8f-kernel-manifest.json')=='48c9e596dedc944d7df34034f5588f2216b478b38300fc9917f3c379d8d0da42';main='8f073980e9630c8d3cd9d6f6f77ab462474c7bcb';ordered=['FV.E2E.StockResultCallNIW'];baseline=sorted(set(I['import_graph'])-set(ordered));assert len(baseline)==775;staged={'FV/E2E/WorldReturnTraceCore.lean','FV/E2E/StockMemoryMachineReturnValueW.lean'};origin={}
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
run('baseline775',['lake','build','--no-build',*baseline])
for n in ordered:
 rel=Path(n.replace('.','/')+'.lean');dest=R/rel;src=D/'source'/rel;assert not dest.exists() or sha(dest)==sha(src),n
 if not dest.exists():dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest)
for i,n in enumerate(ordered):
 run('deps'+str(i),['lake','build','--no-build',*I['import_graph'][n]]);run('key'+str(i),['lake','query','--no-build','+'+n+':depHash']);keys=re.findall(r'^[0-9a-f]{16}$',(L/('key'+str(i)+'.log')).read_text(),re.M);assert len(keys)==1;ready=run('ready'+str(i),['lake','build','--no-build',n],allowed=(0,3))==0
 if not ready:
  rejected=re.findall(r'✖ .* Building ([\w.]+)',(L/('ready'+str(i)+'.log')).read_text());assert set(rejected)=={n},(n,rejected);run('kernel'+str(i),['lake','-v','build','+'+n+':leanArts'])
 run('normal'+str(i),['lake','build','--no-build',n]);tr=R/'.lake/build/lib/lean'/Path(n.replace('.','/')+'.trace');data=json.loads(tr.read_text());assert data.get('inputs') and not data.get('synthetic') and data['depHash']==keys[0];arts={}
 for area in ['lib/lean','ir']:
  stem=R/'.lake/build'/area/n.replace('.','/')
  for p in stem.parent.glob(stem.name+'.*'):
   if p.is_file():arts[str(p.relative_to(R))]=sha(p)
 outputs[n]={'native_key':keys[0],'trace_sha256':sha(tr),'artifacts':arts}
run('complete776',['lake','build','--no-build',*sorted(I['import_graph'])]);roots=I['standard_audit_roots'];audit=L/'result-call-w.lean';audit.write_text('import FV.E2E.StockResultCallNIW\n\n'+''.join('#print axioms '+n+'\n' for n in roots));run('real-audit2',['python3',str(P/'scripts/axiom-audit.py'),'--cwd',str(R),'--log-dir',str(L/'audit'),str(audit)]);spec=importlib.util.spec_from_file_location('result_call_axioms',E/'general7-main-candidate-v1/old-axiom-preservation-v1/axiom_records.py');collector=importlib.util.module_from_spec(spec);spec.loader.exec_module(collector);axes={}
for p in (L/'audit').glob('*.log'):
 for n,a in collector.parse_records(p.read_text()):assert n not in axes;axes[n]=sorted(a)
assert set(axes)==set(roots) and all(set(a)<={'Classical.choice','Quot.sound','propext'} for a in axes.values())
for c,h in cfg.items():assert sha(R/c)==h,c
(L/'receipt.json').write_text(json.dumps({'status':'PASSED_CURRENT8F_SOURCE_PROJECTION_RESULT_CALL_W2;STAGED_HELPERS_EXPLICIT','main':main,'source_context_sha256':sha(L/'current-source-context.json'),'source_manifest_sha256':sha(D/'current8f-kernel-manifest.json'),'records':records,'outputs':outputs,'axiom_sets':axes,'original_inputs_preserved':True,'new_caller_premises':[],'complete_dispatcher_and_production':'OPEN'},indent=2)+'\n')
