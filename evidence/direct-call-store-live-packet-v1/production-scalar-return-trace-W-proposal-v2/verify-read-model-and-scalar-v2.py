from pathlib import Path
import os,json,hashlib,subprocess,psutil,re,shutil,importlib.util
D=Path(__file__).resolve().parent;Q=D.parent;E=Q.parent;R=Q/'validation-package-v1';P=E/'892-joint-current-context-v2/package';Models=Q/'production-read-model-return-trace-W-proposal-v2';L=D/'focused-read-model-scalar-v2';L.mkdir();I=json.loads((D/'source-context.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(D/'manifest.json')=='9eee046fe9afd1151b9716be51c79f5bd9136dee0b8c1555e02206dde03939d3';assert sha(Models/'manifest.json')=='0cfe9c856cdf51a4116ff2b803396455d3952fcc7e0ce2dfa4e6f5befa298232';owned={'FV.E2E.StockMemoryMachineReturnValueW','FV.E2E.ABIReadModelsReturnTraceW','FV.E2E.StockScalarNIW'};ordered=['FV.E2E.ABIReadModelsReturnTraceW','FV.E2E.StockScalarNIW'];baseline=sorted(set(I['graph'])-owned);assert len(baseline)==762
for n,rec in I['sources'].items():assert sha(Path(rec['source_path']))==rec['sha256'],n
for n in baseline:
 assert not(set(I['graph'][n])&owned),(n,'baseline depends on candidate');assert sha(R/Path(n.replace('.','/')+'.lean'))==I['sources'][n]['sha256'],n
assert sha(R/'FV/E2E/StockMemoryMachineReturnValueW.lean')=='16de4b145d2b067f2936b590b4b2957b71ee32fcc25c498cda01f9e4134cede0'
for p in psutil.process_iter(['uids','name','status','cmdline']):
 try:
  if p.info['uids'].real!=os.getuid() or p.info['name'] not in ['lean','lake'] or p.info['status']=='zombie':continue
  assert not p.cwd().startswith(str(R)) and not any(str(R) in a for a in (p.info['cmdline'] or [])),('R writer',p.pid)
 except(psutil.NoSuchProcess,psutil.AccessDenied):pass
cfg={n:sha(R/n) for n in ['lean-toolchain','lake-manifest.json','lakefile.toml']};env=dict(os.environ)
for k in ['FV_MEMCAP_OFF','FV_LAKE_CACHE','LEAN_PATH','LEAN_SYSROOT','LEAN_SRC_PATH','LAKE_CACHE_DIR']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(R),FV_MEMCAP='2G',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1');records=[];outputs={}
def run(label,args,allowed=(0,)):
 e=dict(env,FV_MEMCAP_STATS=str(L/(label+'.mem')),FV_MEMCAP_UNIT='worker-o-read-model-scalar-'+label)
 with (L/(label+'.log')).open('w') as f:rc=subprocess.call([str(P/'scripts/memcap.sh'),*args],cwd=R,env=e,stdout=f,stderr=subprocess.STDOUT)
 records.append({'label':label,'argv':args,'exit':rc,'log_sha256':sha(L/(label+'.log')),'memory':(L/(label+'.mem')).read_text()});(L/'progress.json').write_text(json.dumps(records,indent=2)+'\n');print(label,rc,flush=True);assert rc in allowed,(label,rc);return rc
passed_peer=json.loads((D/'passed-peer-machine.json').read_text())
for rel,h in passed_peer['artifacts'].items():assert sha(R/rel)==h,rel
(L/'reused-baseline762-peer.json').write_text(json.dumps({'prior_baseline_exit':0,'passed_peer_native_key':passed_peer['native_key'],'peer_artifacts_unchanged':True,'baseline_source_and_config_rechecked':True})+'\n')
for n in ordered:
 src=Path(I['sources'][n]['source_path']);dest=R/Path(n.replace('.','/')+'.lean');
 if dest.exists() and sha(dest)!=sha(src):
  assert n=='FV.E2E.ABIReadModelsReturnTraceW' and sha(dest)==sha(Q/'production-read-model-return-trace-W-proposal-v2/failed-source-v1.lean'),n
  (L/'failed-helper-source-before-fix.lean').write_bytes(dest.read_bytes());dest.unlink()
 dest.parent.mkdir(parents=True,exist_ok=True)
 if not dest.exists():shutil.copyfile(src,dest)
for index,n in enumerate(ordered):
 run('deps'+str(index),['lake','build','--no-build',*I['graph'][n]]);run('key'+str(index),['lake','query','--no-build','+'+n+':depHash']);keys=re.findall(r'^[0-9a-f]{16}$',(L/('key'+str(index)+'.log')).read_text(),re.M);assert len(keys)==1
 ready=run('ready'+str(index),['lake','build','--no-build',n],allowed=(0,3))==0
 if not ready:
  rejected=re.findall(r'✖ .* Building ([\w.]+)',(L/('ready'+str(index)+'.log')).read_text());assert set(rejected)=={n},(n,rejected)
  for area in ['lib/lean','ir']:
   stem=R/'.lake/build'/area/n.replace('.','/')
   for f in stem.parent.glob(stem.name+'.*'):
    if not f.is_file():continue
    dest=L/'old-artifacts'/f.relative_to(R);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dest)
    if f.is_symlink() or f.stat().st_nlink!=1 or not f.stat().st_mode&0o200:
     temp=f.with_name(f.name+'.read-model-owned');shutil.copyfile(f,temp);os.replace(temp,f)
  run('kernel'+str(index),['lake','-v','build','+'+n+':leanArts'])
 run('normal'+str(index),['lake','build','--no-build',n]);trace=R/'.lake/build/lib/lean'/Path(n.replace('.','/')+'.trace');meta=json.loads(trace.read_text());assert meta.get('inputs') and not meta.get('synthetic') and meta['depHash']==keys[0];arts={}
 for area in ['lib/lean','ir']:
  stem=R/'.lake/build'/area/n.replace('.','/')
  for p in stem.parent.glob(stem.name+'.*'):
   if p.is_file():arts[str(p.relative_to(R))]=sha(p)
 outputs[n]={'native_key':keys[0],'trace_sha256':sha(trace),'artifacts':arts}
run('complete765',['lake','build','--no-build',*sorted(I['graph'])]);roots=['E2E.MixedFlagBoundary.machine_returnW','E2E.ScalarBoundary.machine_returnW','E2E.DivBoundary.machine_returnW','E2E.CfgBoundary.machine_returnW','E2E.backend_correct_world_niX_stock_scalarW','E2E.worldReturnTraceProvider_scalar'];audit=L/'read-model-scalar.lean';audit.write_text('import FV.E2E.StockScalarNIW\n\n'+''.join('#print axioms '+n+'\n' for n in roots));run('real-audit6',['python3',str(P/'scripts/axiom-audit.py'),'--cwd',str(R),'--log-dir',str(L/'audit'),str(audit)]);spec=importlib.util.spec_from_file_location('source_axioms',E/'general7-main-candidate-v1/old-axiom-preservation-v1/axiom_records.py');collector=importlib.util.module_from_spec(spec);spec.loader.exec_module(collector);axes={}
for p in (L/'audit').glob('*.log'):
 for n,a in collector.parse_records(p.read_text()):assert n not in axes;axes[n]=sorted(a)
assert set(axes)==set(roots) and all(set(a)<={'Classical.choice','Quot.sound','propext'} for a in axes.values())
for n,h in cfg.items():assert sha(R/n)==h,n
for n,rec in I['sources'].items():assert sha(R/Path(n.replace('.','/')+'.lean'))==rec['sha256'],n
(L/'receipt.json').write_text(json.dumps({'status':'PASSED_STAGED_READ_MODELS4_AND_SCALAR2_STANDARD_ROOTS','source_context_sha256':sha(D/'source-context.json'),'scalar_manifest_sha256':sha(D/'manifest.json'),'models_manifest_sha256':sha(Models/'manifest.json'),'configs':cfg,'records':records,'outputs':outputs,'axiom_sets':axes,'no_old_source_changes':True,'full_production_complete':False},indent=2)+'\n')
