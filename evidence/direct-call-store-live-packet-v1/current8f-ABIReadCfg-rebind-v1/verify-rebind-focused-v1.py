from pathlib import Path
import os,json,hashlib,subprocess,psutil,shutil,re,tomllib,importlib.util
D=Path(__file__).resolve().parent;Q=D.parent;E=Q.parent;R=Q/'validation-package-v1';G=Path('/home/lee/clifv/.worktrees/loop-20261102');P=E/'892-joint-current-context-v2/package';L=D/'focused-current8f-v1';L.mkdir();I=json.loads((D/'manifest.json').read_text());S=Q/'production-scalar-return-trace-W-proposal-v2';Ctx=json.loads((S/'source-context.json').read_text());main=I['main'];
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1048576):h.update(b)
 return h.hexdigest()
assert sha(D/'manifest.json')=='147e4cd23d639b965a0f0d7a57acbfb7ff12f59bd7cb2644c37e188fc3ffb44e'
for proc in psutil.process_iter(['uids','name','status','cmdline']):
 try:
  if proc.info['uids'].real!=os.getuid() or proc.info['name'] not in ['lean','lake'] or proc.info['status']=='zombie':continue
  cwd=proc.cwd();args=proc.info['cmdline'] or [];assert not any(cwd.startswith(str(root)) or any(str(root) in a for a in args) for root in [R,G]),('R/G writer',proc.pid)
 except(psutil.NoSuchProcess,psutil.AccessDenied):pass
for n,r in I['delta'].items():assert sha(R/Path(n.replace('.','/')+'.lean'))==r['old_sha256'],n
for c,h in I['configs'].items():assert sha(R/c)==h,c
# Preserve every existing R output hash before the two source changes.
all_outputs={}
for f in (R/'.lake/build').rglob('*'):
 if f.is_file():
  before=f.stat();h=sha(f);after=f.stat();assert (before.st_size,before.st_mtime_ns)==(after.st_size,after.st_mtime_ns),('Output changed during snapshot',str(f));all_outputs[str(f.relative_to(R))]={'sha256':h,'bytes':after.st_size}
(L/'all-R-build-before.json').write_text(json.dumps(all_outputs,indent=2)+'\n')
passed=json.loads((D/'preserved-passed-W-output-records.json').read_text());unaffected={}
for label in ['validated','arithmetic']:
 for key,val in passed[label]['outputs'].items():
  # Validated uses a flat file map; arithmetic uses per-module records.
  artifacts=val['artifacts'] if isinstance(val,dict) and 'artifacts' in val else {key:val}
  for rel,h in artifacts.items():assert sha(R/rel)==h,(label,rel);unaffected[rel]=h
(L/'unaffected-W-before.json').write_text(json.dumps(unaffected,indent=2)+'\n')
env=dict(os.environ)
for k in ['FV_MEMCAP_OFF','FV_LAKE_CACHE','LEAN_PATH','LEAN_SYSROOT','LEAN_SRC_PATH','LAKE_CACHE_DIR']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_MEMCAP='2G',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1');records=[]
def run(label,root,args,allowed=(0,)):
 e=dict(env,FV_ROOT=str(root),FV_MEMCAP_STATS=str(L/(label+'.mem')),FV_MEMCAP_UNIT='worker-o-8f-rebind-'+label)
 with (L/(label+'.log')).open('w') as out:rc=subprocess.call([str(P/'scripts/memcap.sh'),*args],cwd=root,env=e,stdout=out,stderr=subprocess.STDOUT)
 records.append({'label':label,'root':str(root),'argv':args,'exit':rc,'log_sha256':sha(L/(label+'.log')),'memory':(L/(label+'.mem')).read_text()});(L/'progress.json').write_text(json.dumps(records,indent=2)+'\n');print(label,rc,flush=True);assert rc in allowed,(label,rc);return rc
providers=['FV.Backend.ABIReadCfg','FV.E2E.ABIReadCfg'];affected=set(I['scalar_current765_affected_cone4']);baseline=sorted(set(Ctx['graph'])-affected);assert len(baseline)==761
# Check every current-main source before materialization; retain all explicit staged W modules.
new_sources={}
for n,rec in Ctx['sources'].items():
 rel=Path(n.replace('.','/')+'.lean');path=Path(I['delta'][n]['new_source_path']) if n in providers else R/rel;assert path.exists(),path;h=sha(path)
 if n in providers:assert h==I['delta'][n]['new_sha256']
 else:assert h==rec['sha256'],n
 new_sources[n]=h
 staged=n in ['FV.E2E.WorldReturnTraceCore','FV.E2E.StockMemoryMachineReturnValueW','FV.E2E.ABIReadModelsReturnTraceW','FV.E2E.StockScalarNIW']
 if not staged:
  blob=subprocess.check_output(['git','show',main+':'+str(rel)]);assert hashlib.sha256(blob).hexdigest()==h,('Current8f source mismatch',n)
run('unchanged-baseline761',R,['lake','build','--no-build',*baseline]);run('G-published-providers',G,['lake','build','--no-build',*providers])
for n in providers:
 rel=Path(n.replace('.','/')+'.lean');dest=R/rel;src=Path(I['delta'][n]['new_source_path']);assert not dest.is_symlink();dest.unlink();shutil.copyfile(src,dest);assert sha(dest)==I['delta'][n]['new_sha256']
copy={}
def strip_weak(x):
 if isinstance(x,dict):return {k:strip_weak(v) for k,v in x.items() if k!='weakLeanArgs'}
 if isinstance(x,list):return [strip_weak(v) for v in x]
 return x
assert strip_weak(tomllib.loads((R/'lakefile.toml').read_text()))==strip_weak(tomllib.loads((G/'lakefile.toml').read_text()))
for c in ['lean-toolchain','lake-manifest.json']:assert sha(R/c)==sha(G/c)
for i,n in enumerate(providers):
 run('provider-deps'+str(i),R,['lake','build','--no-build',*Ctx['graph'][n]]);run('provider-key'+str(i),R,['lake','query','--no-build','+'+n+':depHash']);keys=re.findall(r'^[0-9a-f]{16}$',(L/('provider-key'+str(i)+'.log')).read_text(),re.M);assert len(keys)==1;tr=G/'.lake/build/lib/lean'/Path(n.replace('.','/')+'.trace');md=json.loads(tr.read_text());assert md['depHash']==keys[0] and md.get('inputs') and not md.get('synthetic'),(n,'G donor key/provenance mismatch');closure=set();todo=[n]
 while todo:
  cur=todo.pop()
  if cur in closure:continue
  closure.add(cur);todo.extend(Ctx['graph'][cur])
 for cur in closure:assert sha(G/Path(cur.replace('.','/')+'.lean'))==new_sources[cur],(n,cur,'G donor source closure differs')
 before=sha(tr);arts={}
 for area in ['lib/lean','ir']:
  stem=G/'.lake/build'/area/n.replace('.','/')
  for f in stem.parent.glob(stem.name+'.*'):
   if not f.is_file() or f.name.endswith(('.c.o','.o','.bc')):continue
   h=sha(f);dest=R/f.relative_to(G)
   if dest.exists():
    old=L/'old-affected-provider-outputs'/dest.relative_to(R);old.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(dest,old);dest.unlink()
   dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dest);assert sha(dest)==h and sha(f)==h;arts[str(dest.relative_to(R))]=h
 assert sha(tr)==before;copy[n]={'native_key':keys[0],'trace_sha256':before,'artifacts':arts};run('provider-normal'+str(i),R,['lake','build','--no-build',n])
(L/'verified-G-reuse.json').write_text(json.dumps(copy,indent=2)+'\n');outputs={}
for i,n in enumerate(['FV.E2E.ABIReadModelsReturnTraceW','FV.E2E.StockScalarNIW']):
 run('owned-deps'+str(i),R,['lake','build','--no-build',*Ctx['graph'][n]]);ready=run('owned-ready'+str(i),R,['lake','build','--no-build',n],allowed=(0,3))==0
 if not ready:
  bad=re.findall(r'✖ .* Building ([\w.]+)',(L/('owned-ready'+str(i)+'.log')).read_text());assert set(bad)=={n},(n,bad);run('owned-kernel'+str(i),R,['lake','-v','build','+'+n+':leanArts'])
 run('owned-normal'+str(i),R,['lake','build','--no-build',n]);tr=R/'.lake/build/lib/lean'/Path(n.replace('.','/')+'.trace');md=json.loads(tr.read_text());assert md.get('inputs') and not md.get('synthetic');arts={}
 for area in ['lib/lean','ir']:
  stem=R/'.lake/build'/area/n.replace('.','/')
  for f in stem.parent.glob(stem.name+'.*'):
   if f.is_file():arts[str(f.relative_to(R))]=sha(f)
 outputs[n]={'native_key':md['depHash'],'trace_sha256':sha(tr),'artifacts':arts}
run('current8f-complete765',R,['lake','build','--no-build',*sorted(Ctx['graph'])]);roots=['E2E.MixedFlagBoundary.machine_returnW','E2E.ScalarBoundary.machine_returnW','E2E.DivBoundary.machine_returnW','E2E.CfgBoundary.machine_returnW','E2E.backend_correct_world_niX_stock_scalarW','E2E.worldReturnTraceProvider_scalar'];audit=L/'current8f-scalar-models.lean';audit.write_text('import FV.E2E.StockScalarNIW\n\n'+''.join('#print axioms '+n+'\n' for n in roots));run('real-current-audit6',R,['python3',str(P/'scripts/axiom-audit.py'),'--cwd',str(R),'--log-dir',str(L/'audit'),str(audit)]);spec=importlib.util.spec_from_file_location('current8f_axioms',E/'general7-main-candidate-v1/old-axiom-preservation-v1/axiom_records.py');collector=importlib.util.module_from_spec(spec);spec.loader.exec_module(collector);axes={}
for p in (L/'audit').glob('*.log'):
 for n,a in collector.parse_records(p.read_text()):assert n not in axes;axes[n]=sorted(a)
old=json.loads((S/'focused-read-model-scalar-v2/receipt.json').read_text())['axiom_sets'];assert set(axes)==set(roots) and axes==old
for rel,h in unaffected.items():assert sha(R/rel)==h,rel
for c,h in I['configs'].items():assert sha(R/c)==h,c
(L/'receipt.json').write_text(json.dumps({'status':'PASSED_CURRENT8F_SCALAR765_AND_SIX_EXACT_STANDARD_ROOTS','main':main,'source_rebind_manifest_sha256':sha(D/'manifest.json'),'all_R_outputs_before_sha256':sha(L/'all-R-build-before.json'),'current_source_hashes765':new_sources,'graph':Ctx['graph'],'G_reused_providers':copy,'changed_owned_outputs':outputs,'records':records,'axiom_sets':axes,'all_six_prior_sets_exact':True,'validated_and_arithmetic_outputs_unchanged':True,'other_global_affected_importers93':'Not validated by this per-unit gate','full326_reverse_validation':'OPEN'},indent=2)+'\n')
