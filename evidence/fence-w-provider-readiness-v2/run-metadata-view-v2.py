from pathlib import Path
import os,json,hashlib,subprocess,re,time,datetime,shutil,psutil
O=Path(__file__).resolve().parent;E=O.parent;old=json.loads((O/'state.json').read_text());out=O/'metadata-view-attempt-v2';out.mkdir();roots=old['roots'];graph=old['prefixes']['broad']['graph'];prefixes={'broad':E/'892-joint-current-context-v2/package','call_store':E/'direct-call-store-live-packet-v1/validation-package-v1'};C=E/'892-current-main-context-v1/package/.lake/ci-cache';lake='/home/lee/.elan/toolchains/leanprover--lean4.34.1/bin/lake';lake='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake';records=[];report={'status':'read_only_originals_metadata_view_running','prior_failed_read_only_state_sha256':hashlib.sha256((O/'state.json').read_bytes()).hexdigest(),'actual_main':old['actual_main'],'views':{},'commands':records,'no_provider_builds':True,'no_lean_compiler':True,'only_owned_missing_hash_sidecars_writable':True}
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while data:=f.read(1048576):h.update(data)
 return h.hexdigest()
def save():
 report['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();(out/'state.json').write_text(json.dumps(report,indent=2)+'\n')
required={str(P/(m.replace('.','/')+'.lean')) for P in prefixes.values()for m in graph}
active=[]
for p in psutil.process_iter(['pid','name','cmdline']):
 try:
  if p.info['name']=='lean' and any(x in required for x in (p.info['cmdline']or[])):active.append(p.pid)
 except (psutil.NoSuchProcess,psutil.AccessDenied):pass
assert not active,('No snapshot of an active provider writer',active)
try:
 for label,original in prefixes.items():
  view=out/('view-'+label);view.mkdir();(view/'.lake/build/lib/lean').mkdir(parents=True);(view/'.lake/build/ir').mkdir(parents=True);(view/'.lake/packages').symlink_to(original/'.lake/packages',target_is_directory=True);writable=[];copied=[];missingSources=[];missingOutputs=[];providerRows={}
  for rel in ['lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(original/rel,view/rel)
  for mod in sorted(graph):
   rel=Path(mod.replace('.','/')+'.lean');src=original/rel
   if not src.is_file():src=prefixes['broad']/rel;missingSources.append(mod)
   assert sha(src)==old['prefixes']['broad']['providers'][mod]['source']['sha256'],('Required actual source differs',label,mod)
   dest=view/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dest)
   row={'source_sha256':sha(dest),'source_was_missing':mod in missingSources,'outputs':{}}
   for kind in ['lib/lean','ir']:
    stem=original/'.lake/build'/kind/Path(mod.replace('.','/'));target=view/'.lake/build'/kind/Path(mod.replace('.','/'));target.parent.mkdir(parents=True,exist_ok=True)
    for p in stem.parent.glob(stem.name+'.*'):
     if not p.is_file():continue
     dest=target.parent/p.name
     if p.name.endswith(('.trace','.hash','.setup.json')):shutil.copy2(p,dest)
     else:os.link(p,dest)
     copied.append(str(dest.relative_to(view)))
     if not p.name.endswith(('.trace','.hash','.setup.json')):
      side=Path(str(dest)+'.hash')
      if not Path(str(p)+'.hash').exists():side.write_text('');writable.append(side)
     row['outputs'][str(dest.relative_to(view))]={'source_path':str(p),'size':p.stat().st_size}
   if not (view/'.lake/build/lib/lean'/Path(mod.replace('.','/')).with_suffix('.olean')).exists():missingOutputs.append(mod)
   trace=view/'.lake/build/lib/lean'/Path(mod.replace('.','/')).with_suffix('.trace')
   if trace.is_file():
    t=json.loads(trace.read_text());row.update(saved_input_key=t.get('depHash'),saved_outputs=t.get('outputs'),trace_sha256=sha(trace))
   providerRows[mod]=row
  writable=list(dict.fromkeys(writable));writableSet={str(p.relative_to(view))for p in writable};before={str(p.relative_to(view)):sha(p) for p in view.rglob('*')if p.is_file() and not p.is_symlink() and not str(p.relative_to(view)).startswith('.lake/packages/')};missingSet=set(missingOutputs)
  def blocked(m,seen=None):
   seen=set()if seen is None else seen
   if m in seen:return False
   seen.add(m);return m in missingSet or any(blocked(d,seen)for d in graph[m])
  ready=[m for m in graph if not blocked(m)];report['views'][label]={'original':str(original),'temporary_view':str(view),'sources_missing_from_original':missingSources,'missing_output_closure':missingOutputs,'source_count':len(graph),'source_hashes':{m:r['source_sha256']for m,r in providerRows.items()},'providers':providerRows,'writable_missing_hash_sidecars':sorted(writableSet),'normal_ready_targets':sorted(ready),'source_config_provenance':old['prefixes'][label]['configs']};save()
  commands=[('dependencies',['build','--no-build',*sorted(set(graph)-set(roots))]),('present-ready',['build','--no-build',*sorted(ready)])]+[(m.rsplit('.',1)[-1],['query','--json','--no-build','+'+m+':depHash'])for m in roots]
  for name,args in commands:
   env=dict(os.environ)
   for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH']:env.pop(k,None)
   log=out/(label+'-'+name);env.update(FV_ROOT=str(view),FV_MEMCAP='1G',FV_MEMCAP_UNIT='worker-o-w-meta-'+label.replace('_','-')+'-'+name.lower(),FV_MEMCAP_STATS=str(log)+'.mem',LAKE_CACHE_DIR=str(C),LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',PYTHONDONTWRITEBYTECODE='1');cmd=['/usr/bin/bwrap','--ro-bind','/','/','--proc','/proc','--dev','/dev']
   for p in writable:cmd+=['--bind',str(p),str(p)]
   cmd+=['--chdir',str(view),'--',lake,*args];start=time.time()
   with Path(str(log)+'.stdout').open('w')as stdout,Path(str(log)+'.stderr').open('w')as stderr:r=subprocess.run(['/home/lee/clifv/.worktrees/stock-extending-production-20261031/scripts/memcap.sh',*cmd],env=env,stdout=stdout,stderr=stderr)
   rec={'prefix':label,'name':name,'lake_argv':[lake,*args],'sandbox_argv_sha256':hashlib.sha256(json.dumps(cmd).encode()).hexdigest(),'exit':r.returncode,'seconds':time.time()-start,'memstats':Path(str(log)+'.mem').read_text()if Path(str(log)+'.mem').exists()else None,'stdout_sha256':sha(Path(str(log)+'.stdout')),'stderr_sha256':sha(Path(str(log)+'.stderr'))}
   if args[0]=='query'and r.returncode==0:
    key=json.loads(Path(str(log)+'.stdout').read_text());mp=C/'outputs/fv'/(key+'.json');rec.update(current_normal_input_key=key,mapping_available=mp.is_file())
    if mp.is_file():
     raw=mp.read_bytes();mapping=json.loads(raw);archive=C/'artifacts'/mapping['data'];rec.update(mapping_path=str(mp),mapping_sha256=hashlib.sha256(raw).hexdigest(),mapping=mapping,archive_available=archive.is_file())
   records.append(rec);save();print(label,name,r.returncode,flush=True)
   if r.returncode in [137,-9]:raise RuntimeError('Measured metadata cap failure; stop without retry')
  after={str(p.relative_to(view)):sha(p)for p in view.rglob('*')if p.is_file()and not p.is_symlink()and not str(p.relative_to(view)).startswith('.lake/packages/')};assert set(after)==set(before);changed={k:{'before':before[k],'after':after[k]}for k in before if before[k]!=after[k]};assert set(changed)<=writableSet;report['views'][label]['changed_owned_hash_sidecars']=changed;report['views'][label]['all_other_snapshot_files_exact']=True;save()
 report['status']='completed_read_only_originals_exact_queries';save()
finally:
 for label in prefixes:
  view=out/('view-'+label)
  if view.exists():shutil.rmtree(view)
 report['temporary_metadata_views_removed']=True;save()
