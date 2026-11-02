from pathlib import Path
import os,json,hashlib,subprocess,re,time,datetime
O=Path(__file__).resolve().parent;E=O.parent;BASE=Path('/home/lee/clifv');roots=['FV.E2E.RegLevelWrites','FV.E2E.DeadCleanupRealizesW','FV.E2E.DeadCleanupRegLevelW'];prefixes={'broad':E/'892-joint-current-context-v2/package','call_store':E/'direct-call-store-live-packet-v1/validation-package-v1'};C=E/'892-current-main-context-v1/package/.lake/ci-cache';lake='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();head=subprocess.check_output(['gh','api','repos/eth-act/clifv/commits/main','--jq','.sha'],text=True).strip();tree={line.split('\t',1)[1]:line.split()[2] for line in subprocess.check_output(['git','ls-tree','-r',head],cwd=BASE,text=True).splitlines()};state={'status':'read_only_inventory_in_progress','actual_main':head,'roots':roots,'prefixes':{},'no_builds':True,'filesystem_read_only_for_lake':True,'no_scheduler_signal':True,'no_promotion':True};records=[]
def save():
 state['commands']=records;state['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();(O/'state.json').write_text(json.dumps(state,indent=2)+'\n')
for label,P in prefixes.items():
 graph={};sources={}
 def visit(m):
  if m in graph:return
  p=P/(m.replace('.','/')+'.lean')
  if not p.is_file():return
  data=p.read_bytes();text=data.decode();graph[m]=[];blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest();rel=str(p.relative_to(P));sources[m]={'source':rel,'sha256':hashlib.sha256(data).hexdigest(),'git_blob':blob,'actual_main_blob':tree.get(rel),'actual_main_exact':tree.get(rel)==blob}
  for line in text.splitlines():
   mt=re.match(r'^(?:(?:public|private|meta) +)*import +(.+)$',line)
   if mt:
    for dep in mt.group(1).split('--',1)[0].split():
     if (P/(dep.replace('.','/')+'.lean')).is_file():graph[m].append(dep);visit(dep)
 for m in roots:visit(m)
 rows={};missing=[]
 for m in sorted(graph):
  stem=P/'.lake/build/lib/lean'/Path(m.replace('.','/'));o=stem.with_suffix('.olean');t=stem.with_suffix('.trace');row={'olean_exists':o.is_file(),'trace_exists':t.is_file(),'source':sources[m]}
  if not o.is_file():missing.append(m)
  if t.is_file():
   try:
    before=t.stat();raw=t.read_bytes();after=t.stat();assert (before.st_ino,before.st_size,before.st_mtime_ns)==(after.st_ino,after.st_size,after.st_mtime_ns);trace=json.loads(raw);row.update(saved_depHash=trace.get('depHash'),saved_outputs=trace.get('outputs'),trace_sha256=hashlib.sha256(raw).hexdigest())
   except (OSError,ValueError,AssertionError):row['trace_status']='not_stable_or_readable; no validity claim'
  rows[m]=row
 missingSet=set(missing)
 def blocked(m,seen=None):
  seen=set() if seen is None else seen
  if m in seen:return False
  seen.add(m)
  return m in missingSet or any(blocked(d,seen) for d in graph[m])
 ready=[m for m in graph if not blocked(m)];configs={}
 for rel in ['lakefile.toml','lake-manifest.json','lean-toolchain']:
  data=(P/rel).read_bytes();actual=subprocess.check_output(['git','show',head+':'+rel],cwd=BASE);configs[rel]={'sha256':hashlib.sha256(data).hexdigest(),'actual_main_sha256':hashlib.sha256(actual).hexdigest(),'exact':data==actual,'only_weak_thread_difference':data.replace(b'weakLeanArgs = ["-j2",',b'weakLeanArgs = [').replace(b'weakLeanArgs = ["-j1",',b'weakLeanArgs = [')==actual}
 state['prefixes'][label]={'path':str(P),'project_closure_count':len(graph),'providers':rows,'graph':graph,'configs':configs,'complete_missing_output_closure':missing,'source_mismatches':[m for m,r in sources.items()if not r['actual_main_exact']],'dependency_targets':sorted(set(graph)-set(roots)),'ready_present_targets':sorted(ready),'missing_ready_leaves':[m for m in missing if all(d not in missingSet for d in graph[m])],'saved_keys_are_not_current_validity_claims':True};save()
profilePaths=[E/'892-joint-current-context-v2/package/scripts/lake-module-peaks.tsv',E/'892-joint-current-context-v2/package/.lake/lake-module-peaks.tsv'];peaks={}
for p in profilePaths:
 if p.exists():
  for line in p.read_text().splitlines():
   items=line.split('\t')
   if len(items)>=3 and items[0] in set().union(*(set(x['providers'])for x in state['prefixes'].values())):
    try:mb=float(items[1]);seconds=float(items[2])
    except ValueError:continue
    if items[0] not in peaks or mb>peaks[items[0]]['peak_MiB']:peaks[items[0]]={'peak_MiB':mb,'seconds':seconds,'profile':str(p),'profile_sha256':sha(p),'kind':'recorded profile; not a current measurement'}
state['known_recorded_profiles']=peaks;save()
for label,P in prefixes.items():
 row=state['prefixes'][label];commands=[('deps',['build','--no-build',*row['dependency_targets']]),('ready',['build','--no-build',*row['ready_present_targets']])]+[(m.rsplit('.',1)[-1],['query','--json','--no-build','+'+m+':depHash'])for m in roots]
 for name,args in commands:
  env=dict(os.environ)
  for key in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH']:env.pop(key,None)
  log=O/(label+'-'+name);env.update(FV_ROOT=str(P),FV_MEMCAP='1G',FV_MEMCAP_UNIT='worker-o-w-ready-'+label.replace('_','-')+'-'+name.lower(),FV_MEMCAP_STATS=str(log)+'.mem',LAKE_CACHE_DIR=str(C),LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',PYTHONDONTWRITEBYTECODE='1')
  cmd=['/usr/bin/bwrap','--ro-bind','/','/','--proc','/proc','--dev','/dev','--chdir',str(P),'--',lake,*args];start=time.time()
  with Path(str(log)+'.stdout').open('w') as out,Path(str(log)+'.stderr').open('w') as err:r=subprocess.run(['/home/lee/clifv/.worktrees/stock-extending-production-20261031/scripts/memcap.sh',*cmd],cwd=BASE,env=env,stdout=out,stderr=err)
  record={'prefix':label,'name':name,'argv':cmd,'exit':r.returncode,'seconds':time.time()-start,'memstats':Path(str(log)+'.mem').read_text()if Path(str(log)+'.mem').exists()else None,'stdout_sha256':sha(Path(str(log)+'.stdout')),'stderr_sha256':sha(Path(str(log)+'.stderr'))}
  if args[0]=='query' and r.returncode==0:
   key=json.loads(Path(str(log)+'.stdout').read_text());mapping=C/'outputs/fv'/(key+'.json');record.update(current_normal_input_key=key,mapping_available=mapping.is_file())
   if mapping.is_file():
    raw=mapping.read_bytes();meta=json.loads(raw);archive=C/'artifacts'/meta['data'];record.update(mapping=str(mapping),mapping_sha256=hashlib.sha256(raw).hexdigest(),mapping_data=meta,archive_available=archive.is_file())
  records.append(record);save();print(label,name,'exit',r.returncode,flush=True)
  if r.returncode in [137,-9]:state['status']='stopped_at_measured_metadata_cap';save();raise SystemExit(1)
state['status']='read_only_readiness_complete';save();print(json.dumps({k:{'closure':v['project_closure_count'],'missing':len(v['complete_missing_output_closure']),'source_mismatches':len(v['source_mismatches'])}for k,v in state['prefixes'].items()}),flush=True)
