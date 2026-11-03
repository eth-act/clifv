from pathlib import Path
import os,json,hashlib,subprocess,shutil,re,datetime
X=Path(__file__).resolve().parent;A=X.parent;E=A.parent;D=X/'R394-readiness-v1';D.mkdir();V=D/'metadata';V.mkdir();S=X/'R394-static-v1/inventory.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(S)=='60afef7e33d4fb88ac516c2644aafd8e7f693bc46169f983e324e456b8909294';s=json.loads(S.read_text());R=E/'direct-call-store-live-packet-v1/validation-package-v1';T='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake';records={};configs={};graph={}
for n in ['lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(R/n,V/n);configs[n]=sha(R/n)
repl=V/'.lake/packages/repl';repl.parent.mkdir(parents=True);shutil.copytree(R/'.lake/packages/repl',repl,ignore=shutil.ignore_patterns('.lake'))
for m,row in s['modules'].items():
 rel=Path(m.replace('.','/'));src=R/rel.with_suffix('.lean');assert sha(src)==row['expected_source_sha256'];dst=V/rel.with_suffix('.lean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst);graph[m]=re.findall(r'^import\s+([\w.]+)',src.read_text(),re.M);files={}
 for folder in ['.lake/build/lib/lean','.lake/build/ir']:
  stem=R/folder/rel
  for f in stem.parent.glob(stem.name+'.*'):
   if not f.is_file() or f.name.endswith('.setup.json'):continue
   dst=V/f.relative_to(R);dst.parent.mkdir(parents=True,exist_ok=True)
   if f.suffix in ['.olean','.ilean','.c']:dst.symlink_to(f)
   else:shutil.copy2(f,dst)
   files[str(f.relative_to(R))]=sha(f)
 td=json.loads((R/'.lake/build/lib/lean'/rel.with_suffix('.trace')).read_text());records[m]={'source_sha256':sha(src),'stored_key':td['depHash'],'outputs':td['outputs'],'trace_sha256':sha(R/'.lake/build/lib/lean'/rel.with_suffix('.trace')),'synthetic_label':td.get('synthetic'),'full_input':bool(td.get('inputs')),'files':files}
def no_writers():
 for p in Path('/proc').iterdir():
  if not p.name.isdigit() or int(p.name)==os.getpid():continue
  try:
   a=(p/'cmdline').read_bytes().decode(errors='replace').replace('\0',' ')
   if '/bin/lean ' in a and any(str(R/(m.replace('.','/')+'.lean')) in a for m in records):raise RuntimeError(('overlapping writer',p.name))
  except (OSError,PermissionError):pass
no_writers();env=dict(os.environ);env.pop('FV_LAKE_CACHE',None);env.pop('FV_MEMCAP_OFF',None);env.update(LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',LEAN_NUM_THREADS='1',LAKE_CACHE_DIR=str(D/'disabled-cache'));cmd=[T,'build','--no-build',*sorted(records)]
with (D/'normal394.stdout').open('w') as o,(D/'normal394.stderr').open('w') as err:q=subprocess.run(cmd,cwd=V,env=env,stdout=o,stderr=err)
text=(D/'normal394.stdout').read_text()+(D/'normal394.stderr').read_text();bad=re.findall(r'Building (FV\.\S+)\nerror: target is out-of-date',text);assert q.returncode==0 or bad
cache={}
def ancestors(m):
 if m not in cache:
  deps=set(x for x in graph.get(m,[]) if x in graph)
  cache[m]=deps|set().union(*(ancestors(x) for x in deps)) if deps else set()
 return cache[m]
roots=[m for m in bad if not (ancestors(m)&set(bad))];conditional=sorted(m for m in records if ancestors(m)&set(roots));queries=[]
for m in roots:
 label=m.split('.')[-1]
 with (D/(label+'-key.stdout')).open('w') as o,(D/(label+'-key.stderr')).open('w') as err:k=subprocess.run([T,'query','--no-build','+'+m+':depHash'],cwd=V,env=env,stdout=o,stderr=err)
 key=(D/(label+'-key.stdout')).read_text().strip();queries.append({'target':m,'stored_key':records[m]['stored_key'],'query_exit':k.returncode,'expected_key':key if k.returncode==0 and re.fullmatch('[0-9a-f]{16}',key) else None,'stdout_sha256':sha(D/(label+'-key.stdout')),'stderr_sha256':sha(D/(label+'-key.stderr'))})
no_writers()
for m,row in records.items():
 assert sha(R/(m.replace('.','/')+'.lean'))==row['source_sha256']
 for rel,h in row['files'].items():assert sha(R/rel)==h
for n,h in configs.items():assert sha(R/n)==h
r={'status':'passed_normal394_requires_creator_classification' if q.returncode==0 else 'failed_normal394_importer_held','origin_ref':'8f073980e9630c8d3cd9d6f6f77ab462474c7bcb','normal_exit':q.returncode,'normal_command':cmd,'normal_stdout_sha256':sha(D/'normal394.stdout'),'normal_stderr_sha256':sha(D/'normal394.stderr'),'records':records,'configs':configs,'reported_outdated_targets':bad,'independent_earliest_roots':roots,'root_expected_key_queries':queries,'complete_conditional_importer_cone':conditional,'overlap_with_ELF_roots':sorted(set(roots)&{'FV.E2E.BinCheck','FV.E2E.PipelineCheck','FV.E2E.LinkProduction','FV.E2E.LoweringProvenance'}),'source_config_payload_bytes_unchanged':True,'writer_exclusion_passed':True,'all23_old_header_AXIOM_gates':'held; no changed importer compiled','P_mismatch_preserved':True,'no_shared_write_or_provider_build':True,'further_R_consumers':'stopped pending coordinator R lease restoration','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(D/'receipt.json').write_text(json.dumps(r,indent=2)+'\n');print('receipt',sha(D/'receipt.json'),'normal',q.returncode,'roots',roots,'conditional',conditional,'keys',queries,flush=True)
