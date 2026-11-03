from pathlib import Path
import os,json,hashlib,subprocess,shutil,collections,datetime
O=Path(__file__).resolve().parent;A=O.parent;E=A.parent;D=O/'host-R376-v1';D.mkdir();V=D/'metadata';V.mkdir();M=json.loads((O/'manifest.json').read_text());R=E/'direct-call-store-live-packet-v1/validation-package-v1';T=Path('/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();modules=sorted(M['provider_source_hashes']);modulePaths={m.replace('.','/')+'.lean' for m in modules}
def writers():
 found=[]
 for p in Path('/proc').iterdir():
  if not p.name.isdigit() or int(p.name)==os.getpid():continue
  try:
   args=(p/'cmdline').read_bytes().decode(errors='replace').replace('\0',' ')
   if '/bin/lean ' not in args and '/bin/lake ' not in args:continue
   if str(R) not in args:continue
   overlapping=[m for m in modulePaths if str(R/m) in args]
   if overlapping or ('/bin/lake ' in args and any((' '+m+' ' in args+' ') for m in modules)):found.append({'pid':int(p.name),'modules':overlapping,'argv':args})
  except (OSError,PermissionError):pass
 return found
w=writers();(D/'writers-before.json').write_text(json.dumps(w,indent=2)+'\n');assert not w,w
config={};initial={};traces={}
for n in ['lakefile.toml','lake-manifest.json','lean-toolchain']:
 shutil.copy2(R/n,V/n);config[n]=sha(R/n)
repl=V/'.lake/packages/repl';repl.parent.mkdir(parents=True,exist_ok=True);shutil.copytree(R/'.lake/packages/repl',repl,ignore=shutil.ignore_patterns('.lake'))
for m in modules:
 rel=Path(m.replace('.','/'));src=R/rel.with_suffix('.lean');assert sha(src)==M['provider_source_hashes'][m];dst=V/rel.with_suffix('.lean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
 for folder in ['.lake/build/lib/lean','.lake/build/ir']:
  stem=R/folder/rel
  for f in stem.parent.glob(stem.name+'.*'):
   if not f.is_file() or f.name.endswith('.setup.json'):continue
   dst=V/f.relative_to(R);dst.parent.mkdir(parents=True,exist_ok=True)
   if f.suffix in ['.olean','.ilean','.c']:dst.symlink_to(f)
   else:shutil.copy2(f,dst)
   initial[str(f.relative_to(R))]=sha(f)
 trace=R/'.lake/build/lib/lean'/rel.with_suffix('.trace');traces[m]=json.loads(trace.read_text())
env=dict(os.environ);env.pop('FV_LAKE_CACHE',None);env.pop('FV_MEMCAP_OFF',None);env.update(PATH=str(T)+':'+env['PATH'],LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LAKE_CACHE_DIR=str(D/'disabled-cache'),OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',LEAN_NUM_THREADS='1')
commands=[]
def run(label,args,extra=None):
 e=dict(env);e.update(extra or {})
 with (D/(label+'.stdout')).open('w') as out,(D/(label+'.stderr')).open('w') as err:q=subprocess.run(args,cwd=V,env=e,stdout=out,stderr=err)
 commands.append({'label':label,'argv':args,'exit':q.returncode,'stdout_sha256':sha(D/(label+'.stdout')),'stderr_sha256':sha(D/(label+'.stderr'))});print(label,q.returncode,flush=True);assert q.returncode==0,label
 return (D/(label+'.stdout')).read_text().splitlines()
run('normal376',[str(T/'lake'),'build','--no-build',*modules]);keys=run('keys376',[str(T/'lake'),'query','--no-build',*['+'+m+':depHash' for m in modules]]);assert len(keys)==376
for m,key in zip(modules,keys):assert key==traces[m]['depHash'],(m,key,traces[m]['depHash'])
paths=[]
for m in modules:
 rel=Path(m.replace('.','/'))
 for ext,folder in [('olean','.lake/build/lib/lean'),('ilean','.lake/build/lib/lean'),('c','.lake/build/ir')]:paths.append(str(R/folder/rel.with_suffix('.'+ext)))
 if traces[m].get('inputs'):paths.append(str(V/rel.with_suffix('.lean')))
helper=A/'outside-avoids-extraction-proposal-v1/HashNative.lean';coldRows=run('cold-native-hashes',[str(T/'lean'),'-j1','--run',str(helper),*paths],{'LEAN_PATH':str(T.parent/'lib/lean')});cold={}
for line in coldRows:
 p,b,t=line.split('\t');cold[p]={'binary':b,'text':t}
G=E/'general7-main-candidate-v1';approvals={'actual-compact-cache-provenance-v1':'b1d4a24db9deeee3cadfc284b937362f44515a77acd310e50b0ee700e0a8f42c','actual-compact-cache-provenance-v2':'10dedb6e2efd650193c0564aee87fb487e371dae77fb36e91659eb66e24027f0','full1657-39-archive-provenance-v1':'2e86f6c324388c88a51b2ac2895054a5bcd35367803032c267fe1f16d75ef7b4','direct33-baseline21-archive-provenance-v1':'47e1a8dbaf303a6ac00956b22153be6c94ef4a8c2ff46fa7048844b82041f9b5','NI-nine-archive-provenance-v1':'b7c04aeeb54e3468dbc34b44452a50d1f430cbe855dd3fb968680215eb6ae223'};approvalRows=[]
for name,h in approvals.items():
 p=G/name/'receipt.json';assert sha(p)==h;approvalRows.append((p,json.loads(p.read_text())))
three=A/'no-call-bounded-adapter-readiness-v1/three-synthetic-archive-origin-v1/receipt.json';assert sha(three)=='3001d19371c46ccb4cd219f687e127766b560f6c96b8580ccfacd81044f66c00';approvalRows.append((three,json.loads(three.read_text())))
records={};unmatched=[];counts=collections.Counter()
for m,key in zip(modules,keys):
 rel=Path(m.replace('.','/'));td=traces[m];trace=R/'.lake/build/lib/lean'/rel.with_suffix('.trace');outputs=td['outputs'];row={'source_sha256':M['provider_source_hashes'][m],'current_key':key,'trace_sha256':sha(trace),'synthetic_label':td.get('synthetic'),'outputs':outputs,'payloads':{},'supported':False}
 expected={'olean':outputs['o'][0].removesuffix('.olean'),'ilean':outputs['i'].removesuffix('.ilean'),'c':outputs['c'].removesuffix('.c')}
 for ext,folder in [('olean','.lake/build/lib/lean'),('ilean','.lake/build/lib/lean'),('c','.lake/build/ir')]:
  p=R/folder/rel.with_suffix('.'+ext);assert cold[str(p)]['binary']==expected[ext],(m,ext);row['payloads'][ext]={'sha256':sha(p),'cold_native_hash':expected[ext]}
 if td.get('inputs') and not td.get('synthetic'):
  row['class']='full_input_native_creator';src=[v for k,v in td['inputs'] if isinstance(k,str) and k.endswith('/'+str(rel.with_suffix('.lean')))];assert len(src)==1 and src[0]==cold[str(V/rel.with_suffix('.lean'))]['text'],m
  logs=[v.get('message','') for v in td.get('log',[])];cmd=[x for x in logs if str(rel.with_suffix('.lean')) in x and '/bin/lean ' in x];assert cmd,m
  row.update(supported=True,creator_command=cmd[0],creator_inputs=td['inputs'],creator_inputs_sha256=hashlib.sha256(json.dumps(td['inputs'],sort_keys=True).encode()).hexdigest(),creator_configuration_binding='native full-input trace and exact logged Lean arguments; current R configuration bound separately')
 else:
  row['class']='compact_archive_derived' if not td.get('synthetic') else 'synthetic_hold'
  if not td.get('synthetic'):
   for p,r in approvalRows:
    rec=r.get('records',{}).get(str(rel.with_suffix('.lean')))
    if not rec or not rec.get('matched') or rec.get('native_key')!=key or rec.get('outputs')!=outputs or rec.get('P_trace_sha256')!=sha(trace):continue
    match=rec['matched'];assert match['producer_conclusion']=='success';assert all(match['payloads'][ext]['extracted_sha256']==row['payloads'][ext]['sha256'] for ext in expected)
    source=subprocess.check_output(['git','show',match['producer_head']+':'+str(rel.with_suffix('.lean'))]);assert hashlib.sha256(source).hexdigest()==row['source_sha256'];row.update(supported=True,approval_receipt=str(p),approval_receipt_sha256=sha(p),creator=match);break
 if not row['supported']:unmatched.append({'module':m,'key':key,'class':row['class'],'trace_sha256':sha(trace),'outputs':outputs})
 records[m]=row;counts[row['class']]+=1
w=writers();assert not w,w
for rel,h in initial.items():assert sha(R/rel)==h,('R output changed',rel)
for m,h in M['provider_source_hashes'].items():assert sha(R/(m.replace('.','/')+'.lean'))==h
for n,h in config.items():assert sha(R/n)==h
receipt={'status':'passed_exact_read_only_host376' if not unmatched else 'unmatched_creator_hold_stop_before_leaf','source_manifest_sha256':sha(O/'manifest.json'),'configuration_hashes':config,'records':records,'counts':dict(counts),'unmatched':unmatched,'normal_and_keys_passed':True,'cold_output_hashes_checked':1128,'creator_approvals':approvals,'commands':commands,'R_sources_configs_outputs_unchanged':True,'writer_exclusion_before_and_after':True,'shared_writes':False,'project_compilers_started':0,'new_leaf_started':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(D/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print('receipt',sha(D/'receipt.json'),dict(counts),'unmatched',unmatched,flush=True);assert not unmatched,'Stop before raw leaf: creator receipt needed'
