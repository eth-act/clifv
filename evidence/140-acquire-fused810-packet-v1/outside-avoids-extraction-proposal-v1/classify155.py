from pathlib import Path
import os,json,hashlib,subprocess,collections,datetime
O=Path(__file__).resolve().parent;A=O.parent;E=A.parent;G=E/'general7-main-candidate-v1';V=O/'light-current8f-query-v1';F=V/'package';S=json.loads((V/'source-only-purpose.json').read_text());P=Path(S['donor']);D=O/'creator-classification155-v1';D.mkdir();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();ref='8f073980e9630c8d3cd9d6f6f77ab462474c7bcb';tool=Path('/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin');env=dict(os.environ);env.pop('FV_LAKE_CACHE',None);env.pop('FV_MEMCAP_OFF',None);env.update(PATH=str(tool)+':'+env['PATH'],LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',LEAN_NUM_THREADS='1')
approvals={
 'actual-compact-cache-provenance-v1':'b1d4a24db9deeee3cadfc284b937362f44515a77acd310e50b0ee700e0a8f42c',
 'actual-compact-cache-provenance-v2':'10dedb6e2efd650193c0564aee87fb487e371dae77fb36e91659eb66e24027f0',
 'full1657-39-archive-provenance-v1':'2e86f6c324388c88a51b2ac2895054a5bcd35367803032c267fe1f16d75ef7b4'}
rs=[]
for n,h in approvals.items():
 p=G/n/'receipt.json';assert sha(p)==h;rs.append((p,json.loads(p.read_text())))
three=A/'no-call-bounded-adapter-readiness-v1/three-synthetic-archive-origin-v1/receipt.json';assert sha(three)=='3001d19371c46ccb4cd219f687e127766b560f6c96b8580ccfacd81044f66c00'
modules=sorted(S['providers']);cmd=[str(tool/'lake'),'query','--no-build',*['+'+m+':depHash' for m in modules]]
q=subprocess.run(cmd,cwd=F,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE);(D/'keys.stdout').write_text(q.stdout);(D/'keys.stderr').write_text(q.stderr);assert q.returncode==0,q.stderr
keys=q.stdout.splitlines();assert len(keys)==len(modules);current=dict(zip(modules,keys));paths=[];traces={}
for m in modules:
 rel=Path(m.replace('.','/'));t=P/'.lake/build/lib/lean'/rel.with_suffix('.trace');td=json.loads(t.read_text());traces[m]=(t,td);assert td['depHash']==current[m]==S['providers'][m]['donor_native_key'];assert td['outputs']==S['providers'][m]['donor_outputs']
 paths.extend(str(P/folder/rel.with_suffix('.'+ext)) for ext,folder in [('olean','.lake/build/lib/lean'),('ilean','.lake/build/lib/lean'),('c','.lake/build/ir')])
 if td.get('inputs') and not td.get('synthetic'):paths.append(str(F/rel.with_suffix('.lean')))
hashEnv=dict(env);hashEnv['LEAN_PATH']=str(tool.parent/'lib/lean');cmdHash=[str(tool/'lean'),'-j1','--run',str(O/'HashNative.lean'),*paths];h=subprocess.run(cmdHash,cwd=O,env=hashEnv,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE);(D/'native-hashes.stdout').write_text(h.stdout);(D/'native-hashes.stderr').write_text(h.stderr);assert h.returncode==0,h.stderr
cold={}
for line in h.stdout.splitlines():
 path,binary,text=line.split('\t');cold[path]={'binary':binary,'text':text}
assert len(cold)==len(set(paths));records={};unmatched=[];counts=collections.Counter();gitCache={}
def git_bytes(head,rel):
 key=(head,rel)
 if key not in gitCache:gitCache[key]=subprocess.check_output(['git','show',head+':'+rel],cwd='/home/lee/clifv')
 return gitCache[key]
for m in modules:
 rel=Path(m.replace('.','/'));t,td=traces[m];source=F/rel.with_suffix('.lean');row={'current_source_sha256':sha(source),'canonical_config_sha256':S['config_hashes']['lakefile.toml'],'current_key':current[m],'trace_sha256':sha(t),'trace_synthetic_label':td.get('synthetic'),'outputs':td['outputs'],'actual_normal155_receipt_sha256':sha(V/'receipt.json'),'current_key_query_sha256':sha(D/'keys.stdout'),'payloads':{},'matched':False}
 assert row['current_source_sha256']==S['providers'][m]['source_sha256']
 expected={'olean':td['outputs']['o'][0].removesuffix('.olean'),'ilean':td['outputs']['i'].removesuffix('.ilean'),'c':td['outputs']['c'].removesuffix('.c')}
 for ext,folder in [('olean','.lake/build/lib/lean'),('ilean','.lake/build/lib/lean'),('c','.lake/build/ir')]:
  p=P/folder/rel.with_suffix('.'+ext);assert cold[str(p)]['binary']==expected[ext],(m,ext,cold[str(p)],expected[ext]);row['payloads'][ext]={'sha256':sha(p),'native_hash_cold':cold[str(p)]['binary']}
 if td.get('inputs') and not td.get('synthetic'):
  row['class']='full_input_native_creator';sourceRows=[v for k,v in td['inputs'] if isinstance(k,str) and k.endswith('/'+str(rel.with_suffix('.lean')))];assert len(sourceRows)==1,(m,sourceRows);assert sourceRows[0]==cold[str(source)]['text'],(m,sourceRows,cold[str(source)])
  logs=[v.get('message','') for v in td.get('log',[])];assert any(str(rel.with_suffix('.lean')) in msg and '/bin/lean ' in msg for msg in logs)
  row.update(creator_trace_inputs_sha256=hashlib.sha256(json.dumps(td['inputs'],sort_keys=True).encode()).hexdigest(),creator_source_native_hash=sourceRows[0],creator_command=logs[0],creator_configuration_sha256=sha(P/'lakefile.toml'),creator_weak_thread_flag='-j2',matched=True)
 else:
  row['class']='compact_archive_derived';found=[]
  for rp,rd in rs:
   rec=rd.get('records',{}).get(str(rel.with_suffix('.lean')))
   if rec and rec.get('matched') and rec.get('native_key')==td['depHash'] and rec.get('outputs')==td['outputs'] and rec['P_trace_sha256']==sha(t):found.append((rp,rec))
  for rp,rec in found:
   match=rec['matched'];assert match['producer_conclusion']=='success';assert all(match['payloads'][ext]['extracted_sha256']==row['payloads'][ext]['sha256'] for ext in expected)
   head=match['producer_head'];creatorSource=git_bytes(head,str(rel.with_suffix('.lean')));assert hashlib.sha256(creatorSource).hexdigest()==sha(source),(m,head,'creator source mismatch')
   row.update(approval_receipt=str(rp),approval_receipt_sha256=sha(rp),creator=match,creator_source_sha256=hashlib.sha256(creatorSource).hexdigest(),creator_git_configuration_sha256=hashlib.sha256(git_bytes(head,'lakefile.toml')).hexdigest(),creator_git_manifest_sha256=hashlib.sha256(git_bytes(head,'lake-manifest.json')).hexdigest(),creator_git_toolchain_sha256=hashlib.sha256(git_bytes(head,'lean-toolchain')).hexdigest(),matched=True);break
 if not row['matched']:unmatched.append({'module':m,'key':current[m],'outputs':td['outputs'],'trace_sha256':sha(t),'class':row['class']})
 counts[row['class']]+=1;records[m]=row
receipt={'status':'complete_classification_requires_coordinator_review' if not unmatched else 'unmatched_creator_hold','records':records,'counts':dict(counts),'unmatched':unmatched,'approved_archive_receipts':approvals,'three_entry3001_receipt_sha256':sha(three),'three_entry3001_applicable_modules':sorted(set(modules)&{x.removesuffix('.lean').replace('/','.') for x in json.loads(three.read_text())['records']}),'current_normal155_receipt_sha256':sha(V/'receipt.json'),'canonical_configuration_sha256':S['config_hashes']['lakefile.toml'],'donor_weak_configuration_sha256':sha(P/'lakefile.toml'),'donor_weak_thread_flag':'-j2','normal_and_all155_expected_key_bindings_passed':True,'cold_native_output_hashes_match_all465_outputs':True,'hash_helper_sha256':sha(O/'HashNative.lean'),'hash_function_source_sha256':sha(tool.parent/'src/lean/lake/Lake/Build/Trace.lean'),'hash_helper_imports_only_toolchain_Lake':True,'new_project_leaf_compilers_started':0,'current8f_leaf_reuse_approved':False,'shared_files_changed':0,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(D/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(dict(counts),'unmatched',unmatched);print('receipt',sha(D/'receipt.json'))
