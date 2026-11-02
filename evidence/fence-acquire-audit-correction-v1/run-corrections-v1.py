from pathlib import Path
import os,json,hashlib,re,subprocess,shutil,datetime
O=Path(__file__).resolve().parent;E=O.parent;F=E/'140-fence-packet-v1';P=F/'package';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='fence-1G'
SN=json.loads((F/'import-snapshot-v23.json').read_text());units={u:json.loads((O/u/'manifest.json').read_text()) for u in ['917','920']};head=subprocess.check_output(['gh','api','repos/eth-act/clifv/commits/main','--jq','.sha'],text=True).strip()
auditor=O/'tools/scripts/axiom-audit.py';assert auditor.read_bytes()==subprocess.check_output(['git','show',head+':scripts/axiom-audit.py'])
old920=json.loads(Path(units['920']['old_gate']).read_text());projection={}
for m,h in old920['source_context_after']['dependency_source_sha256'].items():
 rel=m.replace('.','/')+'.lean';actual=hashlib.sha256(subprocess.check_output(['git','show',head+':'+rel])).hexdigest();assert actual==h,(m,actual,h);projection[m]=actual
for rel,h in SN['config_hashes'].items():assert sha(P/rel)==h;assert hashlib.sha256(subprocess.check_output(['git','show',head+':'+rel])).hexdigest()==h
for unit,S in units.items():
 oldManifest=json.loads(Path(S['old_manifest']).read_text());oldSource=Path(S['old_source'])
 for rel,h in oldManifest['source_sha256'].items():
  assert sha(oldSource/rel)==h;assert sha(P/rel)==h,(unit,rel,'preserve unexpected prefix work')
  if unit=='917':assert hashlib.sha256(subprocess.check_output(['git','show',head+':'+rel])).hexdigest()==h
 for rel,change in S['changes'].items():
  source=O/unit/'source'/rel;assert sha(source)==change['new_sha256'];(P/rel).write_bytes(source.read_bytes())
 attempt='witness-comment-'+unit+'-kernels-v1'
 subprocess.run(['python3',str(F/'verify-access-v23.py'),'--attempt',attempt,*S['kernel_queue']],check=True)
 (O/unit/'kernel-receipt-link.json').write_text(json.dumps({'receipt':str(F/'runs'/attempt/'state.json'),'sha256':sha(F/'runs'/attempt/'state.json')},indent=2)+'\n')
# These new proof modules were raw-kernel candidates. They were never represented as normal-valid providers.
# The963 normal-key provider source/artifact inputs and v23 config remain unchanged.
for m,row in SN['modules'].items():assert sha(P/row['source'])==row['sha256']
for rel,h in SN['artifacts'].items():assert sha(P/rel)==h
logs=O/'real-auditor-v1';logs.mkdir();env=dict(os.environ);env.pop('FV_LAKE_CACHE',None);env.pop('FV_MEMCAP_OFF',None);real=Path(SN['lean_executable']);env.update(PATH=str(O/'tools/bin')+':'+str(real.parent)+':'+env['PATH'],LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',FV_ROOT=str(P),FV_MEMCAP='1G',FV_MEMCAP_UNIT='worker-o-fence-acquire-real-audit-v1',FV_MEMCAP_STATS=str(logs/'memstats'),LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LAKE_CACHE_DIR=str(F/'disabled-cache'))
files=[P/'scripts/audit/stock-fence-memory.lean',P/'scripts/audit/stock-acquire810.lean'];cmd=['python3',str(auditor),'--cwd',str(P),'--log-dir',str(logs),*[str(p) for p in files]]
with (logs/'stdout.log').open('w') as f:result=subprocess.run(['/home/lee/clifv/.worktrees/stock-extending-production-20261031/scripts/memcap.sh',*cmd],cwd=P,env=env,stdout=f,stderr=subprocess.STDOUT)
summary={'argv':cmd,'exit':result.returncode,'auditor_sha256':sha(auditor),'thread_wrapper_sha256':sha(O/'tools/bin/lake'),'memstats':(logs/'memstats').read_text() if (logs/'memstats').exists() else None,'stdout_sha256':sha(logs/'stdout.log')};(logs/'state.json').write_text(json.dumps(summary,indent=2)+'\n');print((logs/'stdout.log').read_text(),flush=True);assert result.returncode==0,'Inspect real auditor diagnostics before retry'
for unit,file in zip(['917','920'],files):
 S=units[unit];log=logs/(file.stem+'.log');text=log.read_text();ax={n:sorted(x.strip() for x in xs.replace('\n',' ').split(',') if x.strip()) for n,xs in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",text,re.S)}
 for n in re.findall(r"'([^']+)' does not depend on any axioms",text):ax[n]=[]
 assert ax==S['axioms'];markers=set(re.findall(r'^#print axioms\s+(\S+)\s+--\s*witness: native_decide',file.read_text(),re.M));assert markers==set(S['fixed_roots']);oldGate=json.loads(Path(S['old_gate']).read_text());artifacts={}
 for mod in json.loads(Path(S['old_manifest']).read_text())['candidate_topological_order']:
  p=P/'.lake/build/lib/lean'/Path(mod.replace('.','/')).with_suffix('.olean');artifacts[mod]={'source_sha256':sha(P/(mod.replace('.','/')+'.lean')),'olean_sha256':sha(p)}
 receipt={'status':'passed','unit':unit,'candidate_source':str(O/unit/'source'),'manifest_sha256':sha(O/unit/'manifest.json'),'source_hashes':{rel:sha(O/unit/'source'/rel) for rel in S['changes']},'actual_main':head,'current_dependency_source_sha256':projection,'comment_only':True,'headers_bodies_inputs_exact':True,'old_axiom_sets_exact':True,'axioms':ax,'roots':len(ax),'recognized_fixed_roots':sorted(markers),'real_repository_auditor':summary,'real_audit_log':str(log),'real_audit_log_sha256':sha(log),'kernel_receipt':json.loads((O/unit/'kernel-receipt-link.json').read_text()),'all_candidate_artifacts':artifacts,'normal_snapshot_sha256':sha(F/'import-snapshot-v23.json'),'normal_provider_receipt_sha256':sha(F/'import-normal-check-v23.json'),'normal_provider_keys_unchanged':True,'new_normal_candidate_build_claim':False,'full_goal_complete':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(O/unit/'current-gate-v1.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS: separate917/920commentcorrections; actualrepositoryauditor2/2; all150AXsets exact',flush=True)
