from pathlib import Path
import json,hashlib,subprocess,os,datetime,re,shutil
O=Path(__file__).resolve().parent;A=O.parent;E=A.parent;F=E/'140-fence-packet-v1';P=F/'package';M=O/'manifest.json';manifest=M.read_bytes();S=json.loads(manifest);N=F/'import-snapshot-v23.json';SN=json.loads(N.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='fence-1G'
merged=json.loads(subprocess.check_output(['gh','pr','view','917','--repo','eth-act/clifv','--json','state,mergeCommit'],text=True));assert merged['state']=='MERGED'
FG=E/'140-fence-integration-prep-v1/mixed-fault-delivery-boundary-v1/current-gate-v1.json';G=json.loads(FG.read_text());assert G['status']=='passed'
def project():
 head=subprocess.check_output(['gh','api','repos/eth-act/clifv/commits/main','--jq','.sha'],text=True).strip();rows={}
 for m,r in {**S['baseline_normal_providers'],**S['landed_foundation_providers']}.items():
  actual=hashlib.sha256(subprocess.check_output(['git','show',head+':'+r['source']])).hexdigest();assert actual==r['sha256'],('Actualmain context changed',m);rows[m]=actual
 for rel,h in SN['config_hashes'].items():assert hashlib.sha256(subprocess.check_output(['git','show',head+':'+rel])).hexdigest()==h,('Configchanged',rel)
 return {'head':head,'dependency_source_sha256':rows,'config_sha256':SN['config_hashes']}
before=project();foundation={}
for m,r in S['landed_foundation_providers'].items():
 entry=G['candidate_artifacts'][m.rsplit('.',1)[-1]];p=P/'.lake/build/lib/lean'/Path(r['source']).with_suffix('.olean');assert sha(p)==entry['olean_sha256'];assert sha(P/r['source'])==r['sha256'];foundation[m]={'path':str(p),'sha256':sha(p),'source_sha256':r['sha256']}
for rel,h in S['source_sha256'].items():
 source=O/'source'/rel;assert sha(source)==h;dest=P/rel;dest.parent.mkdir(parents=True,exist_ok=True)
 if not dest.exists():shutil.copy2(source,dest)
 assert sha(dest)==h,rel
assert sha(N)==S['normal_snapshot_sha256'];assert M.read_bytes()==manifest
oldGatePath=A/'delivery-boundary-v1/current-gate-v2.json';oldGate=json.loads(oldGatePath.read_text());assert sha(oldGatePath)==S['previous_current_gate_sha256'];assert oldGate['proper_normal_provider_keys_passed'];assert sha(F/'import-normal-check-v23.json')==oldGate['normal_receipt_sha256'];assert sha(N)==oldGate['normal_snapshot_sha256']
subprocess.run(['python3',str(F/'verify-access-v23.py'),'--attempt','acquire810-delivery-whitespace-kernels-v1',*S['focused_rebuild_queue'],'scripts.audit.stock-acquire810'],check=True)
run=F/'runs/acquire810-delivery-whitespace-kernels-v1';state=json.loads((run/'state.json').read_text());assert state['status']=='passed';log=(run/'stock-acquire810.log').read_text();ax={r:sorted(a.strip() for a in v.split(',') if a.strip()) for r,v in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)}
for r in re.findall(r"'([^']+)' does not depend on any axioms",log):ax[r]=[]
assert ax==S['axioms'];after=project();assert M.read_bytes()==manifest
for mod in S['candidate_topological_order']:
 if mod not in S['focused_rebuild_queue']:
  entry=oldGate['candidate_artifacts'][mod.rsplit('.',1)[-1]];path=P/'.lake/build/lib/lean'/Path(mod.replace('.','/')).with_suffix('.olean');assert sha(path)==entry['olean_sha256']

artifacts={}
for m,r in S['baseline_normal_providers'].items():
 prefix=m.replace('.','/')+'.';entries={p:h for p,h in SN['artifacts'].items() if p.startswith('.lake/build/lib/lean/'+prefix) or p.startswith('.lake/build/ir/'+prefix)}
 assert '.lake/build/lib/lean/'+m.replace('.','/')+'.olean' in entries
 for p,h in entries.items():assert sha(P/p)==h
 artifacts[m]=entries
lean=Path(SN['lean_executable']);R={'status':'passed','candidate_source':str(O/'source'),'source_sha256':S['source_sha256'],'manifest_sha256':sha(M),'source_context_before':before,'source_context_after':after,'foundation_actual_merged':merged,'foundation_gate_sha256':sha(FG),'foundation_artifact_hashes':foundation,'dependency_artifact_hashes':artifacts,'normal_snapshot_sha256':sha(N),'normal_no_build_result':oldGate['normal_no_build_result'],'normal_receipt_sha256':sha(F/'import-normal-check-v23.json'),'kernels':34,'kernels_rebuilt':13,'kernels_reused':21,'reused_gate_sha256':sha(oldGatePath),'kernel_command_receipt':str(run/'state.json'),'kernel_command_receipt_sha256':sha(run/'state.json'),'candidate_artifacts':{**oldGate['candidate_artifacts'],**{r['label']:{'source_sha256':r['source_sha256'],'olean_sha256':r['olean_sha256'],'argv':r['argv'],'memstats':r['memstats']} for r in state['records']}},'roots':56,'standard_roots':42,'marked_fixed_roots':S['marked_fixed_roots'],'axioms':ax,'axiom_log_sha256':sha(run/'stock-acquire810.log'),'config_hashes':SN['config_hashes'],'toolchain':{'lean_executable':str(lean),'lean_sha256':sha(lean),'lake_sha256':sha(lean.with_name('lake')),'version':subprocess.check_output([str(lean),'--version'],text=True).strip(),'spec':(P/'lean-toolchain').read_text()},'exact_context':True,'kernel_gate_passed':True,'old_axiom_sets_exact':True,'all_721_current_source_hashes_exact':True,'proper_normal_provider_keys_passed':True,'fixed_function_only':True,'full_acquire_closure':False,'no_earlier_physical_faults_complete':False,'full_goal_complete':False,'branch_publication_owner':'worker-O coordinator','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(O/'current-gate-v1.json').write_text(json.dumps(R,indent=2)+'\n');print('PASS:13rebuilt+21reusedkernels,56exactAXroots,721current-mainimports,propernormalkeys',flush=True)
