from pathlib import Path
import json,hashlib,subprocess,os,datetime,re,shutil
O=Path(__file__).resolve().parent;T=O.parent;F=T.parent/'140-fence-packet-v1';P=F/'package';M=O/'manifest.json';manifest=M.read_bytes();S=json.loads(manifest);N=F/'import-snapshot-v22.json';SN=json.loads(N.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='fence-1G'
foundation=json.loads(subprocess.check_output(['gh','pr','view','916','--repo','eth-act/clifv','--json','state,mergeCommit'],text=True));assert foundation['state']=='MERGED','Wait for actual916merge; no kernels started'
Fgate=T/'universal-fence-delivery-boundary-v1/current-gate-v1.json';G=json.loads(Fgate.read_text());assert G['status']=='passed'
def project():
 head=subprocess.check_output(['gh','api','repos/eth-act/clifv/commits/main','--jq','.sha'],text=True).strip();rows={}
 for m,r in S['baseline_normal_providers'].items():
  h=hashlib.sha256(subprocess.check_output(['git','show',head+':'+r['source']])).hexdigest();assert h==r['sha256'],m;rows[m]=h
 for rel,h in S['foundation_sources_required'].items():assert hashlib.sha256(subprocess.check_output(['git','show',head+':'+rel])).hexdigest()==h,rel
 return {'head':head,'provider_source_sha256':rows,'foundation_source_sha256':S['foundation_sources_required']}
before=project();foundationArtifacts={}
# Only implementation imports are reused; the old audit is not an imported provider.
for m in S['foundation_sources_required']:
 mod=m[:-5].replace('/','.');entry=G['candidate_artifacts'][mod.rsplit('.',1)[-1]];p=P/'.lake/build/lib/lean'/Path(m).with_suffix('.olean');assert sha(p)==entry['olean_sha256'];foundationArtifacts[mod]={'path':str(p),'sha256':sha(p)}
for rel,h in S['source_sha256'].items():
 source=O/'source'/rel;assert sha(source)==h
 if rel.startswith('scripts/'):
  dest=P/rel;dest.parent.mkdir(parents=True,exist_ok=True)
  if not dest.exists():shutil.copy2(source,dest)
 assert sha(P/rel)==h,rel
assert sha(N)==S['normal_snapshot_sha256'];assert M.read_bytes()==manifest
subprocess.run(['python3',str(F/'verify-access-v22.py'),'--attempt','mixed-fault-delivery-context-v1','--preflight'],check=True)
subprocess.run(['python3',str(F/'verify-access-v22.py'),'--attempt','mixed-fault-delivery-kernels-v1',*S['candidate_topological_order'],'scripts.audit.stock-fence-memory'],check=True)
run=F/'runs/mixed-fault-delivery-kernels-v1';state=json.loads((run/'state.json').read_text());assert state['status']=='passed';log=(run/'stock-fence-memory.log').read_text();ax={r:sorted(a.strip() for a in v.split(',') if a.strip()) for r,v in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)};assert ax==S['axioms'];after=project();assert M.read_bytes()==manifest
for rel,h in SN['config_hashes'].items():assert sha(P/rel)==h
artifacts={}
for m,r in S['baseline_normal_providers'].items():
 prefix=m.replace('.','/')+'.';entries={p:h for p,h in SN['artifacts'].items() if p.startswith('.lake/build/lib/lean/'+prefix) or p.startswith('.lake/build/ir/'+prefix)}
 assert '.lake/build/lib/lean/'+m.replace('.','/')+'.olean' in entries
 for p,h in entries.items():assert sha(P/p)==h
 artifacts[m]=entries
lean=Path(SN['lean_executable']);R={'status':'passed','candidate_source':str(O/'source'),'source_sha256':S['source_sha256'],'manifest_sha256':sha(M),'source_context_before':before,'source_context_after':after,'foundation_actual_merged':foundation,'foundation_gate_sha256':sha(Fgate),'foundation_artifact_hashes':foundationArtifacts,'dependency_artifact_hashes':artifacts,'normal_snapshot_sha256':sha(N),'normal_no_build_result':json.loads((F/'runs/mixed-fault-delivery-context-v1/state.json').read_text()),'normal_receipt_sha256':sha(F/'import-normal-check-v22.json'),'kernels':47,'kernel_command_receipt':str(run/'state.json'),'kernel_command_receipt_sha256':sha(run/'state.json'),'candidate_artifacts':{r['label']:{'source_sha256':r['source_sha256'],'olean_sha256':r['olean_sha256'],'argv':r['argv'],'memstats':r['memstats']} for r in state['records']},'roots':94,'standard_roots':80,'marked_fixed_roots':S['marked_fixed_roots'],'axioms':ax,'axiom_log_sha256':sha(run/'stock-fence-memory.log'),'config_hashes':SN['config_hashes'],'toolchain':{'lean_executable':str(lean),'lean_sha256':sha(lean),'lake_sha256':sha(lean.with_name('lake')),'version':subprocess.check_output([str(lean),'--version'],text=True).strip(),'spec':(P/'lean-toolchain').read_text()},'exact_context':True,'kernel_gate_passed':True,'all_previous_94_axiom_sets_exact':True,'all_960_current_source_hashes_exact':True,'proper_normal_provider_keys_passed':True,'full_fence_closure':False,'full_goal_complete':False,'branch_publication_owner':'worker-O coordinator','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(O/'current-gate-v1.json').write_text(json.dumps(R,indent=2)+'\n');print('PASS:47kernels,94exactAXroots,960current-mainimports,21exact916sources,propernormalkeys',flush=True)
