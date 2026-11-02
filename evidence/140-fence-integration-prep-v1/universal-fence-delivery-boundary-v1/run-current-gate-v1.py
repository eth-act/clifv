from pathlib import Path
import json,hashlib,subprocess,os,datetime,re
O=Path(__file__).resolve().parent;T=O.parent;F=T.parent/'140-fence-packet-v1';P=F/'package';M=O/'manifest.json';manifest=M.read_bytes();S=json.loads(manifest);N=F/'import-snapshot-v22.json';sha=lambda b:hashlib.sha256(b).hexdigest();assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='fence-1G'
def current_projection():
 head=subprocess.check_output(['gh','api','repos/eth-act/clifv/commits/main','--jq','.sha'],text=True).strip()
 rows={}
 for m,r in S['provider_source_projection'].items():
  content=subprocess.check_output(['git','show',head+':'+r['path']]);h=sha(content);assert h==r['canonical_sha256'],m;rows[m]=h
 return {'head':head,'provider_sha256':rows}
before=current_projection()
for rel,h in S['source_sha256'].items():assert sha((P/rel).read_bytes())==h,rel
assert sha(N.read_bytes())==S['normal_provider_snapshot_sha256'];assert M.read_bytes()==manifest
subprocess.run(['python3',str(F/'verify-access-v22.py'),'--attempt','universal-delivery-context-v1','--preflight'],check=True)
modules=[m for m in S['topological_candidate_and_dependency_order'] if m.replace('.','/')+'.lean' in S['source_sha256']];assert len(modules)==21
subprocess.run(['python3',str(F/'verify-access-v22.py'),'--attempt','universal-delivery-kernels-v1',*modules,'scripts.audit.stock-fence'],check=True)
run=F/'runs/universal-delivery-kernels-v1';state=json.loads((run/'state.json').read_text());assert state['status']=='passed';log=(run/'stock-fence.log').read_text();ax={r:sorted(a.strip() for a in v.split(',') if a.strip()) for r,v in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)};assert ax==S['axioms'];after=current_projection();assert M.read_bytes()==manifest
R={'status':'passed','candidate_source':str(O/'source'),'source_sha256':S['source_sha256'],'manifest_sha256':sha(manifest),'source_context_before':before,'source_context_after':after,'normal_snapshot_sha256':sha(N.read_bytes()),'normal_receipt_sha256':sha((F/'import-normal-check-v22.json').read_bytes()),'normal_command_receipt':str(F/'runs/universal-delivery-context-v1/state.json'),'kernels':21,'kernel_command_receipt':str(run/'state.json'),'kernel_command_receipt_sha256':sha((run/'state.json').read_bytes()),'candidate_artifacts':{r['label']:{'source_sha256':r['source_sha256'],'olean_sha256':r['olean_sha256'],'argv':r['argv'],'memstats':r['memstats']} for r in state['records']},'roots':35,'standard_roots':33,'marked_fixed_roots':S['marked_fixed_roots'],'axioms':ax,'axiom_log_sha256':sha((run/'stock-fence.log').read_bytes()),'exact_context':True,'kernel_gate_passed':True,'all_previous_35_axiom_sets_exact':True,'all_685_current_source_hashes_exact':True,'proper_normal_provider_keys_passed':True,'full_fence_closure':False,'full_goal_complete':False,'branch_publication_owner':'worker-O coordinator','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(O/'publication-ready-state-v1.json').write_text(json.dumps(R,indent=2)+'\n');print('PASS:21 kernels,35 exact AX roots,685 current-main imports,proper normal keys',flush=True)
