from pathlib import Path
import os,json,subprocess,hashlib,re,shutil,datetime
O=Path(__file__).resolve().parent;A=O.parent;E=A.parent;F=E/'140-fence-packet-v1';P=F/'package';R=E/'fence-acquire-audit-correction-v1';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='fence-1G'
logs=O/'logs';logs.mkdir(exist_ok=True);env=dict(os.environ);env.pop('FV_LAKE_CACHE',None);env.pop('FV_MEMCAP_OFF',None);tool='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin';env.update(PATH=str(R/'tools/bin')+':'+tool+':'+env['PATH'],LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',FV_ROOT=str(P),FV_MEMCAP='1G',FV_MEMCAP_UNIT='worker-o-acquire-two-load-pending-fence-paired-frontier-real-audit-v102',FV_MEMCAP_STATS=str(logs/'memstats'),LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LAKE_CACHE_DIR=str(F/'disabled-cache'))
auditor=R/'tools/scripts/axiom-audit.py';audit=P/'scripts/audit/stock-acquire-metadata.lean';cmd=['python3',str(auditor),'--cwd',str(P),'--log-dir',str(logs),str(audit)]
with (logs/'stdout.log').open('w') as out:r=subprocess.run(['/home/lee/clifv/.worktrees/stock-extending-production-20261031/scripts/memcap.sh',*cmd],cwd=P,env=env,stdout=out,stderr=subprocess.STDOUT)
print((logs/'stdout.log').read_text(),flush=True);assert r.returncode==0
text=(logs/'stock-acquire-metadata.log').read_text()
ax={n:sorted(x.strip() for x in xs.replace('\n',' ').split(',') if x.strip()) for n,xs in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",text,re.S)}
ax.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",text)})
assert len(ax)==829,len(ax)
fixed={'Backend.Stock.Proof.AcquireTwoLoadPrefix.original_two_load_schedule','Backend.Stock.Proof.AcquireTwoLoadPrefix.original_two_load_virtual_prefix','Backend.Stock.Proof.AcquireTwoLoadPrefix.original_two_load_acquire_boundary','Backend.Stock.Proof.AcquireTwoLoadPrefix.original_two_load_prepared_machine_fault','Backend.Stock.Proof.AcquireTwoLoadPrefix.original_two_load_execution_witness','Backend.Stock.Proof.AcquireTwoLoadPrefix.original_two_load_whole_source_machine_fault','E2E.backend_correct_worldX_stock_two_load_acquire_faultW','Backend.Stock.Proof.AcquireTwoLoadPrefix.original_returned_runOkABI','E2E.backend_correct_worldX_stock_two_load_acquire_returnW'}
fixed.update({'Backend.Stock.Proof.AcquireTwoLoadPrefix.original_returned_paired_runOkABI', 'Backend.Stock.Proof.AcquireTwoLoadPrefix.original_returned_seeded_runOkABI', 'E2E.backend_correct_worldX_ni_stock_two_load_acquire_returnW', 'Backend.Stock.Proof.AcquireTwoLoadPrefix.original_returned_seeded_paired_runOkABI'})
fixed.update({'E2E.LinkSys.two_load_runGoodB_of_traceW','E2E.LinkSys.two_load_public_fault_runGoodBW'})
fixed.update({'E2E.LinkSys.two_load_public_return_runGoodBW','E2E.LinkSys.two_load_public_return_runGoodLW'})
fixed.add('E2E.StockAcquirePending.two_load_actEntry_keep')
fixed.update(['E2E.StockAcquirePending.two_load_compiled_no_hooks', 'E2E.StockAcquirePending.two_load_goodAtW_stepF_eq_mach', 'E2E.StockAcquirePending.two_load_runF_eq_traceW', 'E2E.LinkSys.two_load_fault_stepF_of_images'])
fixed.update(['E2E.LinkSys.two_load_fault_stepF_of_code_image', 'E2E.LinkSys.two_load_return_stepF_of_code_image'])
fixed.update(['E2E.LinkSys.two_load_return_trace_stepF', 'E2E.LinkSys.two_load_original_return_stepF_NIW'])
fixed.update(['E2E.StockAcquirePending.two_load_compiled_no_relocations'])
fixed.add('E2E.StockAcquirePending.two_load_linked_actEntry')
assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for n,v in ax.items() if n not in fixed)
native='Backend.Stock.Proof.AcquireTwoLoadPrefix.observed_true._native.native_decide.ax_1✝'
assert all(set(ax[n])-{'propext','Classical.choice','Quot.sound'} == {native} for n in fixed)
fixed.update({'E2E.LinkSys.two_load_runGoodB_of_traceW','E2E.LinkSys.two_load_public_fault_runGoodBW'})
old=json.loads((A/'universal-actual-empty-relocations-checkpoint-v101/state.json').read_text())
assert all(ax[n]==xs for n,xs in old['axioms'].items())
src={};art={}
for rel,h in old['source_hashes'].items():
 if rel.startswith('FV/'):
  assert sha(P/rel)==h,rel
  d=O/'source'/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(P/rel,d);src[rel]=sha(d)
for module in ['FV.E2E.StockAcquireLinkedBaseEntry', 'FV.E2E.StockAcquireTwoLoadLinkedEntry']:
 rel=module.replace('.','/')+'.lean';d=O/'source'/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(P/rel,d);src[rel]=sha(d)
for rel in src:
 m=rel.removesuffix('.lean');art[m]=sha(P/'.lake/build/lib/lean'/(m+'.olean'))
rel='scripts/audit/stock-acquire-metadata.lean';d=O/'source'/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(audit,d);src[rel]=sha(d)
state={'status':'passed_linked_entry_from_original_base_fields_and_actual_preparation','roots':829,'standard_roots':801,'fixed_witness_roots':28,'axioms':ax,'all_824_prior_ax_exact':True,'source_hashes':src,'artifact_hashes':art,'real_auditor_exit':r.returncode,'real_auditor_sha256':sha(auditor),'real_stdout_sha256':sha(logs/'stdout.log'),'real_audit_log_sha256':sha(logs/'stock-acquire-metadata.log'),'memstats':(logs/'memstats').read_text(),'normal_snapshot_sha256':sha(F/'import-snapshot-v25.json'),'normal_no_build_sha256':sha(F/'import-normal-check-v25.json'),'previous_checkpoint_sha256':sha(A/'universal-actual-empty-relocations-checkpoint-v101/state.json'),'claims':dict(old['claims']),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
state['claims'].update(
 linked_external_return_contract_from_original_baseExt=True,
 linked_hook_pc_contract_from_original_basePc=True,
 linked_ArmStepX_identity_from_exact_definition=True,
 actual_two_load_noCall_noTls_discharges_linked_ActEntry_sites=True,
 original_public_MachEntry_budget_discharge=False,
 physical_pipeline_inhabitation=False,
 full_goal_complete=False)
state['provider390_receipt_sha256']=sha(A/'no-call-bounded-adapter-readiness-v1/final-recovery-v1/receipt.json')
state['provider390_snapshot_sha256']=sha(A/'no-call-bounded-adapter-readiness-v1/proof-provider390-v1/snapshot.json')
state['verification_runs']={}
for attempt in ['acquire810-linked-base-entry-v1', 'acquire810-two-load-linked-entry-v1']:
 p=F/'runs'/attempt/'state.json';state['verification_runs'][attempt]={'sha256':sha(p),'status':json.loads(p.read_text())['status']}
(O/'state.json').write_text(json.dumps(state,indent=2)+'\n')
