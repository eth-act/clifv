from pathlib import Path
import os,json,subprocess,hashlib,re,shutil,datetime
O=Path(__file__).resolve().parent;A=O.parent;E=A.parent;F=E/'140-fence-packet-v1';P=F/'package';R=E/'fence-acquire-audit-correction-v1';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='fence-1G'
logs=O/'logs';logs.mkdir(exist_ok=True);env=dict(os.environ);env.pop('FV_LAKE_CACHE',None);env.pop('FV_MEMCAP_OFF',None);tool='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin';env.update(PATH=str(R/'tools/bin')+':'+tool+':'+env['PATH'],LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',FV_ROOT=str(P),FV_MEMCAP='1G',FV_MEMCAP_UNIT='worker-o-acquire-two-load-indexed-source-real-audit-v75',FV_MEMCAP_STATS=str(logs/'memstats'),LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LAKE_CACHE_DIR=str(F/'disabled-cache'))
auditor=R/'tools/scripts/axiom-audit.py';audit=P/'scripts/audit/stock-acquire-metadata.lean';cmd=['python3',str(auditor),'--cwd',str(P),'--log-dir',str(logs),str(audit)]
with (logs/'stdout.log').open('w') as out:r=subprocess.run(['/home/lee/clifv/.worktrees/stock-extending-production-20261031/scripts/memcap.sh',*cmd],cwd=P,env=env,stdout=out,stderr=subprocess.STDOUT)
print((logs/'stdout.log').read_text(),flush=True);assert r.returncode==0
text=(logs/'stock-acquire-metadata.log').read_text()
ax={n:sorted(x.strip() for x in xs.replace('\n',' ').split(',') if x.strip()) for n,xs in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",text,re.S)}
ax.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",text)})
assert len(ax)==603,len(ax)
fixed={'Backend.Stock.Proof.AcquireTwoLoadPrefix.original_two_load_schedule','Backend.Stock.Proof.AcquireTwoLoadPrefix.original_two_load_virtual_prefix','Backend.Stock.Proof.AcquireTwoLoadPrefix.original_two_load_acquire_boundary','Backend.Stock.Proof.AcquireTwoLoadPrefix.original_two_load_prepared_machine_fault','Backend.Stock.Proof.AcquireTwoLoadPrefix.original_two_load_execution_witness'}
assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for n,v in ax.items() if n not in fixed)
native='Backend.Stock.Proof.AcquireTwoLoadPrefix.observed_true._native.native_decide.ax_1✝'
assert all(set(ax[n])-{'propext','Classical.choice','Quot.sound'} == {native} for n in fixed)
old=json.loads((A/'universal-two-load-source-entry-checkpoint-v74/state.json').read_text())
assert all(ax[n]==xs for n,xs in old['axioms'].items())
src={};art={}
for rel,h in old['source_hashes'].items():
 if rel.startswith('FV/'):
  assert sha(P/rel)==h,rel
  d=O/'source'/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(P/rel,d);src[rel]=sha(d)
for name in ['StockAcquireTwoLoadActualSource','StockAcquireTwoLoadSourceRelations','StockAcquireTwoLoadOriginalSource','StockAcquireTwoLoadOriginalMachineW']:
 rel='FV/Backend/Proof/'+name+'.lean';d=O/'source'/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(P/rel,d);src[rel]=sha(d)
for rel in src:
 m=rel.removesuffix('.lean');art[m]=sha(P/'.lake/build/lib/lean'/(m+'.olean'))
rel='scripts/audit/stock-acquire-metadata.lean';d=O/'source'/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(audit,d);src[rel]=sha(d)
state={'status':'passed_two_load_original_second_fault_indexed_source_and_machine_bridge','roots':603,'standard_roots':598,'fixed_witness_roots':5,'axioms':ax,'all_597_prior_ax_exact':True,'source_hashes':src,'artifact_hashes':art,'real_auditor_exit':r.returncode,'real_auditor_sha256':sha(auditor),'real_stdout_sha256':sha(logs/'stdout.log'),'real_audit_log_sha256':sha(logs/'stock-acquire-metadata.log'),'memstats':(logs/'memstats').read_text(),'normal_snapshot_sha256':sha(F/'import-snapshot-v25.json'),'normal_no_build_sha256':sha(F/'import-normal-check-v25.json'),'previous_checkpoint_sha256':sha(A/'universal-two-load-source-entry-checkpoint-v74/state.json'),'claims':dict(old['claims']),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
state['claims'].update(actual_retained_consumers_derive_both_source_endpoint_receipts=True,original_read_outcomes_construct_event_ctx_first_result_and_second_fault=True,SourceEntry_derived_for_arbitrary_original_pointer_arguments=True,original_all_fuel_trap_with_first_success_derives_second_fault_relations=True,second_fault_machine_helper_takes_original_run_and_derives_indexed_relations=True,no_external_event_context_source_execution_certificate_for_second_fault_branch=True,first_read_success_is_internal_branch_classification_not_admission_guard=True,first_source_fault_branch_full_machine_composition=False,original_full_program_execution_extracts_those_two_source_outcomes=False,physical_pipeline_witness_inhabited=False,full_BodyEntryW_and_RelW_from_original_public_entry_derived=False,linked_RunGoodLBW_from_current_trace_derived=False,executable_stepF_no_earlier_fault_prefix_derived=False,original_MapRelRW_contract_preserved=True,physical_prefix_reach_and_first_fault_derived=False,actual_source_cut_and_frontier_construction_from_whole_execution=False,actual_mixed_machine_prefix_derived=False,all_uncolored_emitted_forms_classified=False,universal_deferred_first_fault_composition=False,full_goal_complete=False)
(O/'state.json').write_text(json.dumps(state,indent=2)+'\n')
