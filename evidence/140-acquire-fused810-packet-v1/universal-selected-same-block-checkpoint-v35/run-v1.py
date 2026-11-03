from pathlib import Path
import os,json,subprocess,hashlib,re,shutil,datetime
O=Path(__file__).resolve().parent;A=O.parent;E=A.parent;F=E/'140-fence-packet-v1';P=F/'package';R=E/'fence-acquire-audit-correction-v1';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='fence-1G'
logs=O/'logs';logs.mkdir();env=dict(os.environ);env.pop('FV_LAKE_CACHE',None);env.pop('FV_MEMCAP_OFF',None);tool='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin';env.update(PATH=str(R/'tools/bin')+':'+tool+':'+env['PATH'],LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',FV_ROOT=str(P),FV_MEMCAP='1G',FV_MEMCAP_UNIT='worker-o-acquire-selected-same-block-real-audit-v35',FV_MEMCAP_STATS=str(logs/'memstats'),LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LAKE_CACHE_DIR=str(F/'disabled-cache'))
auditor=R/'tools/scripts/axiom-audit.py';audit=P/'scripts/audit/stock-acquire-metadata.lean';cmd=['python3',str(auditor),'--cwd',str(P),'--log-dir',str(logs),str(audit)]
with (logs/'stdout.log').open('w') as out:r=subprocess.run(['/home/lee/clifv/.worktrees/stock-extending-production-20261031/scripts/memcap.sh',*cmd],cwd=P,env=env,stdout=out,stderr=subprocess.STDOUT)
print((logs/'stdout.log').read_text(),flush=True);assert r.returncode==0
text=(logs/'stock-acquire-metadata.log').read_text()
ax={n:sorted(x.strip() for x in xs.replace('\n',' ').split(',') if x.strip()) for n,xs in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",text,re.S)}
ax.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",text)})
assert len(ax)==302,len(ax)
assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in ax.values())
old=json.loads((A/'universal-actual-block-color-checkpoint-v34/state.json').read_text())
assert all(ax[n]==xs for n,xs in old['axioms'].items())
src={};art={}
for rel,h in old['source_hashes'].items():
 if rel.startswith('FV/'):
  assert sha(P/rel)==h,rel
  d=O/'source'/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(P/rel,d);src[rel]=sha(d)
for name in ['StockAcquireTermSourceBoundary', 'StockAcquireSelectedSameBlock']:
 rel='FV/Backend/Proof/'+name+'.lean';d=O/'source'/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(P/rel,d);src[rel]=sha(d)
for rel in src:
 m=rel.removesuffix('.lean');art[m]=sha(P/'.lake/build/lib/lean'/(m+'.olean'))
rel='scripts/audit/stock-acquire-metadata.lean';d=O/'source'/rel;d.parent.mkdir(parents=True);shutil.copy2(audit,d);src[rel]=sha(d)
state={'status':'passed_actual_selected_acquire_original_producer_same_block','roots':302,'standard_roots':302,'axioms':ax,'all_299_prior_ax_exact':True,'source_hashes':src,'artifact_hashes':art,'real_auditor_exit':r.returncode,'real_auditor_sha256':sha(auditor),'real_stdout_sha256':sha(logs/'stdout.log'),'real_audit_log_sha256':sha(logs/'stock-acquire-metadata.log'),'memstats':(logs/'memstats').read_text(),'normal_snapshot_sha256':sha(F/'import-snapshot-v25.json'),'normal_no_build_sha256':sha(F/'import-normal-check-v25.json'),'previous_checkpoint_sha256':sha(A/'universal-actual-block-color-checkpoint-v34/state.json'),'claims':dict(old['claims']),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
state['claims'].update(actual_global_initial_marks_derived_from_successful_buildCtx=True,actual_all_driver_state_and_block_entry_marks_classified=True,actual_all_record_input_marks_classified_including_inherited_entries=True,unconditional_branch_and_outgoing_sunk_frames=True,block_entry_marks_not_assumed_empty=True,actual_prior_scan_sunk_frontier_derived=True,new_marks_before_actual_record_are_reads_or_inherited_entry_marks=True,all_crossed_effects_in_actual_read_queue=False,inherited_block_entry_marks_classified=True,real_generated_interpreter_restricted_terms_read_classification=True,all_actual_emitted_scan_pending_reads_classified=True,actual_scan_forward_group_reads_memory_neutral_on_success=True,read_trace_forgets_to_all_old_exact_mark_contracts=True,nested_helper_calls_are_evaluator_calls_not_CLIF_source_calls=True,all_four_direct_sink_rule_matches_derive_original_source_targets=True,all_four_direct_sink_rule_matches_source_success_memory_preserved=True,actual_driver_derives_sink_format_original_source_existence=True,actual_helper_matched_source_success_memory_preserved=True,bitcast_format_alternative_preserved=True,whole_pending_read_classification=False,whole_pending_memory_simulation=False,current_main_gate_passed=False,actual_atomic_source_success_preserves_memory=True,actual_selected_atomic_source_read_contract=True,actual_original_atomic_fault_shape=True,all_actual_emitted_record_pending_reverse_source_order=True,all_actual_emitted_record_pending_exact_source_event_positions=True,relative_memory_effect_execution_order=False,actual_record_indexed_pending_interpreter_frontiers=True,actual_forward_record_pending_group_association=True,whole_scan_sunk_persistence=True,whole_scan_exact_sink_updates=True,actual_reverse_chunk_assembly=True,whole_scan_pending_queue_source_membership=True,deferred_source_effect_composition=False,source_memory_equality_not_claimed=True,universal_root_record_refinement=False,universal_deferred_first_fault_composition=False,full_goal_complete=False)
(O/'state.json').write_text(json.dumps(state,indent=2)+'\n')

state["claims"].update(actual_scan_source_cut_derived_internally=True,actual_scan_prefix_read_queue_derived_from_original_scope=True,external_color_cut_certificate=False,all_crossed_effects_in_actual_read_queue=False,delayed_memory_equality=False,emitted_first_fault_execution=False)
(O/"state.json").write_text(json.dumps(state,indent=2)+"\n")

state["claims"].update(actual_record_inclusive_prefix_queue_derived=True,actual_record_source_cut_above_every_earlier_effect=True,actual_record_crossed_original_effects_derive_source_success_frames=True,actual_root810_output_color_preserved_through_result_binding=True,delayed_memory_equality=False,emitted_first_fault_execution=False)
(O/"state.json").write_text(json.dumps(state,indent=2)+"\n")

state["claims"].update(actual_scan_prefix_source_color_gap_derived_internally=True,actual_record_output_source_color_gap_derived_internally=True,boundary_none_excluded_inside_derived_color_interval=True,same_block_producer_binding=False,delayed_memory_equality=False,emitted_first_fault_execution=False)
(O/"state.json").write_text(json.dumps(state,indent=2)+"\n")

state["claims"].update(selected_acquire_output_original_source_color_derived=True,selected_acquire_all_intervening_original_statement_success_frames_derived=True,selected_acquire_successful_contiguous_original_source_slice_preserves_memory=True,actual_source_execution_slice_shape_derived=False,same_block_producer_binding=False,delayed_source_machine_memory_correspondence=False,delayed_memory_equality=False,emitted_first_fault_execution=False)
(O/"state.json").write_text(json.dumps(state,indent=2)+"\n")

state["claims"].update(actual_successful_bare_source_execution_slice_derived=True,actual_successful_bare_source_slice_memory_derived=True,bare_calls_use_arbitrary_original_environment=True,full_program_source_mapping_derived=False,full_source_first_fault_prefix_derived=False,delayed_source_machine_memory_correspondence=False,delayed_memory_equality=False,emitted_first_fault_execution=False)
(O/"state.json").write_text(json.dumps(state,indent=2)+"\n")

state["claims"].update(actual_bare_trapped_source_slice_derived=True,actual_selected_source_first_trap_prefix_memory_derived=True,source_first_fault_or_exact_residual_trap_partition=True,full_program_source_mapping_derived=False,full_source_first_fault_prefix_derived=False,delayed_source_machine_memory_correspondence=False,delayed_memory_equality=False,emitted_first_fault_execution=False)
(O/"state.json").write_text(json.dumps(state,indent=2)+"\n")

state["claims"].update(actual_record_output_runtime_color_above_original_block_boundary=True,actual_record_output_runtime_color_bounded_by_original_terminator=True,original_source_event_same_block_from_derived_color_bounds=True,selected_producer_body_position_derived=False,same_block_producer_binding=False,delayed_source_machine_memory_correspondence=False,emitted_first_fault_execution=False)
(O/"state.json").write_text(json.dumps(state,indent=2)+"\n")

state["claims"].update(selected_producer_original_body_position_in_consumer_block_derived=True,selected_producer_terminator_case_excluded_internally=True,selected_source_slice_endpoint_order_derived=False,delayed_source_machine_memory_correspondence=False,emitted_first_fault_execution=False)
(O/"state.json").write_text(json.dumps(state,indent=2)+"\n")
