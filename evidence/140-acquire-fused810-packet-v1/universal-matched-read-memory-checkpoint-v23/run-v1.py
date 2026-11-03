from pathlib import Path
import os,json,subprocess,hashlib,re,shutil,datetime
O=Path(__file__).resolve().parent;A=O.parent;E=A.parent;F=E/'140-fence-packet-v1';P=F/'package';R=E/'fence-acquire-audit-correction-v1';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='fence-1G'
logs=O/'logs';logs.mkdir();env=dict(os.environ);env.pop('FV_LAKE_CACHE',None);env.pop('FV_MEMCAP_OFF',None);tool='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin';env.update(PATH=str(R/'tools/bin')+':'+tool+':'+env['PATH'],LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',FV_ROOT=str(P),FV_MEMCAP='1G',FV_MEMCAP_UNIT='worker-o-acquire-matched-read-memory-real-audit-v23',FV_MEMCAP_STATS=str(logs/'memstats'),LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LAKE_CACHE_DIR=str(F/'disabled-cache'))
auditor=R/'tools/scripts/axiom-audit.py';audit=P/'scripts/audit/stock-acquire-metadata.lean';cmd=['python3',str(auditor),'--cwd',str(P),'--log-dir',str(logs),str(audit)]
with (logs/'stdout.log').open('w') as out:r=subprocess.run(['/home/lee/clifv/.worktrees/stock-extending-production-20261031/scripts/memcap.sh',*cmd],cwd=P,env=env,stdout=out,stderr=subprocess.STDOUT)
print((logs/'stdout.log').read_text(),flush=True);assert r.returncode==0
text=(logs/'stock-acquire-metadata.log').read_text()
ax={n:sorted(x.strip() for x in xs.replace('\n',' ').split(',') if x.strip()) for n,xs in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",text,re.S)}
ax.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",text)})
assert len(ax)==159,len(ax)
assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in ax.values())
old=json.loads((A/'universal-source-read-interval-checkpoint-v22/state.json').read_text())
assert all(ax[n]==xs for n,xs in old['axioms'].items())
src={};art={}
for rel,h in old['source_hashes'].items():
 if rel.startswith('FV/'):
  assert sha(P/rel)==h,rel
  d=O/'source'/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(P/rel,d);src[rel]=sha(d)
for name in ['StockAcquireReadFormats', 'StockAcquireSinkFormatSources', 'StockAcquireSinkFormatContext', 'StockAcquireSinkSourceMemory', 'StockAcquireSinkFormatNode', 'StockAcquireSinkFormatDriver', 'StockAcquireMatchedSinkSources']:
 rel='FV/Backend/Proof/'+name+'.lean';d=O/'source'/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(P/rel,d);src[rel]=sha(d)
for rel in src:
 m=rel.removesuffix('.lean');art[m]=sha(P/'.lake/build/lib/lean'/(m+'.olean'))
rel='scripts/audit/stock-acquire-metadata.lean';d=O/'source'/rel;d.parent.mkdir(parents=True);shutil.copy2(audit,d);src[rel]=sha(d)
state={'status':'passed_actual_driver_derived_sink_source_existence_and_matched_helper_read_memory_frames','roots':159,'standard_roots':159,'axioms':ax,'all_148_prior_ax_exact':True,'source_hashes':src,'artifact_hashes':art,'real_auditor_exit':r.returncode,'real_auditor_sha256':sha(auditor),'real_stdout_sha256':sha(logs/'stdout.log'),'real_audit_log_sha256':sha(logs/'stock-acquire-metadata.log'),'memstats':(logs/'memstats').read_text(),'normal_snapshot_sha256':sha(F/'import-snapshot-v25.json'),'normal_no_build_sha256':sha(F/'import-normal-check-v25.json'),'previous_checkpoint_sha256':sha(A/'universal-source-read-interval-checkpoint-v22/state.json'),'claims':dict(old['claims']),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
state['claims'].update(actual_driver_derives_sink_format_original_source_existence=True,actual_helper_matched_source_success_memory_preserved=True,bitcast_format_alternative_preserved=True,whole_pending_read_classification=False,whole_pending_memory_simulation=False,current_main_gate_passed=False,actual_atomic_source_success_preserves_memory=True,actual_selected_atomic_source_read_contract=True,actual_original_atomic_fault_shape=True,all_actual_emitted_record_pending_reverse_source_order=True,all_actual_emitted_record_pending_exact_source_event_positions=True,relative_memory_effect_execution_order=False,actual_record_indexed_pending_interpreter_frontiers=True,actual_forward_record_pending_group_association=True,whole_scan_sunk_persistence=True,whole_scan_exact_sink_updates=True,actual_reverse_chunk_assembly=True,whole_scan_pending_queue_source_membership=True,deferred_source_effect_composition=False,source_memory_equality_not_claimed=True,universal_root_record_refinement=False,universal_deferred_first_fault_composition=False,full_goal_complete=False)
(O/'state.json').write_text(json.dumps(state,indent=2)+'\n')
