from pathlib import Path
import os,json,subprocess,hashlib,re,shutil,datetime
O=Path(__file__).resolve().parent;A=O.parent;E=A.parent;F=E/'140-fence-packet-v1';P=F/'package';R=E/'fence-acquire-audit-correction-v1';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='fence-1G'
logs=O/'logs';logs.mkdir(exist_ok=True);env=dict(os.environ);env.pop('FV_LAKE_CACHE',None);env.pop('FV_MEMCAP_OFF',None);tool='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin';env.update(PATH=str(R/'tools/bin')+':'+tool+':'+env['PATH'],LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',FV_ROOT=str(P),FV_MEMCAP='1G',FV_MEMCAP_UNIT='worker-o-acquire-earlier-acquire-before-later-fault-real-audit-v69',FV_MEMCAP_STATS=str(logs/'memstats'),LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LAKE_CACHE_DIR=str(F/'disabled-cache'))
auditor=R/'tools/scripts/axiom-audit.py';audit=P/'scripts/audit/stock-acquire-metadata.lean';cmd=['python3',str(auditor),'--cwd',str(P),'--log-dir',str(logs),str(audit)]
with (logs/'stdout.log').open('w') as out:r=subprocess.run(['/home/lee/clifv/.worktrees/stock-extending-production-20261031/scripts/memcap.sh',*cmd],cwd=P,env=env,stdout=out,stderr=subprocess.STDOUT)
print((logs/'stdout.log').read_text(),flush=True);assert r.returncode==0
text=(logs/'stock-acquire-metadata.log').read_text()
ax={n:sorted(x.strip() for x in xs.replace('\n',' ').split(',') if x.strip()) for n,xs in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",text,re.S)}
ax.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",text)})
assert len(ax)==563,len(ax)
assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in ax.values())
old=json.loads((A/'universal-frozen-source-fallback-frontier-checkpoint-v68/state.json').read_text())
assert all(ax[n]==xs for n,xs in old['axioms'].items())
src={};art={}
for rel,h in old['source_hashes'].items():
 if rel.startswith('FV/'):
  assert sha(P/rel)==h,rel
  d=O/'source'/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(P/rel,d);src[rel]=sha(d)
for name in ['StockAcquirePartialPrefixHead', 'StockAcquirePartialPrefixValues', 'StockAcquirePartialPrefixPointer', 'StockAcquireReadPrefixWorld', 'StockAcquireReadBeforeLaterFault']:
 rel='FV/Backend/Proof/'+name+'.lean';d=O/'source'/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(P/rel,d);src[rel]=sha(d)
for rel in src:
 m=rel.removesuffix('.lean');art[m]=sha(P/'.lake/build/lib/lean'/(m+'.olean'))
rel='scripts/audit/stock-acquire-metadata.lean';d=O/'source'/rel;d.parent.mkdir(parents=True);shutil.copy2(audit,d);src[rel]=sha(d)
state={'status':'passed_actual_earlier_acquire_callback_before_later_source_fault','roots':563,'standard_roots':563,'axioms':ax,'all_555_prior_ax_exact':True,'source_hashes':src,'artifact_hashes':art,'real_auditor_exit':r.returncode,'real_auditor_sha256':sha(auditor),'real_stdout_sha256':sha(logs/'stdout.log'),'real_audit_log_sha256':sha(logs/'stock-acquire-metadata.log'),'memstats':(logs/'memstats').read_text(),'normal_snapshot_sha256':sha(F/'import-snapshot-v25.json'),'normal_no_build_sha256':sha(F/'import-normal-check-v25.json'),'previous_checkpoint_sha256':sha(A/'universal-frozen-source-fallback-frontier-checkpoint-v68/state.json'),'claims':dict(old['claims']),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
state['claims'].update(selected_pending_head_derived_from_successful_prefix_before_later_fault=True,earlier_atomic_value_pointer_and_memory_derived_without_consumer_step=True,selected_pointer_binding_and_type_derived_at_frozen_fault_prefix=True,actual_earlier_acquire_executes_before_later_source_fault=True,earlier_acquire_retires_exact_successful_capture_and_preserves_all_frontier_fields=True,later_source_fault_frame_and_history_remain_exact=True,no_source_consumer_step_or_future_return_premise=True,actual_source_cut_and_frontier_construction_from_whole_execution=False,actual_mixed_machine_prefix_derived=False,full_prefix_StRel_reachability_derived=False,preparation_cleanup_retention_transformation_erasure_derived=False,all_uncolored_emitted_forms_classified=False,universal_deferred_first_fault_composition=False,full_goal_complete=False)
(O/'state.json').write_text(json.dumps(state,indent=2)+'\n')
