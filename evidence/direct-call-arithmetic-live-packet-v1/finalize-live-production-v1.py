from pathlib import Path
import datetime,hashlib,json,re,shutil,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';Q=E/'direct-call-arithmetic-live-packet-v1';P=E/'direct-call-production-class-packet-v1';R=Q/'validation-package-v1';S=Q/'reviewed-live-production-v1';S.mkdir()
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024*1024):h.update(b)
 return h.hexdigest()
C=json.loads((Q/'live-exec-facades-v1/receipt.json').read_text());M=json.loads((Q/'actual-live-call-matrix-v2/result.json').read_text());A=json.loads((Q/'live-consumer-audit-final-v1/receipt.json').read_text());X=json.loads((Q/'live-additive-contract-audit-v1/receipt.json').read_text());H=json.loads((Q/'live-old-header-comparison-v1.json').read_text());assert all(x['status']=='passed' for x in [C,M,A,X,H])
assert A['old_axiom_sets_exact']==182 and H['compared']==381
runtime=json.loads((Q/'actual-live-call-matrix-v2/executed-context.json').read_text())
for n,k in runtime['dependency_keys'].items():
 if n in C['dependency_keys']:assert C['dependency_keys'][n]==k,n
 else:
  assert n in ['PrepareLiveCallBundlesV1.lean','ReflowLiveCallBundleV1.lean'];C['dependency_keys'][n]=k;C['source_hashes'][n]=runtime['source_hashes'][n];C['imports'][n]=runtime['imports'][n]
for n,h in C['source_hashes'].items():assert sha(R/n)==h,n
for n,h in C['frozen_constructor_hashes'].items():assert sha(Q/n)==h,n
old_body=lambda p:'\n'.join(x for x in p.read_text().splitlines() if not x.startswith('import ')).strip()
assert old_body(P/'FV/Backend/SemanticABICheck.lean') in old_body(Q/'FV/Backend/SemanticABICheck.lean')
backend=(Q/'FVTest/Backend/Main.lean').read_text().replace('import FV.Backend.LiveCallProduction','import FV.Backend.ResultCallProduction').replace('compileFileLiveCallWhen','compileFileResultCallWhen');assert backend==(P/'FVTest/Backend/Main.lean').read_text()
oldlink=(P/'FVTest/Link/LeanLinkMain.lean').read_text();a=oldlink.index('  -- This complete-file attempt');b=oldlink.index('  let compiled := if stockEnabled',a);assert oldlink[a:b] in (Q/'FVTest/Link/LeanLinkMain.lean').read_text()
assert (P/'FVTest/E2E/ReturnPinLinkProofWith.lean').read_bytes()==(R/'FVTest/E2E/ReturnPinLinkProofWith.lean').read_bytes()
classM=json.loads((Q/'standalone-class-source-v1/manifest.json').read_text());sources={};changed={}
for folder in ['FV','FVTest','scripts/audit']:
 for f in (Q/folder).rglob('*.lean'):
  n=str(f.relative_to(Q))
  if n in classM['owned_sources']:continue
  if n.startswith('scripts/audit/stock-live-call-old-'):continue
  if not n.startswith('scripts/') and n not in C['source_hashes']:raise AssertionError(('uninventoried production source',n))
  d=S/n;d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(f.read_bytes());sources[n]=sha(f)
  if not n.startswith('scripts/'):
   old=(P/n).read_bytes() if (P/n).exists() else None;changed[n]=dict(kind='new' if old is None else 'changed',sha256=sha(f))
for n in ['PrepareLiveCallBundlesV1.lean','ReflowLiveCallBundleV1.lean']:
 shutil.copyfile(Q/n,S/n);sources[n]=sha(Q/n)
(S/'manifest.json').write_text(json.dumps(sources,indent=2)+'\n');(S/'full-context.json').write_text(json.dumps(C,indent=2)+'\n')
floatText='function %float_leaf(f64) -> f64 {\nblock0(v0: f64):\n return v0\n}\n'
probe=(Q/'InspectLiveCallV2.lean').read_text();texts={n:json.loads(re.search(r'def '+n+r'Text : String := ("(?:[^"\\]|\\.)*")',probe).group(1)) for n in ['caller','callee']}
inputs={};artifacts={};generated={}
for case in M['cases']:
 d=Path(case['dir']);raw=(d/'input.clif').read_text();assert raw==texts['caller']+texts['callee']+(floatText if case['typed'] else '')
 answer=json.loads((d/'actual-ra.json').read_text());assert len(answer['functions'])==len(case['entries'])
 if not case['typed']:assert 'x19' in json.dumps(answer['functions'][0])
 inputs[case['module']]=dict(input_sha256=sha(d/'input.clif'),allocator_sha256=sha(d/'actual-ra.json'),cleanup=case['cleanup'],typed=case['typed'],all_original_functions_exact=True)
 for f in d.rglob('*'):
  if f.is_file():artifacts[str(f.relative_to(Q))]=sha(f)
 p=Q/'actual-live-call-matrix-v2/bundles/Crates'/(case['module']+'.lean');generated[str(p.relative_to(Q))]=sha(p)
(Q/'live-production-original-inputs-v1.json').write_text(json.dumps(dict(cases=inputs,caller_sha256=hashlib.sha256(texts['caller'].encode()).hexdigest(),callee_sha256=hashlib.sha256(texts['callee'].encode()).hexdigest(),float_sha256=hashlib.sha256(floatText.encode()).hexdigest(),generated=generated,artifacts=artifacts),indent=2)+'\n')
logs=['live-production-consumer-kernel-v1','live-production-consumer-kernel-v2','live-exec-facades-v1','actual-live-call-matrix-v1','actual-live-call-matrix-v2','live-consumer-audit-v1','live-consumer-audit-v2','live-additive-contract-audit-v1'];stats=[]
for folder in logs:
 for p in (Q/folder).glob('*.mem'):
  values={k:int(v) for k,v in re.findall(r'(peak|oom|oom_kill) (\d+)',p.read_text())}
  if values:stats.append(dict(file=str(p.relative_to(Q)),**values))
assert all(x.get('oom',0)==0 and x.get('oom_kill',0)==0 for x in stats)
(Q/'live-production-resource-evidence-v1.json').write_text(json.dumps(stats,indent=2)+'\n')
outputs={}
for f in (R/'.lake/build').rglob('*'):
 if f.is_file():outputs[str(f.relative_to(R))]=dict(sha256=sha(f),bytes=f.stat().st_size,links=f.stat().st_nlink)
(Q/'live-production-owned-outputs-v1.json').write_text(json.dumps(outputs,indent=2)+'\n')
state=dict(status='passed_staged_integration_not_publication',base=C['base'],source_context=C['source_context'],full_goal_complete=False,production_cutover_landed=False,source_snapshot='reviewed-live-production-v1/manifest.json',source_snapshot_sha256=sha(S/'manifest.json'),full_context_sha256=sha(S/'full-context.json'),production_sources=changed,normal_affected_kernels=119,additional_normal_facades=3,all_actual_runtime_dependency_keys_exact=True,actual_matrix='actual-live-call-matrix-v2/result.json',cases=4,generated_audited_roots=36,actual_three_clis=True,cleanup_modes=[False,True],original_caller_callee_and_float_exact=True,actual_stock_selection='FV/E2E/LiveCallProductionSelection.lean:selected and actual_entrypoint',actual_predecessor_selects_different_code='FV/E2E/StockLiveCallWitness.lean:actual_provider',symbolic_armret='FV/E2E/LiveCallProductionExec.lean:returned_word',returned_word='(word + 13) + word',actual_saved_register='x19',arbitrary_callee_memory='StockLiveCallDomain/Function/SourceResult/Run/NI preserve original full source and memory premises',old_headers_exact=381,old_axiom_sets_exact=182,consumer_audit_standard_roots=252,consumer_audit_fixed_roots=15,additive_standard_roots=5,all_generic_roots_standard_only=True,complete_previous_backend_action=True,complete_previous_linker_action_byte_exact=True,old_checker_body_byte_exact=True,old_shared_emitter_byte_exact=True,new_raw_route_index=None,frozen_constructor_hashes=C['frozen_constructor_hashes'],max_cgroup_peak_bytes=max(x['peak'] for x in stats),all_oom_zero=True,retained_failures=['ReturnPinAdmission projection simplification','matrix environment PATH exit127 before preparation','two missing optional executable facades in initial audit','aggregation regex crossed a no-axioms record'],outputs_manifest='live-production-owned-outputs-v1.json',outputs_files=len(outputs),outputs_bytes=sum(x['bytes'] for x in outputs.values()),cleanup=dict(status='awaiting verified remote backup',prefix=str(R),preserve='Source, configs, logs, generated Lean, objects, ELF files, allocation answers, input hashes and receipts'),remaining=['Resolve frozen constructor stage/stageF boundary before publication','Current-main reconciliation and delivery gates','Call results consumed by memory, multiple calls and original stack arguments','Every remaining original140 obligation'],utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(Q/'live-production-complete-state-v1.json').write_text(json.dumps(state,indent=2)+'\n');print(json.dumps(dict(status=state['status'],sources=len(changed),generated_roots=36,old_headers=381,old_axioms=182,peak=state['max_cgroup_peak_bytes'],output_files=len(outputs),receipt_sha256=sha(Q/'live-production-complete-state-v1.json'))),flush=True)
