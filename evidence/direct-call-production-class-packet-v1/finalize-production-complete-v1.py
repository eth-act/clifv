from pathlib import Path
import datetime,hashlib,json,os,re,shutil,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';P=E/'direct-call-production-class-packet-v1';R=P/'validation-package-v1'
def sha(f):
 h=hashlib.sha256()
 with f.open('rb') as src:
  while data:=src.read(1024*1024):h.update(data)
 return h.hexdigest()
for name in ['actual-result-call-matrix-v7/result.json','mixed-callback-kernel-v1/result.json','final-contract-audit-v1/receipt.json']:
 assert json.loads((P/name).read_text())['status']=='passed',name
assert 'PANIC' not in (P/'old-emitter-regression-v2/old-emitter-regression.log').read_text()
assert '72 configurations' in (P/'old-emitter-regression-v2/old-emitter-regression.log').read_text()
old=subprocess.check_output(['git','show','90c51c88:FV/Backend/SemanticABICheck.lean'],cwd=B,text=True);now=(P/'FV/Backend/SemanticABICheck.lean').read_text()
segment=lambda s:s[s.index('def checkCalls'):s.index('end Backend.SemanticABI')]
assert segment(old)==segment(now)
assert (P/'FV/E2E/PreparedReturnPinCalls.lean').read_bytes()==subprocess.check_output(['git','show','90c51c88:FV/E2E/PreparedReturnPinCalls.lean'],cwd=B)
float_prior=(E/'typed-compiler-modes-packet-v1/actual-cli-v1/bundles/WorkerOTypedCompilerRaw/input.clif').read_text();float_prior=float_prior[float_prior.index('function %float_leaf'):]
cases=json.loads((P/'actual-result-call-matrix-v7/result.json').read_text())['cases'];inputs={};generated={};artifacts={};root_count=0
for case in cases:
 d=Path(case['dir']);original=(d/'input.clif').read_text()
 if case['typed']:assert original.endswith(float_prior)
 inputs[case['module']]=dict(input_sha256=sha(d/'input.clif'),allocator_sha256=sha(d/'actual-ra.json'),functions={f.name:sha(f) for f in d.glob('fn*.clif')},cleanup=case['cleanup'],typed=case['typed'])
 f=P/'actual-result-call-matrix-v7/bundles/Crates'/(case['module']+'.lean');generated[str(f.relative_to(P))]=sha(f)
 for f in d.rglob('*'):
  if f.is_file():artifacts[str(f.relative_to(P))]=sha(f)
 root_count+=4+2*len(case['entries'])
assert root_count==36
snap=P/'reviewed-production-complete-v1';files={};changed={}
for folder in ['FV','FVTest','scripts/audit']:
 for f in (P/folder).rglob('*.lean'):
  n=str(f.relative_to(P));dst=snap/n;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(f,dst);files[n]=sha(f)
  if folder!='scripts/audit':
   old=subprocess.run(['git','show','90c51c88:'+n],cwd=B,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
   if old.returncode or old.stdout!=f.read_bytes():changed[n]=dict(kind='new' if old.returncode else 'changed',sha256=sha(f))
(snap/'manifest.json').write_text(json.dumps(files,indent=2)+'\n')
(P/'actual-original-inputs-v1.json').write_text(json.dumps(dict(cases=inputs,float_sha256=hashlib.sha256(float_prior.encode()).hexdigest(),generated_roots=root_count,generated_sources=generated,artifacts=artifacts),indent=2)+'\n')
stats=[]
for f in P.rglob('*.mem'):
 if R in f.parents:continue
 values=dict(re.findall(r'(peak|oom|oom_kill) (\d+)',f.read_text()))
 if values:stats.append(dict(file=str(f.relative_to(P)),**{k:int(v) for k,v in values.items()}))
assert all(s.get('oom',0)==0 and s.get('oom_kill',0)==0 for s in stats)
(P/'resource-evidence-v1.json').write_text(json.dumps(stats,indent=2)+'\n')
owned={}
for f in (R/'.lake/build').rglob('*'):
 if f.is_file() and f.stat().st_nlink==1:owned[str(f.relative_to(R))]=dict(bytes=f.stat().st_size,sha256=sha(f))
(P/'owned-build-artifacts-before-cleanup-v1.json').write_text(json.dumps(owned,indent=2)+'\n')
receipt=dict(status='passed_preserved_inner_loop',immutable_production='90c51c880b9d614f7c5f9730b8363a6321c840de',old_contract_baseline='a4c0726d46c5908b4ac06cf797ee939af8644703',current_main_validation=False,full_goal_complete=False,files=changed,accepted_binding_manifest=str(E/'direct-call-result-packet-v1.json'),source_snapshot='reviewed-production-complete-v1/manifest.json',inputs='actual-original-inputs-v1.json',actual_matrix='actual-result-call-matrix-v7/result.json',executed_dependency_keys='actual-result-call-matrix-v7/executed-context.json',actual_three_clis=True,complete_original_integer_pair=True,distinct_original_float_bytes=True,cleanup_modes=[False,True],generated_roots=36,actual_default_selection=True,symbolic_armret_and_x0_word=True,symbolic_kernel='actual-symbolic-exec-kernel-v3/result.json',generic_original_callback_retry=True,callback_kernel='mixed-callback-kernel-v1/result.json',one_parameterized_consumer_stack=True,old_checkCalls_and_previous_exact_calls_byte_identical=True,old_prepared_checker_file_byte_identical=True,old_axiom_sets_exact=108,old_axiom_comparison='final-old-axiom-comparison-v1.json',old_typed_header_comparison='final-old-header-comparison-v2.json',final_audit='final-contract-audit-v1/receipt.json',old_emitter_exact_configurations=72,old_emitter_regression='old-emitter-regression-v2/old-emitter-regression.log',all_old_raw_indices_preserved=True,no_new_raw_index=True,peak_bytes=max(s.get('peak',0) for s in stats),all_oom_zero=True,cleanup=dict(status='pending',owned_artifact_files=len(owned),owned_artifact_bytes=sum(v['bytes'] for v in owned.values())),remaining=['Current-main reconciliation and required publication gates','Call results consumed by arithmetic or memory','Live values, multiple calls, and original stack arguments','Every remaining original140 obligation'],utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(P/'production-complete-state-v1.json').write_text(json.dumps(receipt,indent=2)+'\n')
assert (R/'.lake/build').resolve()==P/'validation-package-v1/.lake/build'
shutil.rmtree(R/'.lake/build')
assert not (R/'.lake/build').exists()
receipt['cleanup']['status']='removed_owned_build_outputs';receipt['cleanup']['preserved']='All source, configuration, logs, generated Lean, input/object/ELF/allocator artifacts, receipts, and failed diagnostics'
(P/'production-complete-state-v1.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('Delivery source files',len(changed),'Generated roots',root_count,'Peak',receipt['peak_bytes'],'Owned output bytes removed',receipt['cleanup']['owned_artifact_bytes'])
print('Canonical receipt SHA256',sha(P/'production-complete-state-v1.json'))
