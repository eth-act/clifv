from pathlib import Path
import json,hashlib,shutil,datetime
T=Path(__file__).resolve().parent;Q=T.parent;R=Q/'validation-package-v1';C=T/'reviewed-link-provider-program-v1';C.mkdir()
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
receipt=T/'link-provider-program-v1/receipt.json';context=json.loads(receipt.read_text());audit=T/'link-provider-program-audit-v1/exact-set-comparison.json';A=json.loads(audit.read_text());assert A['old60_exact'] and A['roots']==87
sources={}
for n in ['FV/E2E/LinkTrapCall.lean','FV/E2E/LinkTrapCallInd.lean','FV/E2E/LinkTrapProviderProgram.lean']:
 p=C/n;p.parent.mkdir(parents=True,exist_ok=True);assert (T/n).read_bytes()==(R/n).read_bytes();shutil.copyfile(T/n,p);sources[n]=sha(p)
outputs={}
for n,h in context['source_hashes'].items():
 assert sha(R/n)==h,n
 stem=Path(n).with_suffix('');trace=R/'.lake/build/lib/lean'/stem.with_suffix('.trace');assert trace.exists(),n
 data=json.loads(trace.read_text());p=R/'.lake/build/lib/lean'/stem
 files={str(f.relative_to(R)):sha(f) for f in sorted(p.parent.glob(p.name+'.*')) if f.is_file()}
 assert any(k.endswith('.olean') for k in files),n
 outputs[n]=dict(trace=data,files=files)
outputManifest=T/'linked-provider-program-normal-outputs-v1.json';outputManifest.write_text(json.dumps(dict(context_receipt_sha256=sha(receipt),modules=outputs,status='actual-kernel-normal-keys-and-output-hashes'),indent=2)+'\n')
state=dict(status='passed-staged-integration-context',base=context['base'],source_hashes=sources,actual_source_closure=len(context['source_hashes']),full_closure_receipt_sha256=sha(receipt),normal_output_manifest_sha256=sha(outputManifest),audit_receipt_sha256=sha(T/'link-provider-program-audit-v1/receipt.json'),exact_axiom_comparison_sha256=sha(audit),old_headers_exact=60,old_axiom_sets_exact=60,new_generic_standard_roots=25,existing_static_helper_roots=2,audited_roots=87,original_inputs={n:sha(Q/n) for n in ['original-caller.clif','original-callee.clif']},canonical_callee_manifest_sha256=sha(T/'standalone-callee-canonical-v2/manifest.json'),frozen_constructor_edits=[],open=['MapFaults/TrapAtF executable integration','actual linked ARM and all three CLI/generated flows, both modes and distinct float variant','default production admission; three843 constructors stay frozen'],utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(C/'manifest.json').write_text(json.dumps(state,indent=2)+'\n');print('frozen',len(outputs),'normal modules;87roots;60old contracts exact',flush=True);print('manifest_sha256',sha(C/'manifest.json'),flush=True)
