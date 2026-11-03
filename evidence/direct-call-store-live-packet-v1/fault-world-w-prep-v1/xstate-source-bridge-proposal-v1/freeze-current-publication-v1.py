from pathlib import Path
import json,hashlib,shutil,subprocess,sys
D=Path(__file__).resolve().parent;Q=D.parent.parent;R=Q/'validation-package-v1';B=Path('/home/lee/clifv');L=D/'focused-kernels-v7';rp=L/'receipt.json';r=json.loads(rp.read_text());C=D/'canonical-source-interface-v2';C.mkdir();sys.path.insert(0,str(Q));from axiom_records import parse_records
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
audit=L/'audit/unwind-memory-source.log';actual=dict(parse_records(audit.read_text()));assert set(actual)==set(r['standard_roots']) and len(actual)==8;assert all(set(a)<=set(['propext','Classical.choice','Quot.sound']) for a in actual.values())
base=subprocess.check_output(['gh','api','repos/eth-act/clifv/commits/main','--jq','.sha'],cwd=B,text=True).strip();baseTree=subprocess.check_output(['git','rev-parse',base+'^{tree}'],cwd=B,text=True).strip();bridge={}
for n,h in r['full_source_hashes'].items():
 assert sha(R/n)==h,n
 if n not in r['source_hashes']:
  blob=subprocess.check_output(['git','show',base+':'+n],cwd=B);assert hashlib.sha256(blob).hexdigest()==h,n;bridge[n]=h
for n,h in r['source_hashes'].items():
 assert sha(D/'source'/n)==h;target=C/'source'/n;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(D/'source'/n,target)
configBridge={}
for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']:
 blob=subprocess.check_output(['git','show',base+':'+n],cwd=B);expected=blob.replace(b'weakLeanArgs = [',b'weakLeanArgs = ["-j1",',1) if n=='lakefile.toml' else blob;assert (R/n).read_bytes()==expected,n;configBridge[n]=dict(base_sha256=hashlib.sha256(blob).hexdigest(),actual_sha256=sha(R/n),delta='only approved weak -j1' if n=='lakefile.toml' else 'exact')
normal={}
for n,h in r['full_source_hashes'].items():
 stem=R/'.lake/build/lib/lean'/n[:-5];tr=stem.with_suffix('.trace');td=json.loads(tr.read_text());assert not td.get('synthetic');c=R/'.lake/build/ir'/Path(n[:-5]+'.c');assert c.exists() and c.with_suffix('.c.hash').read_text().strip()+'.c'==td['outputs']['c'];normal[n]=dict(source_sha256=h,native_key=td['depHash'],outputs=td['outputs'],trace_sha256=sha(tr),olean_sha256=sha(stem.with_suffix('.olean')))
trackedAudit=C/'source/scripts/audit/unwind-memory-source.lean';trackedAudit.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(L/'unwind-memory-source.lean',trackedAudit);sources={**r['source_hashes'],'scripts/audit/unwind-memory-source.lean':sha(trackedAudit)};shutil.copyfile(audit,C/'actual-auditor-output.log')
manifest=dict(status='PASSED_EXACT_CURRENT_SOURCE_INTERFACE',base=base,base_tree=baseTree,sources=sources,source_projection=bridge,config_bridge=configBridge,normal177=normal,axiom_sets=actual,real_auditor_sha256=r['real_auditor_sha256'],kernel_receipt_sha256=sha(rp),records=r['records'],old_UnwindStatement_sha256=sha(R/'FV/E2E/UnwindStatement.lean'),ordinary_load_store='Both complete default-flag source functions inhabit TrapsExplicitMX and their actual MemTrapAt event. Neither fixture replaces the original call-store capture.',open=['Production derivation of all new internal instances','Actual caught-handler memory-fault execution','Generic try/callee traps and executable first-fault transfer','Separate Clif.ReachesX conversion proper-current gate'],no_new_caller_requirement=True,old_interface_unchanged=True)
(C/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print(C);print(sha(C/'manifest.json'))
