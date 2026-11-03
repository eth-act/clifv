from pathlib import Path
import json,hashlib,subprocess,os,datetime
O=Path(__file__).resolve().parent;A=O.parent;E=A.parent;D=O/'host-R376-v2';D.mkdir();old=O/'host-R376-v1/receipt.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(old)=='0573bc009c871e4d2728687de9884e6793a65bfc134c4f8945c23bb9bdf58d65';r=json.loads(old.read_text());R=E/'direct-call-store-live-packet-v1/validation-package-v1';Q=E/'direct-call-store-live-packet-v1/production-current8f-dispatcher-integration-v1';origin=Q/'four-core-creator-current-R-v1/receipt.json';assert sha(origin)=='4ce80786963309e2ec9db793e35b07a655f652fb31b27050f28b35495b12c4eb';o=json.loads(origin.read_text());repro=Q/'six-held-compact-origin-reproduction-v1/receipt.json';assert sha(repro)==o['origin_receipt_sha256']=='edf3f7424892b5b0aa08f86f14c9d6984e06392960cb0638c5be151858ebf536';assert set(o['records'])==set(m['module'] for m in r['unmatched'])
for miss in r['unmatched']:
 m=miss['module'];row=r['records'][m];approved=o['records'][m];assert row['source_sha256']==approved['source_sha256'] and row['current_key']==approved['native_key'] and row['trace_sha256']==approved['R_trace_sha256'];creator=approved['origin'];assert creator['producer_conclusion']=='success';assert all(row['payloads'][ext]['sha256']==creator['payloads'][ext]['extracted_sha256']==creator['payloads'][ext]['R_sha256'] for ext in ['olean','ilean','c']);source=subprocess.check_output(['git','show',creator['producer_head']+':'+m.replace('.','/')+'.lean']);assert hashlib.sha256(source).hexdigest()==row['source_sha256'];row.update(supported=True,approved_origin_receipt_sha256=sha(origin),exact_reconstructed_origin=creator)
for m,row in r['records'].items():
 rel=m.replace('.','/');assert sha(R/(rel+'.lean'))==row['source_sha256'];assert sha(R/'.lake/build/lib/lean'/(rel+'.trace'))==row['trace_sha256']
 for ext,folder in [('olean','.lake/build/lib/lean'),('ilean','.lake/build/lib/lean'),('c','.lake/build/ir')]:assert sha(R/folder/(rel+'.'+ext))==row['payloads'][ext]['sha256']
for n,h in r['configuration_hashes'].items():assert sha(R/n)==h==o['configs'][n]
for p in Path('/proc').iterdir():
 if not p.name.isdigit() or int(p.name)==os.getpid():continue
 try:
  args=(p/'cmdline').read_bytes().decode(errors='replace').replace('\0',' ')
  if '/bin/lean ' in args and any(str(R/(m.replace('.','/')+'.lean')) in args for m in r['records']):raise RuntimeError(('overlapping writer',p.name))
 except (OSError,PermissionError):pass
r.update(status='passed_exact_R376_source_config_current_key_normal_output_creator_gate',unmatched=[],prior_hold_receipt_sha256=sha(old),four_exact_preexisting_origin_receipt_sha256=sha(origin),six_entry_reconstruction_sha256=sha(repro),two_stale_checker_holds_preserved=True,all_prior_normal_key_and_cold_results_reused_with_unchanged_R_bytes=True,new_leaf_started=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(D/'receipt.json').write_text(json.dumps(r,indent=2)+'\n');print('passed receipt',sha(D/'receipt.json'))
