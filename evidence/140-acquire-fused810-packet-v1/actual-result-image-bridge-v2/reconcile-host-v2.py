from pathlib import Path
import json,hashlib,subprocess,os,datetime
O=Path(__file__).resolve().parent;A=O.parent;E=A.parent;D=O/'host-R369-v2';D.mkdir();old=O/'host-R369-v1/receipt.json';r=json.loads(old.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();R=E/'direct-call-store-live-packet-v1/validation-package-v1';G=E/'general7-main-candidate-v1'
assert sha(old)=='be067e20e58d57d66bc2dacb8bd6b0e5d9aa82bb2c670dc2a5edc493879f3154'
extra=[(G/'direct33-baseline21-archive-provenance-v1/receipt.json','47e1a8dbaf303a6ac00956b22153be6c94ef4a8c2ff46fa7048844b82041f9b5'),(G/'NI-nine-archive-provenance-v1/receipt.json','b7c04aeeb54e3468dbc34b44452a50d1f430cbe855dd3fb968680215eb6ae223'),(A/'no-call-bounded-adapter-readiness-v1/linkclif-native-origin-v1/receipt.json','77285b5964a67c1f176285f3f2712944a2dd586e8069b0b94cde02b99b4562ab')]
approvals=[]
for p,h in extra:assert sha(p)==h;approvals.append((p,json.loads(p.read_text())))
for missing in r['unmatched']:
 m=missing['module'];row=r['records'][m];rel=m.replace('.','/')+'.lean';matches=[]
 for p,rr in approvals:
  rec=rr.get('records',{}).get(rel)
  if not rec or not rec.get('matched') or rec['native_key']!=row['current_key'] or rec['outputs']!=row['outputs'] or rec['P_trace_sha256']!=row['trace_sha256']:continue
  creator=rec['matched'];assert creator['producer_conclusion']=='success';assert all(creator['payloads'][ext]['extracted_sha256']==row['payloads'][ext]['sha256'] for ext in ['olean','ilean','c']);source=subprocess.check_output(['git','show',creator['producer_head']+':'+rel]);assert hashlib.sha256(source).hexdigest()==row['source_sha256'];matches.append({'receipt':str(p),'receipt_sha256':sha(p),'creator':creator})
 assert matches,m
 row.update(supported=True,exact_additional_approved_matches=matches)
registry=G/'current8f-full-reverse-inventory-v1/archive76-reviewed-origin-receipt-v1.json';assert sha(registry)=='0c3fd868b71254f823d84d06227deb6a11e218f51b1d89dc531e9f591e142a98';reviewed=json.loads(registry.read_text());applicable=[]
for row in reviewed['rows']:
 m=row['target'];cur=r['records'].get(m)
 if cur and row.get('actual_native_key')==cur['current_key'] and row.get('current_trace_sha256')==cur['trace_sha256']:applicable.append(m)
binding=E/'direct-call-store-live-packet-v1/production-current8f-dispatcher-integration-v1/LinkCheck369-approved-creator-binding-v1.json';assert sha(binding)=='a1a523bc93679cd195beb6aafac86e831868680e4c421bd29fe0d91efb10a5ad';b=json.loads(binding.read_text())
for m,row in r['records'].items():
 rel=m.replace('.','/');assert sha(R/(rel+'.lean'))==row['source_sha256'];assert sha(R/'.lake/build/lib/lean'/(rel+'.trace'))==row['trace_sha256'];br=b['current369_source_native_trace_records'][m];assert br['source_sha256']==row['source_sha256'] and br['native_key']==row['current_key'] and br['trace_sha256']==row['trace_sha256']
 for ext,folder in [('olean','.lake/build/lib/lean'),('ilean','.lake/build/lib/lean'),('c','.lake/build/ir')]:assert sha(R/folder/(rel+'.'+ext))==row['payloads'][ext]['sha256']
for n,h in r['configuration_hashes'].items():assert sha(R/n)==h
for p in Path('/proc').iterdir():
 if not p.name.isdigit() or int(p.name)==os.getpid():continue
 try:
  args=(p/'cmdline').read_bytes().decode(errors='replace').replace('\0',' ')
  if '/bin/lean ' in args and any(str(R/(m.replace('.','/')+'.lean')) in args for m in r['records']):raise RuntimeError(('overlapping writer',p.name))
 except (OSError,PermissionError):pass
r.update(status='passed_exact_R369_source_config_current_key_normal_output_creator_gate',unmatched=[],previous_failed_receipt_sha256=sha(old),additional_approved_origin_receipts={str(p):sha(p) for p,h in extra},reviewed76_receipt_sha256=sha(registry),reviewed76_exact_applicable_modules=applicable,source_worker_creator_binding_sha256=sha(binding),all_prior_normal_key_and_cold_hash_results_reused_with_unchanged_R_bytes=True,new_leaf_started=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(D/'receipt.json').write_text(json.dumps(r,indent=2)+'\n');print('passed receipt',sha(D/'receipt.json'),'unmatched',r['unmatched'])
