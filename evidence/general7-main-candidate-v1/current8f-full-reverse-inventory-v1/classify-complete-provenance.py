from pathlib import Path
import json,hashlib,collections
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';D=E/'general7-main-candidate-v1/current8f-full-reverse-inventory-v1';G=B/'.worktrees/loop-20261102';P=E/'892-joint-current-context-v2/package';R=E/'direct-call-store-live-packet-v1/validation-package-v1';M=json.loads((D/'remaining-cone-proposal-v1.json').read_text());keyKnown=M['initial_current_keys'];approved={}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for name in ['actual-compact-cache-provenance-v1','actual-compact-cache-provenance-v2','EdgeSplit-archive-provenance-v1','NI-nine-archive-provenance-v1','NI209-archive-provenance-v1','full1657-39-archive-provenance-v1','direct31-six-archive-provenance-v1','direct31-remaining20-archive-provenance-v1','direct33-baseline21-archive-provenance-v1']:
 p=E/'general7-main-candidate-v1'/name/'receipt.json';receipt=json.loads(p.read_text())
 for source,record in receipt.get('records',{}).items():
  matched=record.get('matched')
  if not matched or not matched.get('trace_bytes_exact'):continue
  approved.setdefault(source[:-5].replace('/','.'),[]).append({'receipt':str(p),'receipt_sha256':sha(p),'record':record})
rows=[];counts=collections.Counter()
for module in M['complete_source_order']:
 rel=Path(module.replace('.','/'));src=G/rel.with_suffix('.lean');data=src.read_bytes();assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==M['source_git_blobs'][module],module;sourceSha=hashlib.sha256(data).hexdigest();trace=G/'.lake/build/lib/lean'/rel.with_suffix('.trace');t=json.loads(trace.read_text()) if trace.exists() else {};key=t.get('depHash');row={'target':module,'source_sha256':sourceSha,'known_current_key':keyKnown.get(module),'G_recorded_key':key,'G_trace_sha256':sha(trace) if trace.exists() else None,'G_trace_kind':('missing' if not t else 'synthetic' if t.get('synthetic') else 'full-input' if t.get('inputs') else 'origin-required'),'existing_approved_archive_matches':[],'proper_donor_candidates':[]}
 for approval in approved.get(module,[]):
  record=approval['record'];matched=record['matched']
  if key!=record.get('native_key') or row['G_trace_sha256'] not in [record.get('P_trace_sha256'),record.get('R_trace_sha256')]:continue
  okay=True
  for kind,entry in matched['payloads'].items():
   area='.lake/build/ir' if kind=='c' else '.lake/build/lib/lean';payload=G/area/rel.with_suffix('.'+kind)
   if not payload.exists() or sha(payload)!=entry['extracted_sha256']:okay=False;break
  if okay:row['existing_approved_archive_matches'].append({'receipt':approval['receipt'],'receipt_sha256':approval['receipt_sha256'],'native_key':key})
 for label,root in [('P',P),('R',R)]:
  s=root/rel.with_suffix('.lean');tr=root/'.lake/build/lib/lean'/rel.with_suffix('.trace')
  if not s.exists() or not tr.exists() or sha(s)!=sourceSha:continue
  donor=json.loads(tr.read_text())
  if donor.get('synthetic') or not donor.get('inputs'):continue
  expected=keyKnown.get(module,key)
  if expected is not None and donor.get('depHash')!=expected:continue
  row['proper_donor_candidates'].append({'owner':label,'depHash':donor.get('depHash'),'trace_sha256':sha(tr),'key_status':'actual current query matches' if module in keyKnown else 'matches stored Loop key only; actual current query still required','actual_normal_still_required':True})
 if row['existing_approved_archive_matches']:category='existing approved archive payload match'
 elif row['G_trace_kind']=='full-input':category='Loop full-input record; actual current-key check required'
 elif row['proper_donor_candidates']:category='proper source/key candidate donor; actual checks required'
 else:category='unresolved creator/key provenance'
 row['classification']=category;counts[category]+=1;rows.append(row)
(D/'complete3381-origin-donor-classification-v1.json').write_text(json.dumps({'scope':'classification only; no acceptance or normal claim','counts':dict(counts),'approved_entries_loaded':sum(map(len,approved.values())),'rows':rows},indent=2)+'\n');print(json.dumps({'counts':dict(counts),'approved_entries_loaded':sum(map(len,approved.values()))}))
