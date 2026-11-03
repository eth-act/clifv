from pathlib import Path
import json,hashlib,subprocess,shutil,datetime
D=Path(__file__).resolve().parent;E=D.parent;P=Path('/home/lee/clifv/.worktrees/loop-20261102');R=P;C=E/'892-current-main-context-v1/package/.lake/ci-cache';Recovery=E/'892-current-main-context-v1';L=D/'reverse81-archive-content-origin-v1';L.mkdir();origin=json.loads((D/'current8f-full-reverse-inventory-v1/unresolved901-archive-mapping-inventory-v1.json').read_text());names=[x['target'].replace('.','/')+'.lean' for x in origin['rows'] if x['archive_candidate_count']];assert len(names)==81;tool=Path('/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/leantar');state=json.loads((Recovery/'ci-recovery-state.json').read_text())
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1048576):h.update(b)
 return h.hexdigest()
index={}
for aid,a in state['artifacts'].items():
 for m in a['mappings']:
  path=Path(m['path']);assert sha(path)==m['sha256'],path
  for line in path.read_text().splitlines()[1:]:
   key,desc=json.loads(line)
   if isinstance(desc,str):index.setdefault(key,[]).append(dict(descriptor=desc,artifact_id=aid,stage=a['name'],producer=a['producer'],mapping=str(path),mapping_sha256=m['sha256'],zip_sha256=a['zip_sha256']))
late_path=E/'892-joint-current-context-v2/late-ci-stage-recovery-v1.json'
late=json.loads(late_path.read_text());assert late['status']=='passed' and late['run']==41408842551
for a in late['records']:
 assert a['producer']['conclusion']=='success' and a['producer']['head_sha']==state['head'];assert a['artifact']['digest']=='sha256:'+a['archive_sha256']
 for rel,h in a['mapping_hashes'].items():
  path=Path(a['stage'])/rel;assert sha(path)==h
  for line in path.read_text().splitlines()[1:]:
   key,desc=json.loads(line)
   if isinstance(desc,str):index.setdefault(key,[]).append(dict(descriptor=desc,artifact_id=str(a['artifact']['id']),stage=a['artifact']['name'],producer=a['producer'],mapping=str(path),mapping_sha256=h,zip_sha256=a['archive_sha256'],late_recovery_receipt_sha256=sha(late_path)))
records={};reproduced=[];unresolved=[]
for i,n in enumerate(names):
 p=P/'.lake/build/lib/lean'/Path(n[:-5]+'.trace');r=R/'.lake/build/lib/lean'/Path(n[:-5]+'.trace');td=json.loads(p.read_text());rec=dict(P_trace_sha256=sha(p),P_trace_keys=list(td),R_trace_sha256=sha(r) if r.exists() else None,native_key=td['depHash'],outputs=td['outputs'],candidates=[],matched=None)
 hits=index.get(td['depHash'],[]);tried=set()
 for h in hits:
  if h['descriptor'] in tried:continue
  tried.add(h['descriptor']);archive=C/'artifacts'/h['descriptor'];candidate=dict(h,archive_exists=archive.exists());rec['candidates'].append(candidate)
  if not archive.exists():continue
  scratch=L/'scratch';scratch.mkdir();lib=scratch/'lib';ir=scratch/'ir';lib.mkdir();ir.mkdir();payload=json.dumps([dict(file=str(archive),base=[str(lib),str(ir)],hash=td['depHash'])]);argv=[str(tool),'--jobs','1','-x','-j','-'];q=subprocess.run(argv,input=payload,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE);candidate.update(exit=q.returncode,archive_sha256=sha(archive))
  if q.returncode:
   candidate['error']=q.stderr;shutil.rmtree(scratch);continue
  traces=list(lib.rglob('*.trace'));assert len(traces)==1,traces;got=json.loads(traces[0].read_text());candidate['unpacked_trace']=got;candidate['trace_matches']=got==td;candidate['trace_bytes_exact']=traces[0].read_bytes()==p.read_bytes();payloads={};payload_ok=True
  if got.get('depHash')==td.get('depHash') and got.get('outputs')==td.get('outputs'):
   for ext,root in [('olean',lib),('ilean',lib),('c',ir)]:
    fs=list(root.rglob('*.'+ext));assert len(fs)==1,(n,ext,fs);dest=P/'.lake/build'/('ir' if ext=='c' else 'lib/lean')/Path(n[:-5]+'.'+ext);eq=dest.exists() and sha(dest)==sha(fs[0]);payloads[ext]=dict(extracted_sha256=sha(fs[0]),P_sha256=sha(dest) if dest.exists() else None,exact=eq);payload_ok &= eq
   candidate['payloads']=payloads
   if payload_ok:
    out=L/'reproduced-traces'/Path(n[:-5]+'.trace');out.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(traces[0],out);rec['matched']=dict(artifact_id=h['artifact_id'],stage=h['stage'],producer_head=h['producer']['head_sha'],producer_conclusion=h['producer']['conclusion'],archive=h['descriptor'],archive_sha256=candidate['archive_sha256'],mapping=h['mapping'],mapping_sha256=h['mapping_sha256'],trace_bytes_exact=candidate['trace_bytes_exact'],payloads=payloads);reproduced.append(n)
  shutil.rmtree(scratch)
  if rec['matched']:break
 if not rec['matched']:unresolved.append(n)
 records[n]=rec
 (L/'progress.json').write_text(json.dumps(dict(completed=len(records),reproduced=len(reproduced),unresolved=unresolved,records=records),indent=2)+'\n')
 if i%25==0:print('completed',i+1,'reproduced',len(reproduced),'unresolved',len(unresolved),flush=True)
report=dict(status='PROVENANCE_EVIDENCE_ONLY;ACCEPTANCE_STILL_ON_HOLD',tool=str(tool),tool_sha256=sha(tool),tool_version=subprocess.check_output([str(tool),'--version'],text=True).strip(),Lake_Module_source_sha256=sha(tool.parent.parent/'src/lean/lake/Lake/Build/Module.lean'),Lake_Common_source_sha256=sha(tool.parent.parent/'src/lean/lake/Lake/Build/Common.lean'),authoritative_recovery_state_sha256=sha(Recovery/'ci-recovery-state.json'),late_recovery_receipt_sha256=sha(late_path),origin_inventory_sha256=sha(D/'current8f-full-reverse-inventory-v1/unresolved901-archive-mapping-inventory-v1.json'),records=records,reproduced=reproduced,unresolved=unresolved,no_shared_write=True,no_build=True,current_keys_unverified=True,synthetic_labels_preserved=True,trace_schema_acceptance_unchanged=True,scratch_removed=not (L/'scratch').exists(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(L/'receipt.json').write_text(json.dumps(report,indent=2)+'\n');print('FINAL reproduced',len(reproduced),'unresolved',len(unresolved),flush=True)
