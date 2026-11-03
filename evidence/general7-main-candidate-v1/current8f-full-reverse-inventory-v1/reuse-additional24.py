from pathlib import Path
import json,hashlib,shutil,os,subprocess,tempfile
import psutil
b=Path('/home/lee/clifv');d=b/'.git/agent-evidence/stock-memory-20261029/general7-main-candidate-v1/current8f-full-reverse-inventory-v1';P=b/'.git/agent-evidence/stock-memory-20261029/892-joint-current-context-v2/package';G=b/'.worktrees/loop-20261102';candidates=json.loads((d/'additional-current-donor-candidates-v1.json').read_text())['rows'];rows=[dict(r,current_source_sha256=r['source_sha256'],donors={'P':{'trace_sha256':r['trace_sha256']}}) for r in candidates];assert len(rows)==24;assert json.loads((d/'P24-normal-result.json').read_text())['exit']==0
for process in psutil.process_iter(['pid']):
 try:
  if process.uids().real!=os.getuid():continue
  command=process.cmdline();cwd=process.cwd()
  if cwd.startswith(str(G)) and any(Path(x).name in ['lean','lake','leanc'] for x in command[:2]):raise AssertionError(('active loop compiler',process.pid))
 except (psutil.NoSuchProcess,psutil.AccessDenied):continue
old=d/'preserved-additional24-loop-artifacts-v1';old.mkdir(exist_ok=False);preserved={};copied={}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for row in rows:
 rel=Path(row['target'].replace('.','/'));assert sha(P/rel.with_suffix('.lean'))==row['current_source_sha256'];assert sha(G/rel.with_suffix('.lean'))==row['current_source_sha256'];trace=P/'.lake/build/lib/lean'/rel.with_suffix('.trace');assert sha(trace)==row['donors']['P']['trace_sha256'];assert json.loads(trace.read_text())['depHash']==row['key']
 for folder in ['.lake/build/lib/lean','.lake/build/ir']:
  srcParent=P/folder/rel.parent;destParent=G/folder/rel.parent;assert destParent.resolve().is_relative_to(G.resolve());assert destParent.stat().st_uid==os.getuid()
  for target in destParent.glob(rel.name+'.*'):
   if target.is_file():
    h=sha(target);saved=old/h
    if not saved.exists():shutil.copyfile(target,saved)
    preserved[str(target.relative_to(G))]=h
  for src in srcParent.glob(rel.name+'.*'):
   if not src.is_file():continue
   dest=destParent/src.name;fd,tmp=tempfile.mkstemp(dir=destParent,prefix='.owned-reuse-');os.close(fd);shutil.copyfile(src,tmp);os.replace(tmp,dest);h=sha(src);assert sha(dest)==h;copied[str(dest.relative_to(G))]=h
(d/'reuse24-artifacts-v1.json').write_text(json.dumps({'preserved_old_artifacts':preserved,'copied_current_artifacts':copied,'targets':rows,'scope':'exact fresh P provenance and actual P normal; actual G normal required next'},indent=2)+'\n')
cmd=['/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake','build','--no-build',*[r['target'] for r in rows]]
with (d/'G24-normal.log').open('w') as f:result=subprocess.run(cmd,cwd=G,env=dict(os.environ,LAKE_RESTORE_ARTIFACTS='false'),stdout=f,stderr=subprocess.STDOUT)
(d/'G24-normal-result.json').write_text(json.dumps({'exit':result.returncode,'copied':len(copied),'preserved':len(preserved)},indent=2)+'\n');print('G24 actual normal',result.returncode,'copied',len(copied),'preserved',len(preserved));raise SystemExit(result.returncode)
