from pathlib import Path
import json,hashlib,subprocess,os,shutil,tempfile,psutil
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';D=E/'general7-main-candidate-v1/current8f-full-reverse-inventory-v1';G=B/'.worktrees/loop-20261102';roots={'P':E/'892-joint-current-context-v2/package','R':E/'direct-call-store-live-packet-v1/validation-package-v1'}
proposal=D/'donor49-reviewed-recovery-proposal-v1.json'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
assert sha(proposal)=='d4e6dbebd2e3991d523a5c99b01a5035697769c12741e0d547a8fe23bfb1fef3';m=json.loads(proposal.read_text());rows=m['rows'];assert len(rows)==49
for label,root in [('G',G),*roots.items()]:
 for f,h in (m['G_configs'] if label=='G' else m['configs'][label]).items():assert sha(root/f)==h,(label,f)
def writers():
 for z in psutil.process_iter(['pid']):
  try:
   if z.uids().real!=os.getuid():continue
   cmd=z.cmdline()
   if not cmd or Path(cmd[0]).name not in ['lean','lake','lake.orig','leanc']:continue
   cwd=z.cwd()
   if cwd.startswith(str(G)):raise AssertionError(('active G compiler',z.pid))
   for row in rows:
    if str(roots[row['donor']]/Path(row['target'].replace('.','/')+'.lean')) in cmd:raise AssertionError(('active exact donor writer',z.pid,row['target']))
  except (psutil.NoSuchProcess,psutil.AccessDenied):continue
writers();cmd=['/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake','--json','query','--no-build',*['+'+x['target']+':depHash' for x in rows]]
r=subprocess.run(cmd,cwd=G,env=dict(os.environ,LAKE_RESTORE_ARTIFACTS='false'),capture_output=True,text=True);(D/'donor49-precopy-key.stdout').write_text(r.stdout);(D/'donor49-precopy-key.stderr').write_text(r.stderr);assert r.returncode==0,r.returncode;keys=[json.loads(x) for x in r.stdout.splitlines() if x.strip()];assert keys==[x['native_key'] for x in rows]
for row in rows:
 root=roots[row['donor']];rel=Path(row['target'].replace('.','/')+'.lean');assert sha(root/rel)==sha(G/rel)==row['source_sha256']
 for f,h in row['copy_payloads'].items():assert sha(root/f)==h,(row['target'],f)
writers();saved=D/'preserved-donor49-loop-artifacts-v1';saved.mkdir();preserved={};copied={}
for row in rows:
 root=roots[row['donor']]
 for f,h in row['copy_payloads'].items():
  src=root/f;dest=G/f;assert dest.parent.resolve().is_relative_to(G.resolve()) and dest.parent.stat().st_uid==os.getuid();assert sha(src)==h
  if dest.exists():
   old=sha(dest);keep=saved/old
   if not keep.exists():shutil.copyfile(dest,keep)
   preserved[f]=old
  fd,tmp=tempfile.mkstemp(dir=dest.parent,prefix='.owned-donor49-');os.close(fd);shutil.copyfile(src,tmp);os.replace(tmp,dest);assert sha(dest)==h;copied[f]=h
partial={'proposal_sha256':sha(proposal),'preserved':preserved,'copied':copied,'targets':[x['target'] for x in rows],'setup_and_nobuild_unchanged':True,'normal_pending':True};(D/'donor49-owned-reuse-v1.json').write_text(json.dumps(partial,indent=2)+'\n')
with (D/'G49-normal-v1.log').open('w') as out:r=subprocess.run(['/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake','build','--no-build',*[x['target'] for x in rows]],cwd=G,env=dict(os.environ,LAKE_RESTORE_ARTIFACTS='false'),stdout=out,stderr=subprocess.STDOUT)
result={'exit':r.returncode,'targets':len(rows),'copied':len(copied),'preserved':len(preserved),'normal_log_sha256':sha(D/'G49-normal-v1.log'),'full326_and3381':'OPEN'};(D/'G49-normal-result-v1.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True);raise SystemExit(r.returncode)
