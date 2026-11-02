from pathlib import Path
import datetime,fcntl,hashlib,json,os,re,subprocess,time
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031'
while True:
 try:command=Path('/proc/2060338/cmdline').read_bytes()
 except FileNotFoundError:break
 if b'return-pin-generated-isolated-v3' not in command:break
 time.sleep(10)
generated=json.loads((E/'return-pin-generated-isolated-state-v3.json').read_text());assert generated['status']=='passed'
lock=(E/'main870-cache-import.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
root=Path(generated['isolated_package']);lib=root/'.lake/build/lib/lean';logs=E/'sret-captured-exec-isolated-kernel-v2';assert not logs.exists();logs.mkdir()
packets=['sret-symbolic-heap-packet-v4','sret-exec-entry-packet-v1','sret-exec-boundary-packet-v2','sret-result-bytes-packet-v2','sret-exec-result-bytes-packet-v1','return-pin-routed-packet-v1']
hashes={};audits=[]
for packet in packets:
 manifest=json.loads((E/(packet+'.json')).read_text())
 for name,digest in manifest['files'].items():
  assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest
  hashes[name]=digest
  if name.startswith('scripts/audit/'):audits.append(name)
name='FV/E2E/SretCopyCapturedExec.lean';data=(E/'WorkerOSretCapturedExecDraftV2.lean').read_bytes();(root/name).write_bytes(data);hashes[name]=hashlib.sha256(data).hexdigest();ordered=[name]
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(V),FV_MEMCAP='3G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false')
env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,env=env,text=True).strip()
# Never overwrite a hardlinked import: these modules are owned new outputs.
for name in ordered:
 target=lib/Path(name).with_suffix('');target.parent.mkdir(parents=True,exist_ok=True)
 for suffix in ['.olean','.ilean','.olean.private','.olean.server','.c']:
  path=Path(str(target)+suffix)
  if path.exists():path.unlink()
 with (logs/(Path(name).stem+'.log')).open('w') as out:
  subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'lake','env','lean','--root='+str(root),str(root/name),'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c'],cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
 print('KERNEL',name,'passed',flush=True)
# Check old binary variants in the same actual package context.
headers=json.loads((E/'return-pin-binary-old-headers-v1.json').read_text());binary_manifest=json.loads((E/'return-pin-binary-packet-v1.json').read_text());declarations='\n'.join((root/n).read_text() for n in binary_manifest['files'] if n.startswith('FV/'));assert len(headers)==25 and all(h in declarations for h in headers.values())
audit=root/'scripts/audit/sret-captured-exec.lean';audit.write_text('import FV.E2E.SretCopyCapturedExec\n\n#print axioms E2E.SretCapturedEntry.captured_entry -- witness: native_decide\n#print axioms E2E.SretCapturedEntry.captured_exec_bytes -- witness: native_decide\n');audits.append(str(audit));audits.append(str(E/'return-pin-binary-old-audit-v1.lean'))
for name in audits:
 source=Path(name) if Path(name).is_absolute() else root/name;label=source.stem
 with (logs/(label+'-audit-summary.log')).open('w') as out:
  subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'python3',str(V/'scripts/axiom-audit.py'),'--cwd',str(root),'--log-dir',str(logs/(label+'-audit')),str(source)],cwd=V,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
 print('AUDIT',label,'passed',flush=True)
def axioms(p):return {n:sorted(v.strip() for v in a.split(',') if v.strip()) for n,a in re.findall(r"'(\S+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",' '.join(p.read_text().split()))}
old=axioms(E/'return-pin-binary-old-audit-v1/return-pin-binary-old-audit-v1.log');now=axioms(logs/'return-pin-binary-old-audit-v1-audit/return-pin-binary-old-audit-v1.log');assert len(old)==25 and now==old
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=V,text=True).strip()==generated['head']
receipt=dict(status='passed',head=generated['head'],source_hashes=hashes,modules=ordered,old_binary_headers_exact=25,old_binary_axiom_sets_exact=25,captured_execution='Both cleanup modes, original complete linked mixed program, arbitrary symbolic source bytes, all sixteen destination and source bytes',requires_current_main_gates=True,full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(E/'sret-captured-exec-isolated-state-v2.json').write_text(json.dumps(receipt,indent=2)+'\n');print('Complete symbolic captured execution and old binary variants passed in the isolated package.',flush=True)
