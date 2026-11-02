from pathlib import Path
import datetime,fcntl,hashlib,json,os,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031'
lock=(E/'main870-cache-import.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
prior=json.loads((E/'sret-captured-exec-isolated-state-v4.json').read_text());assert prior['status']=='passed'
context=json.loads((E/'return-pin-consumer-isolated-state-v3.json').read_text());root=Path(context['isolated_package']);packet=E/'sret-captured-exec-packet-v1';manifest=json.loads((E/'sret-captured-exec-packet-v1.json').read_text());logs=E/'sret-captured-exec-canonical-isolated-kernel-v1';assert not logs.exists();logs.mkdir()
for name,digest in manifest['files'].items():
 data=(packet/name).read_bytes();assert hashlib.sha256(data).hexdigest()==digest;p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(V),FV_MEMCAP='3G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false');env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,env=env,text=True).strip()
target=root/'.lake/build/lib/lean/FV/E2E/SretCopyCapturedExec'
assert all(not Path(str(target)+s).exists() or Path(str(target)+s).stat().st_nlink==1 for s in ['.olean','.ilean','.olean.private','.olean.server','.c'])
with (logs/'kernel.log').open('w') as out:subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'lake','env','lean','--root='+str(root),str(root/'FV/E2E/SretCopyCapturedExec.lean'),'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c'],cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
with (logs/'audit-summary.log').open('w') as out:subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'python3',str(V/'scripts/axiom-audit.py'),'--cwd',str(root),'--log-dir',str(logs/'audit'),str(root/'scripts/audit/sret-captured-exec.lean')],cwd=V,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=V,text=True).strip()==prior['head']
receipt=dict(status='passed',head=prior['head'],source_hashes=manifest['files'],generic_roots=0,fixed_roots=2,requires_current_main_gates=True,full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(E/'sret-captured-exec-canonical-isolated-state-v1.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
