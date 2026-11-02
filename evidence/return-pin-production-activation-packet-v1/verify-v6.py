from pathlib import Path
import datetime,fcntl,hashlib,json,os,re,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031';packet=E/'return-pin-production-activation-packet-v1';prior_root=E/'return-pin-consumer-isolated-package-v1';prior=json.loads((E/'return-pin-consumer-isolated-state-v3.json').read_text())
lock=(E/'main870-cache-import.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=V,text=True).strip()=='a4c0726d46c5908b4ac06cf797ee939af8644703'
root=packet/'validation-package-v1';lib=root/'.lake/build/lib/lean';context=json.loads((packet/'kernel-v1/context.json').read_text());ordered=[]
for name in context['modules']:
 local=packet/name
 if local.exists():
  data=local.read_bytes();target=root/name
  if target.read_bytes()!=data:
   target.write_bytes(data)
   for suffix in ['.olean','.ilean','.olean.private','.olean.server','.c']:
    artifact=Path(str(lib/Path(name).with_suffix(''))+suffix)
    if artifact.exists():artifact.unlink()
  context['source_hashes'][name]=hashlib.sha256(data).hexdigest()
 if not (lib/Path(name).with_suffix('.olean')).exists():ordered.append(name)
print('Remaining modules:',len(ordered),flush=True)
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(V),FV_MEMCAP='3G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false');env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,env=env,text=True).strip();logs=packet/'kernel-v6';assert not logs.exists();logs.mkdir();context['status']='running';(logs/'context.json').write_text(json.dumps(context,indent=2)+'\n');print('Rebuild modules:',len(ordered),flush=True)
for idx,name in enumerate(ordered):
 env['FV_MEMCAP_STATS']=str(logs/(name.replace('/','_')+'.mem'));env['FV_MEMCAP_UNIT']='worker-o-activation-v6-'+str(idx)
 target=lib/Path(name).with_suffix('');target.parent.mkdir(parents=True,exist_ok=True)
 with (logs/(name.replace('/','_')+'.log')).open('w') as out:subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'lake','env','lean','--root='+str(root),str(root/name),'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c'],cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
 print('KERNEL',name,'passed',flush=True)
with (logs/'audit-summary.log').open('w') as out:subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'python3',str(V/'scripts/axiom-audit.py'),'--cwd',str(root),'--log-dir',str(logs/'audit'),str(root/'scripts/audit/return-pin-production.lean'),str(root/'scripts/audit/return-pin-production-witness.lean')],cwd=V,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=V,text=True).strip()==context['head'];context.update(status='passed',generic_roots=3,fixed_roots=2,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(packet/'generic-state-v6.json').write_text(json.dumps(context,indent=2)+'\n');print('Production activation modules and mixed-mode witnesses passed.',flush=True)
