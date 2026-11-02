from pathlib import Path
import datetime,fcntl,hashlib,json,os,re,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031'
lock=(E/'main870-cache-import.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
pre=json.loads((E/'return-pin-consumer-isolated-preflight-v1.json').read_text())
def git(*args):return subprocess.check_output(['git',*args],cwd=V,text=True).strip()
head=git('rev-parse','HEAD');assert head=='a4c0726d46c5908b4ac06cf797ee939af8644703' and not git('status','--porcelain')
root=E/'return-pin-consumer-isolated-package-v1';assert root.exists()
context=json.loads((E/'return-pin-consumer-isolated-kernel-v1/context.json').read_text())
logs=E/'return-pin-consumer-isolated-kernel-v2';assert not logs.exists();logs.mkdir()
manifest=json.loads((E/'return-pin-generated-proof-packet-v2.json').read_text())
for name,digest in manifest['files'].items():
 data=(E/'return-pin-generated-proof-packet-v2'/name).read_bytes();assert hashlib.sha256(data).hexdigest()==digest
 (root/name).write_bytes(data);context['source_hashes'][name]=digest
context['packets']=[p.replace('return-pin-generated-proof-packet-v1','return-pin-generated-proof-packet-v2') for p in context['packets']]
context['reused_kernel_log']='return-pin-consumer-isolated-kernel-v1'
ordered=context['modules'][context['modules'].index('FV/E2E/ReturnPinGeneratedStack.lean'):]
lib=root/'.lake/build/lib/lean'
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(V),LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',FV_MEMCAP='3G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2')
env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,env=env,text=True).strip()
audits=[n for n in context['source_hashes'] if n.startswith('scripts/audit/')]
for name in ordered:
 target=lib/Path(name).with_suffix('');target.parent.mkdir(parents=True,exist_ok=True)
 with (logs/(Path(name).stem+'.log')).open('w') as out:
  subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'lake','env','lean','--root='+str(root),str(root/name),'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c'],cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
 print('KERNEL',name,'passed',flush=True)
for name in audits:
 label=Path(name).stem
 with (logs/(label+'-audit-summary.log')).open('w') as out:
  subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'python3',str(V/'scripts/axiom-audit.py'),'--cwd',str(root),'--log-dir',str(logs/(label+'-audit')),str(root/name)],cwd=V,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
 print('AUDIT',name,'passed',flush=True)
assert git('rev-parse','HEAD')==head and not git('status','--porcelain')
context.update(status='passed',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),requires_current_main_gates=True)
(E/'return-pin-consumer-isolated-state-v2.json').write_text(json.dumps(context,indent=2)+'\n')
print('All candidate modules and unchanged audits passed. Current-main importer and publication gates remain required.',flush=True)
