from pathlib import Path
import datetime,hashlib,json,os,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031';P=E/'return-pin-typed-proof-packet-v1';R=E/'return-pin-production-activation-packet-v1/validation-package-v2';logs=P/'kernel-v1';logs.mkdir();lib=R/'.lake/build/lib/lean'
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(V),FV_MEMCAP='3G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false');env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,env=env,text=True).strip()
modules=['FV/E2E/TypedProductionChecks.lean','FVTest/E2E/TypedLinkProofWith.lean','FVTest/E2E/LinkCheckMain.lean'];hashes={}
for i,name in enumerate(modules):
 source=R/name;source.parent.mkdir(parents=True,exist_ok=True);source.write_bytes((P/name).read_bytes());hashes[name]=hashlib.sha256(source.read_bytes()).hexdigest();target=lib/Path(name).with_suffix('');target.parent.mkdir(parents=True,exist_ok=True)
 for suffix in ['.olean','.ilean','.olean.private','.olean.server','.c']:
  f=Path(str(target)+suffix)
  if f.exists():f.unlink()
 env['FV_MEMCAP_STATS']=str(logs/(str(i)+'.mem'));env['FV_MEMCAP_UNIT']='worker-o-typed-proof-v1-'+str(i)
 with (logs/(str(i)+'.log')).open('w') as out:subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'lake','env','lean','--root='+str(R),str(source),'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c'],cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
 print(name,'passed',flush=True)
with (logs/'audit.log').open('w') as out:subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'python3',str(V/'scripts/axiom-audit.py'),'--cwd',str(R),'--log-dir',str(logs/'audit'),str(P/'scripts/audit/typed-production.lean')],cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
(P/'state-v1.json').write_text(json.dumps(dict(status='passed',generic_roots=4,source_hashes=hashes,isolated_package=str(R),requires_current_main_gates=True,full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat()),indent=2)+'\n');print('Typed adapters and emitter passed.',flush=True)
