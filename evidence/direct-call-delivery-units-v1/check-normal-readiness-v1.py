from pathlib import Path
import json,os,subprocess,datetime
D=Path(__file__).resolve().parent;S=json.loads((D/'current-foundation-snapshot-v1.json').read_text());P=Path(S['package']);L=D/'normal-readiness-v1';L.mkdir();env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(P),FV_MEMCAP='1G',FV_MEMCAP_UNIT='worker-o-foundation-readiness-v1',FV_MEMCAP_STATS=str(L/'scope.mem'),LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1')
cmd=['/home/lee/clifv/.worktrees/stock-extending-production-20261031/scripts/memcap.sh','lake','build','--no-build',*S['normal_check_roots']]
with (L/'lake.log').open('w') as f:r=subprocess.call(cmd,cwd=P,env=env,stdout=f,stderr=subprocess.STDOUT)
x={'status':'passed' if r==0 else 'not_ready','exit':r,'normal_provider_roots':len(S['normal_check_roots']),'no_compiler_allowed':True,'no_live_package_writes':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(L/'state.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x),flush=True);print((L/'lake.log').read_text()[-6000:]);raise SystemExit(r)
