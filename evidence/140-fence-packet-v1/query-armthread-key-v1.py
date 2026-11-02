from pathlib import Path
import os,subprocess,json,time
F=Path(__file__).resolve().parent;P=F/'package';O=F/'runs/armthread-key-query-v1';O.mkdir(exist_ok=False);env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH']:env.pop(k,None)
env.update(FV_ROOT=str(P),FV_MEMCAP='1G',FV_MEMCAP_UNIT='worker-o-fence-armthread-key-query-v1',FV_MEMCAP_STATS=str(O/'stats.mem'),LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1')
lake='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake';cmd=[lake,'query','--json','--no-build','+FV.Concurrency.ArmThread:depHash'];start=time.time()
with (O/'stdout.log').open('w') as out,(O/'stderr.log').open('w') as err:p=subprocess.run(['/home/lee/clifv/.worktrees/stock-extending-production-20261031/scripts/memcap.sh',*cmd],cwd=P,env=env,stdout=out,stderr=err)
(O/'state.json').write_text(json.dumps({'argv':cmd,'exit':p.returncode,'seconds':time.time()-start,'no_build':True,'stats':(O/'stats.mem').read_text()},indent=2)+'\n');raise SystemExit(p.returncode)
