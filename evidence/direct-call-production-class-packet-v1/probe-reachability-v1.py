from pathlib import Path
import datetime,hashlib,json,os,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031';P=E/'direct-call-production-class-packet-v1';logs=P/'reachability-probe-v1';logs.mkdir()
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(V),FV_MEMCAP='1G',FV_MEMCAP_STATS=str(logs/'backend.mem'),FV_MEMCAP_UNIT='worker-o-result-call-reachability-v1',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false');env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,env=env,text=True).strip()
source=P/'ReachabilityProbeV1.lean'
with (logs/'probe.log').open('w') as out:
 result=subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'lake','env','lean',str(source)],cwd=V,env=env,stdout=out,stderr=subprocess.STDOUT)
receipt=dict(status='passed' if result.returncode==0 else 'failed',exit_code=result.returncode,context='read-only frozen V artifacts; diagnostic only, not current-main validation',source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),stats=(logs/'backend.mem').read_text() if (logs/'backend.mem').exists() else None,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(logs/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));raise SystemExit(result.returncode)
