from pathlib import Path
import hashlib,json,subprocess,os
X=Path(__file__).resolve().parent;D=X/'light-leaf-v2';P=X/'light-current8f-query-v1/package';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((D/'receipt.json').read_text());assert json.loads((D/'exit.json').read_text())['exit']==0;assert sha(P/'lakefile.toml')==r['canonical_config_sha256']
env=dict(os.environ);env.pop('FV_LAKE_CACHE',None);env.pop('FV_MEMCAP_OFF',None);env.update(LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',FV_MEMCAP='1G',FV_MEMCAP_UNIT='worker-o-outside-avoids-canonical-final-normal',FV_MEMCAP_STATS=str(D/'canonical-normal-memstats'))
T='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake';names=json.loads((X/'creator-classification155-v1/receipt.json').read_text())['records']
cmd=[T,'build','--no-build',*names,'FV.E2E.OutsideAvoids']
with (D/'canonical-normal156.log').open('w') as o:q=subprocess.run(['/home/lee/clifv/.worktrees/stock-extending-production-20261031/scripts/memcap.sh',*cmd],cwd=P,env=env,stdout=o,stderr=subprocess.STDOUT)
assert q.returncode==0
r.update(canonical_final_normal156_exit=q.returncode,canonical_final_normal156_log_sha256=sha(D/'canonical-normal156.log'),guard_restoration_sha256=sha(D/'guard-restored.json'),bounded_run_memstats=(D/'memstats').read_text(),canonical_normal_memstats=(D/'canonical-normal-memstats').read_text(),kernel_receipt_sha256=sha(D/'receipt.json'))
(D/'final-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print('final receipt',sha(D/'final-receipt.json'))
