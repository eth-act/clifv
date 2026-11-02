from pathlib import Path
import datetime,fcntl,json,os,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031'
lock=(E/'main870-cache-import.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
ready=json.loads((E/'small-slot-ready-state-v1.json').read_text());assert ready['status']=='inspected' and ready['selected']
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=V,text=True).strip()==ready['head']
main=Path('/proc/1849857/cmdline');assert main.exists() and b'lake-serial-build.py' in main.read_bytes() and b'--no-dedup' not in main.read_bytes()
mainenv={p.split(b'=',1)[0].decode():p.split(b'=',1)[1].decode() for p in Path('/proc/1849857/environ').read_bytes().split(b'\0') if b'=' in p}
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()));env.update(FV_ROOT=str(V),FV_MEMCAP='3G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2')
cache=env.get('FV_LAKE_CACHE') or env.get('LAKE_CACHE_DIR');assert cache and cache==(mainenv.get('FV_LAKE_CACHE') or mainenv.get('LAKE_CACHE_DIR')),'The scheduler must use the actual shared module locks'
script=(V/'scripts/lake-serial-build.py').read_text().replace('FV_MEMCAP="4G"','FV_MEMCAP="1G"')
script=script.replace('stale = bad & assumed','stale = bad & assumed\n        if stale:\n            raise RuntimeError("The small-slot target has stale dependencies; inspect readiness instead of starting another dependency writer: " + " ".join(sorted(stale)))')
assert 'if stale:' in script and 'FV_MEMCAP="4G"' not in script
helper=E/'small-slot-serial-build-v1.py';helper.write_text(script)
selected=E/'small-slot-selected-v1.txt';selected.write_text('\n'.join(ready['selected'])+'\n');logs=E/'small-slot-validation-v1';assert not logs.exists();logs.mkdir()
print('Use the existing module locks; caps12GiB +3GiB, one small compiler, two threads. No source changes or build restart.',flush=True)
with (logs/'scheduler.log').open('w') as out:
 subprocess.run(['nice','-n','10','python3',str(helper),'--root',str(V),'--out',str(logs/'modules'),'--budget','3G','--max-jobs','1','--max-cap','3G','--min-cap','3G','--default-cap','3G','--heavy','3G','--profile',str(V/'scripts/lake-module-peaks.tsv'),'--profile',str(V/'.lake/lake-module-peaks.tsv'),'--record',str(logs/'measured-peaks.tsv'),'--only',str(selected),*ready['selected']],cwd=V,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=V,text=True).strip()==ready['head']
receipt=dict(status='passed',head=ready['head'],modules=ready['selected'],main_scheduler_unchanged=1849857,main_cap='12GiB',small_slot_cap='3GiB',small_query_cap='1GiB',max_small_jobs=1,shared_module_locks=True,no_additional_cache_or_worktree=True,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(E/'small-slot-validation-state-v1.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
