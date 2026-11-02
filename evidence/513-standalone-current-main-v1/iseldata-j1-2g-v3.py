"""One approved IselData-only attempt with explicit-j1. Never continue the queue."""
from pathlib import Path
import datetime, hashlib, json, os, subprocess, time
import psutil

OUT=Path(__file__).resolve().parent
ROOT=Path('/home/lee/clifv')
E=OUT.parent
CTX=json.loads((OUT/'context.json').read_text())
assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='513-IselData-j1-2G'
logs=OUT/'iseldata-j1-2g-v3';assert not logs.exists();logs.mkdir()
package=Path(CTX['stages']['baseline']['package'])
library=package/'.lake/build/lib/lean'
source='FV/Backend/Proof/IselData.lean'
stem=library/Path(source).with_suffix('')
def sha(p):
    digest=hashlib.sha256()
    with Path(p).open('rb') as stream:
        for block in iter(lambda:stream.read(1024*1024),b''):digest.update(block)
    return digest.hexdigest()
old=json.loads((OUT/'kernel-v1/progress.json').read_text())['records']
passed=old[:-1]
assert len(passed)==119 and old[-1]['source']==source
assert all(item['exit']==0 for item in passed)
for item in passed:
    assert sha(package/item['source'])==item['source_sha256']
    path=library/Path(item['source']).with_suffix('')
    for suffix,h in item['outputs'].items():assert sha(str(path)+suffix)==h
assert sha(package/source)==CTX['stages']['baseline']['source_hashes'][source]
assert sha(CTX['lean_executable'])==CTX['lean_executable_sha256']
for item in CTX['external_imports'].values():assert sha(item['path'])==item['sha256']
for path in stem.parent.glob(stem.name+'.*'):
    if path.is_file() or path.is_symlink():path.unlink()
env=dict(os.environ)
for key in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','FV_LAKE_CACHE','LAKE_CACHE_DIR','LAKE_ARTIFACT_CACHE','LAKE_RESTORE_ARTIFACTS','FV_MEMCAP_OFF']:
    env.pop(key,None)
env.update(FV_MEMCAP='2G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',FV_ROOT=str(package),LEAN_PATH=str(library)+os.pathsep+CTX['toolchain_library'],FV_MEMCAP_STATS=str(logs/'memory.mem'),FV_MEMCAP_UNIT='worker-o-513-iseldata-j1-2g-v3')
command=[CTX['lean_executable'],'-j1','--root='+str(package),str(package/source),'-o',str(stem)+'.olean','-i',str(stem)+'.ilean','-c',str(stem)+'.c']
policy=E/'lean-thread-policy-probe-state-v2.json'
assert json.loads(policy.read_text())['observations'][1]['flags']==['-j1']
started=time.monotonic();samples=[]
with (logs/'lean.log').open('w') as stream:
    process=subprocess.Popen(['nice','-n','10',str(ROOT/'.worktrees/stock-extending-production-20261031/scripts/memcap.sh'),*command],cwd=package,env=env,stdout=stream,stderr=subprocess.STDOUT)
    while process.poll() is None:
        for item in psutil.process_iter(['pid','cmdline','num_threads','memory_info']):
            try:
                argv=item.info['cmdline'] or []
                if len(argv)>1 and argv[0]==CTX['lean_executable'] and str(package/source) in argv and item.info.get('memory_info') is not None:
                    samples.append({'seconds':time.monotonic()-started,'pid':item.pid,'os_threads':item.info['num_threads'],'rss_bytes':item.info['memory_info'].rss,'argv':argv})
            except (psutil.NoSuchProcess,psutil.AccessDenied):pass
        time.sleep(0.5)
    result=process.wait()
elapsed=time.monotonic()-started
stats=(logs/'memory.mem').read_text() if (logs/'memory.mem').exists() else 'missing'
outputs={}
if result==0:
    for suffix in ['.olean','.ilean','.olean.private','.olean.server','.ir','.c']:
        path=Path(str(stem)+suffix)
        if path.is_file():outputs[suffix]={'sha256':sha(path),'bytes':path.stat().st_size}
for item in passed:
    path=library/Path(item['source']).with_suffix('')
    for suffix,h in item['outputs'].items():assert sha(str(path)+suffix)==h
assert sha(package/source)==CTX['stages']['baseline']['source_hashes'][source]
record={'status':'passed' if result==0 else 'stopped_after_single_failure','base':CTX['base'],'candidate_tree':CTX['candidate_tree'],'source':source,'source_sha256':sha(package/source),'command':command,'LEAN_PATH':env['LEAN_PATH'],'exit':result,'elapsed_seconds':elapsed,'memstats':stats,'thread_policy_probe_sha256':sha(policy),'explicit_lean_worker_threads':1,'LEAN_NUM_THREADS':2,'OMP_NUM_THREADS':2,'observed_max_lean_os_threads':max((s['os_threads'] for s in samples),default=None),'thread_samples':samples,'outputs':outputs,'previous119_artifacts_verified_unchanged':True,'fresh_baseline_modules_passed':120 if result==0 else 119,'remaining_baseline_modules':104 if result==0 else 105,'candidate_kernels_run':0,'type_axiom_comparisons_run':0,'no_other_kernel_ran':True,'automatic_repeat':False,'automatic_budget_increase':False,'next':'Report checkpoint before any further command or queue continuation','full_affected_gates_passed':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(OUT/'iseldata-j1-2g-state-v3.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record[k] for k in ['status','source','exit','elapsed_seconds','memstats','explicit_lean_worker_threads','observed_max_lean_os_threads','fresh_baseline_modules_passed','no_other_kernel_ran']}),flush=True)
raise SystemExit(result if result>0 else (1 if result<0 else 0))
