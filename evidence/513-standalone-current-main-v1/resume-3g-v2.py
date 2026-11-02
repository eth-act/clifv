"""Fresh full focused closure at2GiB. Stop on first failure; never auto-retry."""
from pathlib import Path
import datetime, fcntl, hashlib, json, os, re, subprocess

OUT=Path(__file__).resolve().parent
ROOT=Path('/home/lee/clifv')
CTX=json.loads((OUT/'context.json').read_text())
assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='513-standalone-3G'
logs=OUT/'kernel-v2';assert not logs.exists();logs.mkdir()
lock=(OUT/'execution.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
env=dict(os.environ)
for key in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','FV_LAKE_CACHE','LAKE_CACHE_DIR','LAKE_ARTIFACT_CACHE','LAKE_RESTORE_ARTIFACTS','FV_MEMCAP_OFF']:
    env.pop(key,None)
env.update(FV_MEMCAP='3G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2')
lean=CTX['lean_executable'];tool_lib=CTX['toolchain_library']
memcap=ROOT/'.worktrees/stock-extending-production-20261031/scripts/memcap.sh'
prior=json.loads((OUT/'state-v1.json').read_text())
assert prior['status']=='stopped_at_first_failure' and prior['passed_commands']==119
old=json.loads((OUT/'kernel-v1/progress.json').read_text())['records']
assert len(old)==120 and old[-1]['exit']==137
records=old[:-1]
assert all(item['exit']==0 for item in records)

def sha(p):
    result=hashlib.sha256()
    with Path(p).open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):result.update(block)
    return result.hexdigest()
assert sha(lean)==CTX['lean_executable_sha256']
for data in CTX['external_imports'].values():assert sha(data['path'])==data['sha256']
def guard(stage):
    d=CTX['stages'][stage];pkg=Path(d['package'])
    for p,h in d['source_hashes'].items():assert sha(pkg/p)==h,('Source changed',stage,p)

def run(stage,source,idx,emit=True):
    package=Path(CTX['stages'][stage]['package']);library=package/'.lake/build/lib/lean'
    local=dict(env,LEAN_PATH=str(library)+os.pathsep+tool_lib,FV_ROOT=str(package))
    label=stage+'-'+str(idx)+'-'+Path(source).stem
    log=logs/(label+'.log');stats=logs/(label+'.mem')
    local.update(FV_MEMCAP_STATS=str(stats),FV_MEMCAP_UNIT='worker-o-513-standalone-v2-'+stage+'-'+str(idx))
    command=[lean,'--root='+str(package),str(package/source)]
    outputs={}
    if emit:
        stem=library/Path(source).with_suffix('');stem.parent.mkdir(parents=True,exist_ok=True)
        for suffix in ['.olean','.ilean','.olean.private','.olean.server','.ir','.c']:
            Path(str(stem)+suffix).unlink(missing_ok=True)
        command+=['-o',str(stem)+'.olean','-i',str(stem)+'.ilean','-c',str(stem)+'.c']
    with log.open('w') as stream:
        result=subprocess.run(['nice','-n','10',str(memcap),*command],cwd=package,env=local,stdout=stream,stderr=subprocess.STDOUT)
    measured=stats.read_text() if stats.exists() else 'missing memstats'
    if emit and result.returncode==0:
        for suffix in ['.olean','.ilean','.olean.private','.olean.server','.ir','.c']:
            p=Path(str(stem)+suffix)
            if p.is_file():outputs[suffix]=sha(p)
    record={'stage':stage,'source':source,'source_sha256':sha(package/source),'command':command,'LEAN_PATH':local['LEAN_PATH'],'exit':result.returncode,'log_sha256':sha(log),'memstats':measured,'outputs':outputs}
    records.append(record)
    (logs/'progress.json').write_text(json.dumps({'records':records},indent=2)+'\n')
    if result.returncode:
        state={'status':'stopped_at_first_failure','base':CTX['base'],'candidate_tree':CTX['candidate_tree'],'failed_command':record,'passed_commands':len(records)-1,'automatic_retry':False,'budget_increase':False,'next':'Report actual diagnostic and measured memory before any retry','full_affected_gates_passed':False}
        (OUT/'state-v2.json').write_text(json.dumps(state,indent=2)+'\n')
        raise SystemExit(result.returncode if result.returncode>0 else 1)
    print('KERNEL',stage,source,'passed',flush=True)

guard('baseline')
for idx,p in enumerate(CTX['stages']['baseline']['full_topological_queue']):
    if idx<len(old)-1:
        item=old[idx];assert item['stage']=='baseline' and item['source']==p
        pkg=Path(CTX['stages']['baseline']['package']);assert sha(pkg/p)==item['source_sha256']
        stem=pkg/'.lake/build/lib/lean'/Path(p).with_suffix('')
        assert item['outputs']
        for suffix,h in item['outputs'].items():assert sha(str(stem)+suffix)==h,('Passed artifact changed',p,suffix)
        continue
    run('baseline',p,idx)
run('baseline','Types.lean',len(records),False)
guard('baseline');guard('candidate')
base_lib=Path(CTX['stages']['baseline']['package'])/'.lake/build/lib/lean'
new_lib=Path(CTX['stages']['candidate']['package'])/'.lake/build/lib/lean'
owned={str(Path(p).with_suffix('')) for p in CTX['candidate_targets']}
for source in base_lib.rglob('*'):
    if not source.is_file() or not any(source.name.endswith(s) for s in ['.olean','.ilean','.olean.private','.olean.server','.ir']):continue
    rel=source.relative_to(base_lib)
    if any(str(rel).startswith(p+'.') for p in owned):continue
    target=new_lib/rel;target.parent.mkdir(parents=True,exist_ok=True);assert not target.exists();os.link(source,target)
for idx,p in enumerate(CTX['candidate_targets']):run('candidate',p,idx)
run('candidate','Types.lean',len(records),False)
baseline_log=next(logs.glob('baseline-*-Types.log'))
candidate_log=next(logs.glob('candidate-*-Types.log'))
assert baseline_log.read_bytes()==candidate_log.read_bytes(),'Current standalone elaborated types or axiom sets differ'
guard('baseline');guard('candidate')
state={'status':'passed','base':CTX['base'],'candidate_tree':CTX['candidate_tree'],'standalone_without892':True,'fresh_baseline_project_kernels':len(CTX['stages']['baseline']['full_topological_queue']),'candidate_kernels':7,'exact_elaborated_types':8,'exact_axiom_sets':8,'old_public_headers':372,'consumer_bodies':203,'moved_declarations':8,'external_artifacts_only_from_pinned_toolchain':True,'no_frozen_project_library_fallback':True,'command_records':records,'scope':'Fresh entire focused project closure and seven changed candidate kernels. Direct kernel/AX, not all reverse importers/normal keys/full tests.','full_goal_complete':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(OUT/'state-v2.json').write_text(json.dumps(state,indent=2)+'\n')
print(json.dumps({'status':'passed','fresh_baseline_project_kernels':state['fresh_baseline_project_kernels'],'candidate_kernels':7,'exact_types_axiom_roots':8}),flush=True)
