from pathlib import Path
import json,os,hashlib,subprocess,time,psutil,shutil
F=Path(__file__).resolve().parent;P=F/'package';O=F/'runs/allocated-match-leaf-normal-v1';O.mkdir(exist_ok=False);S=json.loads((F/'import-snapshot-v16.json').read_text());assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='fence-leaf-3G'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();leaf='FV.E2E.RegLevelCorrectU';stem=P/'.lake/build/lib/lean/FV/E2E/RegLevelCorrectU';ir=P/'.lake/build/ir/FV/E2E/RegLevelCorrectU';env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(k,None)
env.update(FV_ROOT=str(P),LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1');lake=Path(S['lean_executable']).with_name('lake');env['PATH']=str(lake.parent)+':'+env['PATH'];memcap='/home/lee/clifv/.worktrees/stock-extending-production-20261031/scripts/memcap.sh'
for m,row in S['modules'].items():assert sha(P/row['source'])==row['sha256']
for rel,h in S['artifacts'].items():assert sha(P/rel)==h,rel
records=[]
def run(name,cmd,cap):
 env.update(FV_MEMCAP=cap,FV_MEMCAP_UNIT='worker-o-fence-'+name,FV_MEMCAP_STATS=str(O/(name+'.mem')));start=time.time();seen={}
 with (O/(name+'.log')).open('w') as log:
  proc=subprocess.Popen([memcap,*cmd],cwd=P,env=env,stdout=log,stderr=subprocess.STDOUT)
  while proc.poll() is None:
   try:
    for child in psutil.Process(proc.pid).children(recursive=True):
     try:
      if child.name()=='lean':
       args=child.cmdline()
       if not args:continue
       assert '-j1' in args,('Unexpected Lean thread args',args)
       item=seen.setdefault(str(child.pid),{'argv':args,'max_os_threads':0});item['max_os_threads']=max(item['max_os_threads'],child.num_threads())
     except (psutil.NoSuchProcess,psutil.AccessDenied):pass
   except (psutil.NoSuchProcess,psutil.AccessDenied):pass
   time.sleep(.05)
 row={'name':name,'argv':cmd,'cap':cap,'exit':proc.returncode,'seconds':time.time()-start,'memstats':(O/(name+'.mem')).read_text(),'lean_processes':seen};records.append(row);(O/'state.json').write_text(json.dumps({'status':'running' if proc.returncode==0 else 'failed_stop','records':records},indent=2)+'\n');assert proc.returncode==0,('Stop on exact diagnostic/cap failure',row);return row
baseline=[m for m in S['modules'] if m!=leaf];assert len(baseline)==920
run('baseline920-normal-no-build',[str(lake),'build','--no-build',*baseline],'1G')
config=P/'lakefile.toml';old=config.read_bytes();(O/'lakefile-before-j1.toml').write_bytes(old);assert b'weakLeanArgs = ["-j2"' in old;changed=old.replace(b'weakLeanArgs = ["-j2"',b'weakLeanArgs = ["-j1"',1);config.write_bytes(changed)
provisional={}
for base in [stem,ir]:
 for p in base.parent.glob(base.name+'.*'):
  if p.is_file() or p.is_symlink():provisional[str(p.relative_to(P))]=sha(p);p.unlink()
(O/'provisional-output-hashes.json').write_text(json.dumps(provisional,indent=2)+'\n')
try:
 row=run('allocated-match-normal-leaf',[str(lake),'build','+FV.E2E.RegLevelCorrectU:leanArts'],'3G')
finally:config.write_bytes(old)
assert row['lean_processes'],'No actual compiler observed'
for base in [stem,ir]:
 for p in base.parent.glob(base.name+'.*'):
  if p.is_file():S['artifacts'][str(p.relative_to(P))]=sha(p)
S['status']='current_leaf_built_requires_full_normal_check';S['allocated_match_leaf_normal_gate']={'record':row,'baseline920':records[0],'leaf_source_sha256':sha(P/S['modules'][leaf]['source']),'weak_j1_config_sha256':hashlib.sha256(changed).hexdigest(),'original_config_restored':sha(config)==hashlib.sha256(old).hexdigest(),'cache_writes':False,'live_package_writes':False,'borrowed_2GiB_released_after_leaf':True}
(F/'import-snapshot-v17.json').write_text(json.dumps(S,indent=2)+'\n');v=(F/'verify-access-v16.py').read_text().replace('import-snapshot-v16.json','import-snapshot-v17.json').replace('import-normal-check-v16.json','import-normal-check-v17.json');(F/'verify-access-v17.py').write_text(v)
(O/'state.json').write_text(json.dumps({'status':'passed_leaf_borrowed_2GiB_released','records':records,'source_sha256':sha(P/S['modules'][leaf]['source']),'original_config_restored':True,'full_normal_check_required':True},indent=2)+'\n');print('Leaf passed; borrowed2GiB released; no other compiler ran')
