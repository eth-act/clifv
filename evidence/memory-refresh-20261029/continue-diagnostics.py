from pathlib import Path
import os,subprocess,time,json,re,shutil,datetime,signal
root=Path('/home/lee/clifv/.worktrees/stock-cfg-source-20261025');e=Path('/home/lee/clifv/.git/agent-evidence/stock-memory-20261029');os.chdir(root)
state=e/'diagnostic-state.json'
env=dict(os.environ,PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+os.environ.get('PATH',''),FV_LAKE_CACHE='/home/lee/clifv/.worktrees/driver-proof-resume/.lake/artifact-cache',FV_MEMCAP='8G',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LEAN_NUM_THREADS='2',CARGO_BUILD_JOBS='2')
def save(status,**extra):state.write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status=status,source_head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),**extra),indent=2)+'\n')
def wait_for(pid,part):
 save('waiting',pid=pid,purpose=part)
 while Path(f'/proc/{pid}/cmdline').exists():
  cmd=Path(f'/proc/{pid}/cmdline').read_bytes().replace(b'\0',b' ')
  if part.encode() not in cmd or Path(f'/proc/{pid}/stat').read_text().split()[2]=='Z':break
  time.sleep(10)
def run(label,argv,env):
 save('running',label=label)
 with (e/(label+'.log')).open('w') as log:
  p=subprocess.run(argv,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
 if p.returncode:raise RuntimeError(f'{label} exited {p.returncode}; inspect log, no pass claim')
try:
 if not (e/'ci-import-receipt.json').exists():
  wait_for(252789,'gh run download')
  stage=e/'ci-stage';assert (stage/'outputs.jsonl').is_file(),'CI stage absent/incomplete; inspect download log'
  assert shutil.disk_usage(root).free>=70*1024**3,'insufficient headroom for cache import'
  # Hold only our scheduler's dispatch loop, allowing its healthy children to
  # finish. Import the cache with no competing compiler; then resume dispatch.
  scheduler=Path('/proc/285322/cmdline');paused=False
  try:
   if scheduler.exists():
    command=scheduler.read_bytes().replace(b'\0',b' ')
    assert b'lake-serial-build.py' in command and str(e/'memory-class-build').encode() in command
    os.kill(285322,signal.SIGSTOP);paused=True;save('draining-healthy-children-for-cache-import')
    while True:
     live=[]
     for proc in Path('/proc').glob('[0-9]*'):
      try:
       st=(proc/'stat').read_text().split()
       if st[3]=='285322' and st[2]!='Z':live.append(proc.name)
      except (FileNotFoundError,ProcessLookupError,PermissionError):pass
     if not live:break
     time.sleep(10)
   run('ci-unstage',['scripts/memcap.sh','lake','cache','unstage',str(stage)],env)
  finally:
   if paused and scheduler.exists():os.kill(285322,signal.SIGCONT)
  (e/'ci-import-receipt.json').write_text(json.dumps(dict(state='passed',artifact=12891485845,run=40769795369,base='62fa93f0f46804c97a02c0de8ac9332ea51f41aa',import_log=str(e/'ci-unstage.log'),purpose='content-addressed cache import only; not current-source validation'),indent=2)+'\n')
  shutil.rmtree(stage)
 wait_for(285322,'lake-serial-build.py')
 log=(e/'memory-class-build.log').read_text();assert re.search(r'END (\d+)/\1 ok',log),'source-class diagnostic did not pass'
 env['FV_MEMCAP']='16G'
 run('memory-consumers-build',['python3','scripts/lake-serial-build.py','--budget','16G','--max-jobs','2','--max-cap','16G','--out',str(e/'memory-consumers-build'),'FV.Backend.Proof.StockMemoryCompatibility','FV.E2E.StockMemoryPairedFunctionWitness','FV.E2E.StockMemoryNI','FV.E2E.CompiledSemanticNI','FV.E2E.SemanticNIBoundary','FVTest.Backend.Lowering.StockMemoryProductionLinked'],env)
 assert re.search(r'END (\d+)/\1 ok',(e/'memory-consumers-build.log').read_text()),'missing scheduler pass'
 save('targeted-diagnostics-passed',limits='Not full author gates or merge approval')
except Exception as error:
 save('failed',error=str(error));raise
