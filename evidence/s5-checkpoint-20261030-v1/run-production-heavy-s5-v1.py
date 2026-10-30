from pathlib import Path
import os,json,subprocess,datetime,psutil,time,hashlib
b=Path('/home/lee/clifv');r=b/'.worktrees/stock-memory-delivery-20261030';e=b/'.git/agent-evidence/stock-memory-20261029';env=dict(os.environ);env.update(json.loads((e/'author-env-v1.json').read_text()));env.update(FV_ROOT=str(r),FV_MEMCAP='10G',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LEAN_NUM_THREADS='2',CARGO_BUILD_JOBS='2');state=e/'production-heavy-s5-state-v1.json'
def save(status,**x):state.write_text(json.dumps(dict(status=status,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),worker_o_budget_gib=18,worker_a_budget_gib=14,temporary_loan_gib=2,**x),indent=2)+'\n')
try:
 save('waiting',dependency=2307417)
 while psutil.pid_exists(2307417):time.sleep(1)
 assert 'done FV.Backend.Proof.IselSzTTabH103 rc=0' in (e/'production-reverse-modules-v4/sched.log').read_text()
 try:
  scheduler=psutil.Process(2266696);assert 'lake-serial-build.py' in ' '.join(scheduler.cmdline());scheduler.terminate();scheduler.wait(timeout=15)
 except psutil.NoSuchProcess:pass
 try:psutil.Process(2266652).wait(timeout=15)
 except psutil.NoSuchProcess:pass
 save('running',phase='focused10GiB-retry')
 with (e/'production-heavy-s5-v1.log').open('w') as log:done=subprocess.run(['nice','-n','10',str(r/'scripts/memcap.sh'),'python3','scripts/lake-serial-build.py','--budget','10G','--max-jobs','1','--max-cap','10G','--default-cap','10G','--out',str(e/'production-heavy-s5-modules-v1'),'FV.Backend.Proof.IselCovTTabS5'],cwd=r,env=env,stdout=log,stderr=subprocess.STDOUT)
 save('passed' if done.returncode==0 else 'failed',returncode=done.returncode,loan_can_return=True)
 raise SystemExit(done.returncode)
except BaseException as error:
 if not isinstance(error,SystemExit):save('failed',error=repr(error),loan_can_return=True)
 raise
