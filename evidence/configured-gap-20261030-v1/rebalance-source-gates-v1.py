from pathlib import Path
import psutil,time,subprocess,json,re,datetime
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029';state=e/'source-gate-rebalance-state-v1.json';records=[]
targets=[dict(name='production',module='FV.Backend.Proof.IselPrgTab',pid=2099566,scheduler=2044289,watcher=2044012,log='production-reverse-modules-v3/sched.log',label='production-reverse-gates-v4',recipe='run-production-reverse-gates-v4.py'),dict(name='captured',module='FV.Backend.Proof.IselPrgTabT',pid=2219236,scheduler=2051139,watcher=2051023,log='captured-current-consumer-modules-v2/sched.log',label='captured-current-consumers-v3',recipe='run-captured-current-consumers-v3.py')]
def save(status,**x):state.write_text(json.dumps(dict(status=status,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),records=records,pending=[x['name'] for x in targets],**x),indent=2)+'\n')
try:
 save('waiting',reason='Preserve healthy current table builds, then use8GiB per lane within existing16GiB allocation')
 while targets:
  for target in targets[:]:
   if psutil.pid_exists(target['pid']):continue
   log=(e/target['log']).read_text()
   if 'done '+target['module']+' rc=0' not in log:
    if psutil.pid_exists(target['scheduler']):continue
    raise RuntimeError(('Current module did not pass',target))
   try:
    scheduler=psutil.Process(target['scheduler']);assert 'lake-serial-build.py' in ' '.join(scheduler.cmdline());scheduler.terminate();scheduler.wait(timeout=15)
   except psutil.NoSuchProcess:pass
   try:psutil.Process(target['watcher']).wait(timeout=15)
   except psutil.NoSuchProcess:pass
   done=subprocess.run(['ai-coord','watch','--label',target['label'],'--','python3',str(e/target['recipe'])],cwd=b,text=True,capture_output=True,check=True);match=re.search(r'runner pid (\d+)',done.stdout);assert match,done.stdout
   records.append(dict(name=target['name'],previous_watcher=target['watcher'],new_watcher=int(match.group(1)),label=target['label'],stdout=done.stdout,preserved_module=target['module'],new_budget='8G'));targets.remove(target);save('waiting' if targets else 'passed')
  if targets:time.sleep(1)
except BaseException as error:save('failed',error=repr(error));raise
