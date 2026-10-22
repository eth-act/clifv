from pathlib import Path
import os,signal,time,json,subprocess,re,datetime
parent=479609;cmd=Path(f'/proc/{parent}/cmdline').read_bytes().replace(b'\0',b' ').decode();assert 'stock-div-current-final-pr-build' in cmd;os.kill(parent,signal.SIGSTOP)
# Stop the idle dependent waiter only; it has not run any validation cohort.
waiter=534740
if Path(f'/proc/{waiter}/cmdline').exists():
 cmd=Path(f'/proc/{waiter}/cmdline').read_bytes().replace(b'\0',b' ').decode();assert 'stock-div-current-consumer-gates' in cmd
 os.kill(waiter,signal.SIGTERM)
Path('/tmp/stock-div-current-normal-worker-pid.json').write_text(json.dumps({'pid':os.getpid(),'script':'stock-div-current-cap-adjust.py'}))
def children():
 result=[]
 for f in Path('/proc').iterdir():
  if not f.name.isdigit():continue
  try:a=(f/'stat').read_text().rsplit(')',1)[1].split()
  except OSError:continue
  if int(a[1])==parent and a[0]!='Z':result.append(int(f.name))
 return result
print('Letting active generated-helper proof finish; then solo6G retry and6G minimum for remaining modules',flush=True)
while children():time.sleep(1)
os.kill(parent,signal.SIGTERM);os.kill(parent,signal.SIGCONT)
E=os.environ.copy();E.update(json.load(open('/tmp/stock-div-release-env.json')));E['FV_MEMCAP']='6G'
log=Path('/tmp/stock-div-current-preparation-solo-retry.log')
with log.open('w') as f:r=subprocess.run(['python3','scripts/lake-time.py','/tmp/stock-div-current-preparation-solo-retry.time','scripts/memcap.sh','lake','build','FV.Backend.Proof.StockPrepareInputs'],env=E,stdout=f,stderr=subprocess.STDOUT)
print('required solo preparation retry',r.returncode,flush=True)
if r.returncode:raise SystemExit(r.returncode)
needed=set(Path('/tmp/stock-div-current-pr-needed.txt').read_text().splitlines());done=set()
for name in ['stock-div-current-pr-build.log','stock-div-current-final-pr-build.log']:
 done |= set(re.findall(r'done (\S+) rc=0',Path('/tmp',name).read_text()))
pending=needed-done;Path('/tmp/stock-div-current-remaining-needed.txt').write_text('\n'.join(sorted(pending))+'\n')
Path('/tmp/stock-div-current-cap-reconciliation.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'candidate':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'full_affected_key_scope':len(needed),'previous_successes':sorted(done&needed),'remaining':sorted(pending),'solo_retry_log':str(log),'reason':'Two confirmed 3GiB cgroup cap failures; raise minimum allocation to6GiB inside unchanged16GiB/max2 aggregate. Preserve all successful earlier modules and healthy helper state.'},indent=2)+'\n')
with open('/tmp/stock-div-current-remaining-build.log','w') as f:r=subprocess.run(['python3','scripts/lake-serial-build.py','--budget','16G','--max-jobs','2','--max-cap','16G','--default-cap','6G','--only','/tmp/stock-div-current-remaining-needed.txt','--out','/tmp/stock-div-current-remaining-build','FV','FVTest'],env=E,stdout=f,stderr=subprocess.STDOUT)
print('remaining affected module refresh',r.returncode,flush=True)
if r.returncode:raise SystemExit(r.returncode)
E['FV_MEMCAP']='8G';r=subprocess.run(['python3','/tmp/stock-div-run-gates.py','current-normal'],env=E);raise SystemExit(r.returncode)
