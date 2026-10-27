from pathlib import Path
import subprocess,time,json,datetime,os
root=Path('/home/lee/clifv/.worktrees/stock-cfg-source-20261025');os.chdir(root)
head='52b22dc9e1cb4329ec160ade0f2e12a4312f2d51';pid=444027
status=Path('/tmp/stock-memory-recovery-20261027-v1.json')
def save(state,**extra):status.write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),head=head,state=state,**extra),indent=2)+'\n')
def frozen():
 assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()==head
 assert not subprocess.check_output(['git','status','--porcelain'],text=True).strip()
frozen();save('waiting-for-surviving-scheduler',pid=pid)
while Path(f'/proc/{pid}/cmdline').exists():
 cmd=Path(f'/proc/{pid}/cmdline').read_bytes()
 if b'lake-serial-build.py' not in cmd:break
 if Path(f'/proc/{pid}/stat').read_text().split()[2]=='Z':break
 time.sleep(10)
frozen();save('resuming-normal-gate-after-orphan-scheduler-exit')
r=subprocess.run(['taskset','-c','0-3','nice','-n','10','python3','scripts/stock-delivery-gates.py','resume','/tmp/stock-memory-reconciled-normal-manifest-v1.json','--root',str(root),'--out','/tmp/stock-memory-reconciled-normal-gates-v1'])
if r.returncode:save('failed-normal',returncode=r.returncode);raise SystemExit(r.returncode)
for label,script in [('validation','/tmp/stock-memory-reconciled-validation-queue-v1.py'),('post','/tmp/stock-memory-reconciled-post-queue-v1.py')]:
 frozen();save('running-'+label);r=subprocess.run(['python3',script])
 if r.returncode:save('failed-'+label,returncode=r.returncode);raise SystemExit(r.returncode)
save('passed-author-reconciliation-gates');print('RECONCILED_AUTHOR_GATES_PASS',flush=True)
