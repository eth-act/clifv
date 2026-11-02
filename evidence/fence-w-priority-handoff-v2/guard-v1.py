from pathlib import Path
import datetime,json,os,psutil,signal,time
D=Path(__file__).resolve().parent
while not (D/'state.json').exists():time.sleep(.1)
s=json.loads((D/'state.json').read_text());pid=s['owner'];birth=s['owner_birth'];scheduler=s['scheduler'];sb=s['scheduler_birth'];cg=Path(s['scope_parent']);(D/'guard-armed.json').write_text(json.dumps({'owner':pid,'scheduler':scheduler,'guard':os.getpid()})+'\n')
emergency=False
while True:
 s=json.loads((D/'state.json').read_text())
 if s.get('same_controller_resumed'):break
 try:p=psutil.Process(pid);alive=p.create_time()==birth and p.status()!=psutil.STATUS_ZOMBIE
 except psutil.NoSuchProcess:alive=False
 if not alive:
  # A killed controller does not justify signalling a healthy compiler.
  busy=False
  for pattern in ['worker-o-wprio-v2-*.scope/cgroup.procs',f'fvb-{scheduler}-*.scope/cgroup.procs']:
   for f in cg.glob(pattern):
    try:busy=busy or bool(f.read_text().strip())
    except FileNotFoundError:pass
  if not busy:
   try:
    p=psutil.Process(scheduler);assert p.create_time()==sb
    if p.status()==psutil.STATUS_STOPPED:os.kill(scheduler,signal.SIGCONT);emergency=True
   except psutil.NoSuchProcess:pass
   break
 time.sleep(1)
(D/'guard-receipt.json').write_text(json.dumps({'status':'completed','emergency_resume':emergency,'scheduler':scheduler,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},indent=2)+'\n')
