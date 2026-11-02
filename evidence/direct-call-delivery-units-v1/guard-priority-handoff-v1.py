from pathlib import Path
import datetime,json,psutil,os,signal,time
D=Path(__file__).resolve().parent;O=json.loads((D/'priority-handoff-owner-v1.json').read_text());statefile=D/'provider-large-slot-v1/state.json';S=json.loads(statefile.read_text());scheduler=S['scheduler'];birth=S['scheduler_birth'];resumed=False
while True:
 state=json.loads(statefile.read_text())
 if state.get('same_controller_resumed'):break
 try:
  p=psutil.Process(O['pid']);alive=p.create_time()==O['birth'] and p.status()!='zombie'
 except psutil.NoSuchProcess:alive=False
 if not alive:
  # A killed controller can leave a healthy provider running. Let that provider finish first.
  active=[]
  for p in psutil.process_iter(['name','status','cmdline']):
   a=p.info['cmdline'] or []
   if p.info['name']=='lean' and p.info['status']!='zombie' and any('current-foundation-package-v1/FV/Backend/Proof/StockSourceCallWitness.lean' in x for x in a):active.append(p.pid)
  if not active:
   q=psutil.Process(scheduler);assert q.create_time()==birth
   if q.status()=='stopped':os.kill(scheduler,signal.SIGCONT);resumed=True
   break
 time.sleep(1)
(D/'priority-handoff-guard-v1.json').write_text(json.dumps({'status':'completed','emergency_SIGCONT_needed':resumed,'scheduler':scheduler,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},indent=2)+'\n')
