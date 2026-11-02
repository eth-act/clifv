from pathlib import Path
import os,signal,json,datetime,re
matches=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:
  args=(p/'cmdline').read_bytes().split(b'\0')
  if b'scripts/lake-serial-build.py' in args and b'/tmp/stock-outcome-final-normal' in args and (p/'cwd').resolve()==Path.cwd():matches.append(int(p.name))
 except OSError:pass
assert len(matches)==1,matches
pid=matches[0];os.kill(pid,signal.SIGSTOP);p=Path('/proc')/str(pid);children=[int(x) for x in (p/'task'/str(pid)/'children').read_text().split()];active={}
for line in Path('/tmp/stock-outcome-final-normal-runner.log').read_text().splitlines():
 m=re.search(r'\b(start|done) (FV\S+)',line)
 if m:
  if m[1]=='start':active[m[2]]=line
  else:active.pop(m[2],None)
r={'controller_pid':pid,'children':children,'active_modules':list(active),'reason':'Drain dispatch only, keep healthy active kernel jobs. Drain overbroad full baseline replay after healthy optimizer workers finish. No optimizer sources changed in513; resume author verification on affected modules and keep full baseline observation separate. Partial prior normal successes remain evidence, not a completed-pass claim.','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};Path('/tmp/stock-outcome-final-normal-drain.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
