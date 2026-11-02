from pathlib import Path
import os,signal,json,datetime,re
matches=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:
  args=(p/'cmdline').read_bytes().split(b'\0')
  if b'/tmp/stock-outcome-upstream-lake-serial-build.py' in args and b'/tmp/stock-outcome-independent-bounded' in args and (p/'cwd').resolve()==Path.cwd():matches.append(int(p.name))
 except OSError:pass
assert len(matches)==1,matches
pid=matches[0];os.kill(pid,signal.SIGSTOP);p=Path('/proc')/str(pid);children=[int(x) for x in (p/'task'/str(pid)/'children').read_text().split()];active={}
for line in Path('/tmp/stock-outcome-independent-bounded-runner.log').read_text().splitlines():
 m=re.search(r'\b(start|done) (FV\S+)',line)
 if m:
  if m[1]=='start':active[m[2]]=line
  else:active.pop(m[2],None)
r={'controller_pid':pid,'children':children,'active_modules':list(active),'reason':'Drain dispatch only, keep healthy active kernel jobs. Original5GiB worker finished; drain this remaining healthy linker proof before reconciling516 and the full16GiB/max2 final pass. Partial prior normal successes remain evidence, not a completed-pass claim.','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};Path('/tmp/stock-outcome-independent-bounded-drain.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
