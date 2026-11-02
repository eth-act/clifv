from pathlib import Path
import os,signal,json,datetime,hashlib,re
pid=941064;p=Path('/proc')/str(pid);cmd=(p/'cmdline').read_bytes().split(b'\0');assert b'scripts/lake-serial-build.py' in cmd and b'/tmp/stock-outcome-normal' in cmd;assert (p/'cwd').resolve()==Path.cwd();os.kill(pid,signal.SIGSTOP)
children=[int(x) for x in (p/'task'/str(pid)/'children').read_text().split()];assert children,'No active children: reassess drain'
records=[]
for child in children:
 q=Path('/proc')/str(child);records.append({'pid':child,'stat':(q/'stat').read_text(),'command':(q/'cmdline').read_bytes().replace(b'\0',b' ').decode()})
active={}
for line in Path('/tmp/stock-outcome-normal-runner.log').read_text().splitlines():
 m=re.search(r'\b(start|done) (FV\S+)',line)
 if m:
  if m[1]=='start':active[m[2]]=line
  else:active.pop(m[2],None)
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'controller_pid':pid,'controller_argv_sha256':hashlib.sha256((p/'cmdline').read_bytes()).hexdigest(),'state':'dispatch paused; healthy worker children continue; terminate controller only after every active worker finishes','children':records,'active_modules':list(active)};Path('/tmp/stock-outcome-controller-drain.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items() if k!='children'});print('active child pids',children)
