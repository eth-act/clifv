from pathlib import Path
import os,signal,json
root=Path.cwd();found=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit() or int(p.name)==os.getpid():continue
 try:
  cmd=(p/'cmdline').read_bytes().split(b'\0');cwd=(p/'cwd').resolve();wait=(p/'wchan').read_text();children=(p/'task'/p.name/'children').read_text().strip()
  if cwd==root and cmd[:2]==[b'python3',b'-'] and 'nanosleep' in wait and not children:found.append({'pid':int(p.name),'cwd':str(cwd),'wait':wait,'children':children})
 except (OSError,ValueError):pass
assert len(found)==1,found
assert not Path('/tmp/stock-outcome-normal-exit.json').exists(),'Initial build already finished; reassess before stopping anything'
Path('/tmp/stock-outcome-waiter-replacement.json').write_text(json.dumps({'action':'Stop only sleeping follow-up orchestrator before its obsolete cached replay; initial healthy build remains running. Reconcile build-only main update after initial build ends, then use upstream batch replay.','waiter':found[0]},indent=2)+'\n');os.kill(found[0]['pid'],signal.SIGTERM);print(found[0])
