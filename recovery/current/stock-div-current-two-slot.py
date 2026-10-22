from pathlib import Path
import os,signal,time,json,subprocess
p=402052
cmd=Path(f'/proc/{p}/cmdline').read_bytes().replace(b'\0',b' ').decode();assert 'stock-div-current-pr-build' in cmd
os.kill(p,signal.SIGSTOP)
def children():
 out=[]
 for f in Path('/proc').iterdir():
  if not f.name.isdigit():continue
  try:a=(f/'stat').read_text().rsplit(')',1)[1].split()
  except OSError:continue
  if int(a[1])==p and a[0]!='Z':out.append(int(f.name))
 return out
while children():time.sleep(1)
os.kill(p,signal.SIGTERM);os.kill(p,signal.SIGCONT)
print('Previous active proof completed; replacing only idle scheduler',flush=True)
E=os.environ.copy();E.update(json.load(open('/tmp/stock-div-release-env.json')));E['FV_MEMCAP']='8G'
with open('/tmp/stock-div-current-final-pr-build.log','w') as f:r=subprocess.run(['python3','scripts/lake-serial-build.py','--budget','16G','--max-jobs','2','--max-cap','16G','--default-cap','3G','--only','/tmp/stock-div-current-pr-needed.txt','--out','/tmp/stock-div-current-final-pr-build','FV','FVTest'],env=E,stdout=f,stderr=subprocess.STDOUT)
print('current affected keys',r.returncode,flush=True)
if r.returncode:raise SystemExit(r.returncode)
r=subprocess.run(['python3','/tmp/stock-div-run-gates.py','current-normal'],env=E);raise SystemExit(r.returncode)
