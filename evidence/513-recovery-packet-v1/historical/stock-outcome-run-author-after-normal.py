from pathlib import Path
import os,json,time,subprocess
Path('/tmp/stock-outcome-author-waiter.pid').write_text(str(os.getpid())+'\n')
while not Path('/tmp/stock-outcome-final-normal-check.json').exists():time.sleep(15)
r=json.load(open('/tmp/stock-outcome-final-normal-check.json'))
if r['exit']:print('Complete normal-key build needs repair',r,flush=True);raise SystemExit(1)
with open('/tmp/stock-outcome-gates-runner.log','w') as f:p=subprocess.run(['python3','scripts/stock-delivery-gates.py','run','/tmp/stock-outcome-manifest.json','--root',str(Path.cwd()),'--out','/tmp/stock-outcome-author'],stdout=f,stderr=subprocess.STDOUT)
Path('/tmp/stock-outcome-gates-exit.json').write_text(json.dumps({'exit':p.returncode,'head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()},indent=2)+'\n');print('Author gates',p.returncode,flush=True)
