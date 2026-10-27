from pathlib import Path
import json,subprocess,time,os
root=Path('/home/lee/clifv/.worktrees/stock-cfg-source-20261025');os.chdir(root)
assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()=='52b22dc9e1cb4329ec160ade0f2e12a4312f2d51'
p=Path('/tmp/stock-memory-reconciled-validation-queue-v1.json')
while True:
 r=json.loads(p.read_text())
 if r['state']=='passed':break
 if r['state']=='failed':raise SystemExit('Earlier queue failed; post checks held')
 time.sleep(10)
env=dict(os.environ,**json.load(open('/tmp/stock-memory-production-normal-manifest-v1.json'))['env']);env['FV_MEMCAP']='8G'
for script in ['contract-parity','reference-native','fixture-byte-binding','cli-native']:
 path='/tmp/stock-memory-reconciled-'+script+'-v1.py';log='/tmp/stock-memory-reconciled-'+script+'-v1.log'
 with open(log,'w') as f:r=subprocess.run(['taskset','-c','0,1','nice','-n','10','python3',path],cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
 if r.returncode:raise SystemExit('Failed '+path)
 print('PASS',script,flush=True)
print('ALL_RECONCILED_POST_CHECKS_PASS',flush=True)
