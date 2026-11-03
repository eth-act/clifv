from pathlib import Path
import json,subprocess,os
b=Path('/home/lee/clifv');d=b/'.git/agent-evidence/stock-memory-20261029/general7-main-candidate-v1/current8f-full-reverse-inventory-v1';targets=[r['target'] for r in json.loads((d/'additional-current-donor-candidates-v1.json').read_text())['rows']];assert len(targets)==24
root=b/'.git/agent-evidence/stock-memory-20261029/892-joint-current-context-v2/package';cmd=['/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake','build','--no-build',*targets]
with (d/'P24-normal.log').open('w') as f:r=subprocess.run(cmd,cwd=root,env=dict(os.environ,LAKE_RESTORE_ARTIFACTS='false'),stdout=f,stderr=subprocess.STDOUT)
(d/'P24-normal-result.json').write_text(json.dumps({'targets':targets,'exit':r.returncode,'scope':'P normal only; exact current-source/key binding is separately recorded'},indent=2)+'\n');print('P24 normal',r.returncode);raise SystemExit(r.returncode)
