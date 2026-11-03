from pathlib import Path
import json,subprocess,os
b=Path('/home/lee/clifv');d=b/'.git/agent-evidence/stock-memory-20261029/general7-main-candidate-v1/current8f-full-reverse-inventory-v1';targets=[n[:-5].replace('/','.') for n in json.loads((d.parent/'reverse81-archive-content-origin-v1/receipt.json').read_text())['reproduced']];root=b/'.worktrees/loop-20261102';cmd=['/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake','build','--no-build',*targets]
with (d/'archive76-normal-keys.stdout').open('w') as out,(d/'archive76-normal-keys.stderr').open('w') as err:r=subprocess.run(cmd,cwd=root,env=dict(os.environ,LAKE_RESTORE_ARTIFACTS='false'),stdout=out,stderr=err)
print('archive76-normal query exit',r.returncode);raise SystemExit(r.returncode)
