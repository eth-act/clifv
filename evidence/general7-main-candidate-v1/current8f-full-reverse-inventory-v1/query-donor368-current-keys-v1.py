from pathlib import Path
import json,subprocess,os
b=Path('/home/lee/clifv');d=b/'.git/agent-evidence/stock-memory-20261029/general7-main-candidate-v1/current8f-full-reverse-inventory-v1';targets=[x['target'] for x in json.loads((d/'complete3381-reviewed-origin-donor-disposition-v3.json').read_text())['rows'] if x['classification']=='proper source/key candidate donor; actual checks required'];root=b/'.worktrees/loop-20261102';cmd=['/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake','--json','query','--no-build',*['+'+m+':depHash' for m in targets]]
with (d/'donor368-current-keys.stdout').open('w') as out,(d/'donor368-current-keys.stderr').open('w') as err:r=subprocess.run(cmd,cwd=root,env=dict(os.environ,LAKE_RESTORE_ARTIFACTS='false'),stdout=out,stderr=err)
print('donor368-current query exit',r.returncode);raise SystemExit(r.returncode)
