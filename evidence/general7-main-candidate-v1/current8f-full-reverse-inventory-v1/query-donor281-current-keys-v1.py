from pathlib import Path
import json,subprocess,os
b=Path('/home/lee/clifv');d=b/'.git/agent-evidence/stock-memory-20261029/general7-main-candidate-v1/current8f-full-reverse-inventory-v1';targets=[x['target'] for x in json.loads((d/'donor318-after49-frontier-classification-v1.json').read_text())['rows'] if x['query_ready_after_verified49']];root=b/'.worktrees/loop-20261102';cmd=['/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake','--json','query','--no-build',*['+'+m+':depHash' for m in targets]]
with (d/'donor281-current-keys.stdout').open('w') as out,(d/'donor281-current-keys.stderr').open('w') as err:r=subprocess.run(cmd,cwd=root,env=dict(os.environ,LAKE_RESTORE_ARTIFACTS='false'),stdout=out,stderr=err)
print('donor281-current query exit',r.returncode);raise SystemExit(r.returncode)
