from pathlib import Path
import json,subprocess,os
b=Path('/home/lee/clifv');d=b/'.git/agent-evidence/stock-memory-20261029/general7-main-candidate-v1/current8f-full-reverse-inventory-v1';m=json.loads((d/'remaining-cone-proposal-v1.json').read_text());targets=m['complete_source_order'];root=b/'.worktrees/loop-20261102';cmd=['/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake','--json','query','--no-build',*['+'+n+':depHash' for n in targets]]
with (d/'complete-keys.stdout').open('w') as out,(d/'complete-keys.stderr').open('w') as err:r=subprocess.run(cmd,cwd=root,env=dict(os.environ,LAKE_RESTORE_ARTIFACTS='false'),stdout=out,stderr=err)
if r.returncode==0:
 keys=[json.loads(l) for l in (d/'complete-keys.stdout').read_text().splitlines()];assert len(keys)==len(targets);(d/'complete-current3381-keys.json').write_text(json.dumps(dict(zip(targets,keys)),indent=2)+'\n')
print('complete source closure key query',r.returncode);raise SystemExit(r.returncode)
