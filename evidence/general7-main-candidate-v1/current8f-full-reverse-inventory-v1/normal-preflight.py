import json,pathlib,subprocess,os
b=pathlib.Path('/home/lee/clifv');d=b/'.git/agent-evidence/stock-memory-20261029/general7-main-candidate-v1/current8f-full-reverse-inventory-v1';m=json.loads((d/'manifest.json').read_text());root=b/'.worktrees/loop-20261102'
def git(*a):return subprocess.check_output(['git',*a],cwd=root,text=True).strip()
assert git('rev-parse','HEAD^{tree}')==git('rev-parse',m['head']+'^{tree}')
cmd=['/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake','build','--no-build',*m['reverse_targets']]
env=dict(os.environ,LAKE_RESTORE_ARTIFACTS='false',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2')
with (d/'normal326.log').open('w') as f:r=subprocess.run(cmd,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
(d/'normal326-result.json').write_text(json.dumps({'head':m['head'],'targets':len(m['reverse_targets']),'normal_exit':r.returncode,'kind':'read-only readiness preflight; no fresh kernel claim'},indent=2)+'\n');print('normal326 exit',r.returncode);raise SystemExit(r.returncode)
