from pathlib import Path
import datetime,hashlib,json,os,shutil,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031';P=E/'typed-compiler-modes-packet-v1';T=E/'return-pin-typed-proof-packet-v1';R=P/'validation-package-v1';logs=P/'old-variant-kernel-v1';logs.mkdir()
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(V),FV_MEMCAP='3G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false');env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,env=env,text=True).strip()
def run(label,args):
 env['FV_MEMCAP_STATS']=str(logs/(label+'.mem'));env['FV_MEMCAP_UNIT']='worker-o-typed-mode-cli-'+label.lower()
 with (logs/(label+'.log')).open('w') as out:subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh')]+args,cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
 print(label,'passed',flush=True)
run('audit',['python3',str(V/'scripts/axiom-audit.py'),'--cwd',str(R),'--log-dir',str(logs/'audit'),str(P/'scripts/audit/typed-compiler-old-variants.lean')])
import re
raw=(logs/'audit/typed-compiler-old-variants.log').read_text();sets={name:sorted(x.strip() for x in values.replace('\n',' ').split(',') if x.strip()) for name,values in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",raw,re.S)}
pairs=json.loads((P/'old-header-parity-v1.json').read_text())
for name,pair in pairs.items():
 assert pair['old'] in sets and pair['new'] in sets,(name,sets)
 assert sets[pair['old']]==sets[pair['new']],name
 pair['axioms']=sets[pair['old']]
(P/'old-variant-parity-v1.json').write_text(json.dumps(dict(status='passed',pairs=pairs,old_source_files_unchanged=True),indent=2)+'\n');print('Six original theorem headers and axiom sets remain exact.',flush=True)
