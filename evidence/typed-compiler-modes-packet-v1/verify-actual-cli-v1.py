from pathlib import Path
import datetime,hashlib,json,os,shutil,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031';P=E/'typed-compiler-modes-packet-v1';T=E/'return-pin-typed-proof-packet-v1';R=P/'validation-package-v1';logs=P/'actual-cli-v1';logs.mkdir();bundles=logs/'bundles';bundles.mkdir()
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(V),FV_MEMCAP='3G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false');env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,env=env,text=True).strip()
def run(label,args):
 env['FV_MEMCAP_STATS']=str(logs/(label+'.mem'));env['FV_MEMCAP_UNIT']='worker-o-typed-mode-cli-'+label.lower()
 with (logs/(label+'.log')).open('w') as out:subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh')]+args,cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
 print(label,'passed',flush=True)
cases=json.loads((T/'actual-bundle-state-v1.json').read_text())['cases'];reused={};generated={};count=0
for case in cases:
 label='WorkerOTypedCompiler'+('Cleanup' if case['cleanup'] else 'Raw');old=Path(case['dir']);directory=bundles/label;shutil.copytree(old,directory);bundle=json.loads((directory/'bundle.json').read_text());bundle['exe']=str(directory/'program.elf')
 for unit in bundle['units']:
  unit['data']=str(directory/Path(unit['data']).name)
  for entry in unit['functions']:
   for key in ['dump','ra']:entry[key]=str(directory/Path(entry[key]).name)
 (directory/'bundle.json').write_text(json.dumps(bundle,indent=2)+'\n')
 stable={str(p.relative_to(directory)):hashlib.sha256(p.read_bytes()).hexdigest() for p in directory.iterdir() if p.name.endswith(('.clif','.ra.json')) or p.name=='actual-ra.json'};reused[label]=dict(original=str(old),stable_hashes=stable,source_receipt=str(T/'actual-bundle-state-v1.json'));(logs/'reuse-manifest.json').write_text(json.dumps(reused,indent=2)+'\n')
 flag='--dead-cleanup' if case['cleanup'] else '--no-dead-cleanup'
 run(label+'-linker',['lake','env','lean','--run',str(P/'FVTest/Link/LeanLinkMain.lean'),str(directory),flag])
 text=(logs/(label+'-linker.log')).read_text();assert 'written by Link.TypedCompilerWith.attempt' in text;assert 'Link.TypedCompilerWith.attempt_correct_source_peak' in text;assert 'coverage: none' not in text
 output=bundles/'Crates'/(label+'.lean');run(label+'-checker',['lake','env','lean','--run',str(T/'FVTest/E2E/LinkCheckMain.lean'),str(directory),flag,'--lean',str(output),'--module',label])
 text=(logs/(label+'-checker.log')).read_text();assert 'okB: true' in text and 'binary: ok' in text and 'checker: typed Stock' in text
 target=R/'.lake/build/lib/lean/Crates'/label;target.parent.mkdir(parents=True,exist_ok=True);run(label+'-generated',['lake','env','lean','--root='+str(bundles),str(output),'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c'])
 public=['okB_input','link_ok','base_closed','bin_ok']+[f'correct_{i}' for i in range(3)]+[f'correct_stack_{i}' for i in range(3)];audit=logs/(label+'-audit.lean');audit.write_text('import Crates.'+label+'\n'+'\n'.join('#print axioms Crates.'+label+'.'+n+' -- witness: native_decide' for n in public)+'\n');run(label+'-audit',['python3',str(V/'scripts/axiom-audit.py'),'--cwd',str(R),'--log-dir',str(logs/(label+'-audit')),str(audit)])
 assert all(hashlib.sha256((directory/n).read_bytes()).hexdigest()==digest for n,digest in stable.items());generated[str(output.relative_to(logs))]=hashlib.sha256(output.read_bytes()).hexdigest();count+=len(public)
(P/'actual-cli-state-v1.json').write_text(json.dumps(dict(status='passed',cases=2,actual_generic_compiler_selected=True,source_and_peak_theorems_reported=True,original_inputs_and_actual_allocator_answers_exact=True,generated_roots=count,generated_hashes=generated,reuse_manifest='actual-cli-v1/reuse-manifest.json',requires_current_main_gates=True,full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat()),indent=2)+'\n');print('Both actual typed compiler modes passed with truthful source and peak theorem selection.',flush=True)
