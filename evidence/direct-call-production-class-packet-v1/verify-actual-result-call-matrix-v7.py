from pathlib import Path
import datetime,hashlib,json,os,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';P=E/'direct-call-production-class-packet-v1';V=B/'.worktrees/stock-extending-production-20261031';R=P/'validation-package-v1'
assert json.loads((P/'coherent-consumer-kernel-v1/result.json').read_text())['status']=='passed'
assert json.loads((P/'generated-import-kernel-v1/result.json').read_text())['status']=='passed'
assert json.loads((P/'actual-support-kernel-v1/result.json').read_text())['status']=='passed'
logs=P/'actual-result-call-matrix-v7';logs.mkdir();casesroot=logs/'bundles';casesroot.mkdir()
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(V),FV_MEMCAP='2G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false');env['LEAN_PATH']=str(R/'.lake/build/lib/lean')+':'+subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,env=env,text=True).strip()
# Bind the executed CLI closure, rather than merging partial source-hash maps.
ctx=json.loads((P/'generated-import-kernel-v1/result.json').read_text());assert ctx['status']=='passed'
inventory=json.loads((P/'production-context-inventory-v25.json').read_text());assert inventory['carrier_head']==subprocess.check_output(['git','rev-parse','HEAD'],cwd=V,text=True).strip()
for name,h in ctx['source_hashes'].items():assert inventory['source_hashes'][name]==h,('executed closure changed',name)
for name,blob in inventory['configs'].items():
 data=(V/name).read_bytes();assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==blob
import re
keys={};dag={};artifact_hashes={}
def digest_file(path):
 h=hashlib.sha256()
 with path.open('rb') as src:
  while block:=src.read(1024*1024):h.update(block)
 return h.hexdigest()
for name,h in ctx['source_hashes'].items():
 if (P/name).exists():data=(P/name).read_bytes()
 elif (E/'direct-call-result-packet-v1'/name).exists():data=(E/'direct-call-result-packet-v1'/name).read_bytes()
 else:data=subprocess.check_output(['git','cat-file','blob',inventory['git_blobs'][name]],cwd=B)
 assert hashlib.sha256(data).hexdigest()==h,name
 dag[name]=sorted(m.replace('.','/')+'.lean' for m in re.findall(r'^import\s+([\w.]+)',data.decode(),re.M) if m.startswith(('FV.','FVTest.')))
 for suffix in ['.olean','.olean.private']:
  f=R/'.lake/build/lib/lean'/Path(name).with_suffix(suffix)
  if f.exists():artifact_hashes[str(f.relative_to(R))]=digest_file(f)
config_key=hashlib.sha256(json.dumps(inventory['configs'],sort_keys=True).encode()).hexdigest()
def key(name):
 if name not in keys:keys[name]=hashlib.sha256(json.dumps([config_key,ctx['source_hashes'][name],[(dep,key(dep)) for dep in dag[name]]],sort_keys=True).encode()).hexdigest()
 return keys[name]
for name in dag:key(name)
(logs/'executed-context.json').write_text(json.dumps(dict(source_hashes=ctx['source_hashes'],dependency_keys=keys,artifact_hashes=artifact_hashes,configs=inventory['configs'],current_main_validation=False,rerun_reason='Final complete matrix under exact executed closure; restore original float whitespace; avoid partial matrix reuse'),indent=2)+'\n')
receipts={}
def run(label,args,**extra):
 local=dict(env);local.update(extra);local['FV_MEMCAP_STATS']=str(logs/(label+'.mem'));local['FV_MEMCAP_UNIT']='worker-o-result-actual-'+label.lower()
 with (logs/(label+'.log')).open('w') as out:r=subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh')]+args,cwd=R,env=local,stdout=out,stderr=subprocess.STDOUT)
 receipts[label]={'exit_code':r.returncode,'command':args,'log_sha256':hashlib.sha256((logs/(label+'.log')).read_bytes()).hexdigest()};(logs/'commands.json').write_text(json.dumps(receipts,indent=2)+'\n')
 print(label,'exit',r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
def lean(source,*args):return ['lake','env','lean','-j1','-DElab.async=false','--run',str(source)]+list(args)
run('prepare',lean(P/'PrepareResultCallBundlesV3.lean',str(casesroot)))
cases=json.loads((casesroot/'manifest.json').read_text());assert len(cases)==4
for case in cases:
 label=case['module'];directory=Path(case['dir']);flag='--dead-cleanup' if case['cleanup'] else '--no-dead-cleanup';ra=directory/'actual-ra.json'
 original=(directory/'input.clif').read_bytes();(directory/'original-input.sha256').write_text(hashlib.sha256(original).hexdigest()+'\n')
 run(label+'-backend',lean(P/'FVTest/Backend/Main.lean',case['input'],str(directory/'actual.o'),'--regalloc','lean','--dump',str(directory/'actual-dump'),flag),FV_RA_OUT=str(ra))
 answers=json.loads(ra.read_text())['functions'];bundle=json.loads((directory/'bundle.json').read_text());functions=bundle['units'][0]['functions'];assert len(answers)==len(functions)
 for entry,answer in zip(functions,answers):Path(entry['ra']).write_text(json.dumps({'functions':[answer]})+'\n')
 run(label+'-reflow',lean(P/'ReflowResultCallBundleV4.lean',case['dir'],str(case['cleanup']).lower()))
 layout=json.loads((directory/'actual-layout.json').read_text());bundle['markers']=layout;bundle['symbols']=layout;(directory/'bundle.json').write_text(json.dumps(bundle,indent=2)+'\n')
 run(label+'-linker',lean(P/'FVTest/Link/LeanLinkMain.lean',case['dir'],flag))
 linker=(logs/(label+'-linker.log')).read_text()
 if not case['typed']:assert 'Link.ResultCallCompilerWith.attempt' in linker,linker
 output=casesroot/'Crates'/(label+'.lean')
 run(label+'-checker',lean(P/'FVTest/E2E/LinkCheckMain.lean',case['dir'],flag,'--lean',str(output),'--module',label))
 checker=(logs/(label+'-checker.log')).read_text();assert 'okB: true' in checker and 'binary: ok' in checker,checker
 text=output.read_text()
 if not case['typed']:assert 'ResultCallChecks.CrateStmtProduction' in text
 else:assert 'ArmRefinesT' in text or 'TypedProductionChecks' in text,text
 assert (directory/'input.clif').read_bytes()==original
 target=R/'.lake/build/lib/lean/Crates'/label;target.parent.mkdir(parents=True,exist_ok=True)
 run(label+'-generated',['lake','env','lean','-j1','-DElab.async=false','--root='+str(casesroot),str(output),'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c'])
 roots=['okB_input','link_ok','base_closed','bin_ok']+[f'correct_{n}' for n in range(len(case['entries']))]+[f'correct_stack_{n}' for n in range(len(case['entries']))]
 audit=logs/(label+'-audit.lean');audit.write_text('import Crates.'+label+'\n'+'\n'.join('#print axioms Crates.'+label+'.'+root+' -- witness: native_decide' for root in roots)+'\n')
 run(label+'-audit',['python3',str(P/'axiom-audit-j1.py'),'--cwd',str(R),'--log-dir',str(logs/(label+'-audit')),str(audit)])
state=dict(status='passed',cases=cases,current_main_validation=False,full_goal_complete=False,all_three_clis=True,commands=receipts,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(logs/'result.json').write_text(json.dumps(state,indent=2)+'\n')
