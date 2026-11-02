from pathlib import Path
import datetime,hashlib,json,os,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031';P=E/'return-pin-production-activation-packet-v1';R=P/'validation-package-v2';assert json.loads((P/'fresh-state-v1.json').read_text())['status']=='passed'
logs=P/'actual-bundle-v6';assert logs.exists();casesroot=logs/'bundles'
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(V),FV_MEMCAP='3G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false');env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,env=env,text=True).strip()
def run(label,args,**extra):
 if label in ['prepare','WorkerOActualPreviousRaw-backend','WorkerOActualPreviousRaw-linker','WorkerOActualPreviousRaw-checker','WorkerOActualPreviousRaw-generated','WorkerOActualPreviousRaw-audit','WorkerOActualCapturedRaw-backend']:
  assert (logs/(label+'.log')).exists();print(label,'reused successful v6 run',flush=True);return
 local=dict(env);local.update(extra);local['FV_MEMCAP_STATS']=str(logs/(label+'.mem'));local['FV_MEMCAP_UNIT']='worker-o-actual-bundle-'+label.lower()
 with (logs/(label+'.log')).open('w') as out:subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh')]+args,cwd=R,env=local,stdout=out,stderr=subprocess.STDOUT,check=True)
 print(label,'passed',flush=True)
run('prepare',['lake','env','lean','--run',str(P/'PrepareActualBundlesV6.lean'),str(casesroot)])
cases=json.loads((casesroot/'manifest.json').read_text());assert len(cases)==4;generated={};roots=0
for case in cases:
 label=case['module'];directory=Path(case['dir']);flag='--dead-cleanup' if case['cleanup'] else '--no-dead-cleanup';ra=directory/'actual-ra.json'
 run(label+'-backend',['lake','env','lean','--run',str(P/'FVTest/Backend/Main.lean'),case['input'],str(directory/'actual.o'),'--regalloc','lean','--dump',str(directory/'actual-dump'),flag],FV_RA_OUT=str(ra))
 answers=json.loads(ra.read_text())['functions'];bundle=json.loads((directory/'bundle.json').read_text());functions=bundle['units'][0]['functions'];assert len(answers)==len(functions)
 for entry,answer in zip(functions,answers):Path(entry['ra']).write_text(json.dumps({'functions':[answer]})+'\n')
 if label!='WorkerOActualPreviousRaw':
  run(label+'-reflow',['lake','env','lean','--run',str(P/'ReflowActualBundleV1.lean'),case['dir'],str(case['cleanup']).lower()])
  layout=json.loads((directory/'actual-layout.json').read_text());bundle['markers']=layout;bundle['symbols']=layout;(directory/'bundle.json').write_text(json.dumps(bundle,indent=2)+'\n')
 run(label+'-linker',['lake','env','lean','--run',str(P/'FVTest/Link/LeanLinkMain.lean'),case['dir'],flag])
 checkerlog=logs/(label+'-checker.log');output=casesroot/'Crates'/(label+'.lean')
 run(label+'-checker',['lake','env','lean','--run',str(P/'FVTest/E2E/LinkCheckMain.lean'),case['dir'],flag,'--lean',str(output),'--module',label])
 assert 'okB: true' in checkerlog.read_text(),checkerlog
 assert 'binary: ok' in checkerlog.read_text(),checkerlog
 # The small original fixtures use one output module. Keep actual generated source unchanged.
 assert output.exists();name=output.relative_to(casesroot);target=R/'.lake/build/lib/lean'/name.with_suffix('');target.parent.mkdir(parents=True,exist_ok=True)
 run(label+'-generated',['lake','env','lean','--root='+str(casesroot),str(output),'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c'])
 text=output.read_text();public=['okB_input','link_ok','base_closed','bin_ok']+[f'correct_{n}' for n in range(len(case['entries']))]+[f'correct_stack_{n}' for n in range(len(case['entries']))]
 audit=logs/(label+'-audit.lean');audit.write_text('import Crates.'+label+'\n'+'\n'.join('#print axioms Crates.'+label+'.'+root+' -- witness: native_decide' for root in public)+'\n')
 run(label+'-audit',['python3',str(V/'scripts/axiom-audit.py'),'--cwd',str(R),'--log-dir',str(logs/(label+'-audit')),str(audit)])
 roots+=len(public);generated[str(name)]=hashlib.sha256(output.read_bytes()).hexdigest()
state=dict(status='passed',cases=cases,all_three_actual_clis=True,actual_allocator_answers_reused=True,generated_roots=roots,generated_hashes=generated,requires_current_main_gates=True,full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(P/'actual-bundle-state-v8.json').write_text(json.dumps(state,indent=2)+'\n');print('All four actual bundles and generated proofs passed.',flush=True)
