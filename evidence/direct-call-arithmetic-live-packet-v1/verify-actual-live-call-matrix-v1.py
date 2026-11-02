from pathlib import Path
import datetime,hashlib,json,os,re,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';Q=E/'direct-call-arithmetic-live-packet-v1';R=Q/'validation-package-v1';V=B/'.worktrees/stock-extending-production-20261031';D=E/'direct-call-delivery-units-v1'
# This matrix cannot run from drafts. The producer binds the full executed source/config closure.
context=json.loads((Q/'live-production-consumer-kernel-v1/receipt.json').read_text());assert context['status']=='passed'
assert context['proofslot_grant']=='live-production-2G'
L=Q/'actual-live-call-matrix-v1';L.mkdir();casesroot=L/'bundles';casesroot.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in context['source_hashes'].items():assert sha(R/n)==h,('executed source changed',n)
for n,h in context['effective_configs'].items():assert sha(R/n)==h,('configuration changed',n)
(L/'executed-context.json').write_text(json.dumps(context,indent=2)+'\n')
env=dict(os.environ)
for k in ['FV_LAKE_CACHE','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','FV_MEMCAP_OFF']:env.pop(k,None)
env.update(FV_ROOT=str(R),FV_MEMCAP='2G',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false')
env['LEAN_PATH']=str(R/'.lake/build/lib/lean')+':/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/lib/lean'
records={}
def run(label,args,**extra):
 local=dict(env);local.update(extra);local['FV_MEMCAP_STATS']=str(L/(label+'.mem'));local['FV_MEMCAP_UNIT']='worker-o-live-actual-'+label.lower()
 with (L/(label+'.log')).open('w') as stream:rc=subprocess.call(['nice','-n','10',str(V/'scripts/memcap.sh'),*args],cwd=R,env=local,stdout=stream,stderr=subprocess.STDOUT)
 records[label]=dict(exit_code=rc,argv=args,log_sha256=sha(L/(label+'.log')),stats=(L/(label+'.mem')).read_text() if (L/(label+'.mem')).exists() else None)
 (L/'commands.json').write_text(json.dumps(records,indent=2)+'\n');print(label,'exit',rc,flush=True)
 if rc:raise SystemExit(rc)
def lean(source,*args):return ['lake','env','lean','-j1','-DElab.async=false','--run',str(source),*args]
run('prepare',lean(Q/'PrepareLiveCallBundlesV1.lean',str(casesroot)))
cases=json.loads((casesroot/'manifest.json').read_text());assert len(cases)==4
for case in cases:
 label=case['module'];directory=Path(case['dir']);flag='--dead-cleanup' if case['cleanup'] else '--no-dead-cleanup';ra=directory/'actual-ra.json'
 original=(directory/'input.clif').read_bytes();(directory/'original-input.sha256').write_text(hashlib.sha256(original).hexdigest()+'\n')
 run(label+'-backend',lean(Q/'FVTest/Backend/Main.lean',case['input'],str(directory/'actual.o'),'--regalloc','lean','--dump',str(directory/'actual-dump'),flag),FV_RA_OUT=str(ra))
 answers=json.loads(ra.read_text())['functions'];bundle=json.loads((directory/'bundle.json').read_text());functions=bundle['units'][0]['functions'];assert len(answers)==len(functions)
 if not case['typed']:assert 'x19' in json.dumps(answers[0]),('actual caller must preserve its live value',answers[0])
 for entry,answer in zip(functions,answers):Path(entry['ra']).write_text(json.dumps({'functions':[answer]})+'\n')
 run(label+'-reflow',lean(Q/'ReflowLiveCallBundleV1.lean',case['dir'],str(case['cleanup']).lower()))
 layout=json.loads((directory/'actual-layout.json').read_text());bundle['markers']=layout;bundle['symbols']=layout;(directory/'bundle.json').write_text(json.dumps(bundle,indent=2)+'\n')
 run(label+'-linker',lean(Q/'FVTest/Link/LeanLinkMain.lean',case['dir'],flag))
 linker=(L/(label+'-linker.log')).read_text()
 if not case['typed']:assert 'Link.LiveCallCompilerWith.attempt' in linker,linker
 output=casesroot/'Crates'/(label+'.lean')
 run(label+'-checker',lean(Q/'FVTest/E2E/LinkCheckMain.lean',case['dir'],flag,'--lean',str(output),'--module',label))
 checker=(L/(label+'-checker.log')).read_text();assert 'okB: true' in checker and 'binary: ok' in checker,checker
 text=output.read_text()
 if not case['typed']:assert 'LiveCallChecks.CrateStmtProduction' in text,text
 else:assert 'ArmRefinesT' in text or 'TypedProductionChecks' in text,text
 assert (directory/'input.clif').read_bytes()==original
 target=R/'.lake/build/lib/lean/Crates'/label;target.parent.mkdir(parents=True,exist_ok=True)
 run(label+'-generated',['lake','env','lean','-j1','-DElab.async=false','--root='+str(casesroot),str(output),'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c'])
 roots=['okB_input','link_ok','base_closed','bin_ok']+[f'correct_{i}' for i in range(len(case['entries']))]+[f'correct_stack_{i}' for i in range(len(case['entries']))]
 audit=L/(label+'-audit.lean');audit.write_text('import Crates.'+label+'\n'+'\n'.join('#print axioms Crates.'+label+'.'+root+' -- witness: native_decide' for root in roots)+'\n')
 run(label+'-audit',['python3',str(D/'axiom-audit-j1.py'),'--cwd',str(R),'--log-dir',str(L/(label+'-audit')),str(audit)])
for n,h in context['source_hashes'].items():assert sha(R/n)==h,n
state=dict(status='passed',cases=cases,all_three_clis=True,original_pair=True,distinct_float_variant=True,actual_default_selected=True,generated_proofs_audited=True,source_context=context['source_context'],commands=records,production_complete=False,full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(L/'result.json').write_text(json.dumps(state,indent=2)+'\n')
