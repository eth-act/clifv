from pathlib import Path
import os,json,subprocess,hashlib,tomllib,re,datetime
O=Path(__file__).resolve().parent;A=O.parent;E=A.parent;D=O/'raw-leaf-v2';D.mkdir();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();H=O/'host-R369-v2/receipt.json';assert sha(H)=='a2f00c678b48b0c612f17efafa1d6d78e254e665a73284f8546d951b7ca83441';h=json.loads(H.read_text());R=E/'direct-call-store-live-packet-v1/validation-package-v1';T=Path('/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin');source=O/'source/FV/E2E/StockAcquireActualResultImage.lean';lib=D/'outputs';stem=lib/'FV/E2E/StockAcquireActualResultImage';stem.parent.mkdir(parents=True)
def recheck():
 for m,row in h['records'].items():
  rel=m.replace('.','/');assert sha(R/(rel+'.lean'))==row['source_sha256'];assert sha(R/'.lake/build/lib/lean'/(rel+'.trace'))==row['trace_sha256']
  for ext,folder in [('olean','.lake/build/lib/lean'),('ilean','.lake/build/lib/lean'),('c','.lake/build/ir')]:assert sha(R/folder/(rel+'.'+ext))==row['payloads'][ext]['sha256']
 for n,v in h['configuration_hashes'].items():assert sha(R/n)==v
 for p in Path('/proc').iterdir():
  if not p.name.isdigit() or int(p.name)==os.getpid():continue
  try:
   args=(p/'cmdline').read_bytes().decode(errors='replace').replace('\0',' ')
   if '/bin/lean ' in args and any(str(R/(m.replace('.','/')+'.lean')) in args for m in h['records']):raise RuntimeError(('overlapping writer',p.name))
  except (OSError,PermissionError):pass
recheck()
for m in h['records']:
 rel=Path(m.replace('.', '/'))
 for ext in ['olean','ilean']:
  p=lib/rel.with_suffix('.'+ext);p.parent.mkdir(parents=True,exist_ok=True);p.symlink_to(R/'.lake/build/lib/lean'/rel.with_suffix('.'+ext))
env=dict(os.environ);env.pop('FV_LAKE_CACHE',None);env.pop('FV_MEMCAP_OFF',None);env.update(LEAN_PATH=str(lib)+':'+str(R/'.lake/build/lib/lean'),OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',LEAN_NUM_THREADS='1',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false');weak=tomllib.loads((R/'lakefile.toml').read_text())['weakLeanArgs'];commands=[]
def run(label,args,e=env,cwd=O):
 with (D/(label+'.stdout')).open('w') as out,(D/(label+'.stderr')).open('w') as err:q=subprocess.run(args,cwd=cwd,env=e,stdout=out,stderr=err)
 commands.append({'label':label,'argv':args,'exit':q.returncode,'stdout_sha256':sha(D/(label+'.stdout')),'stderr_sha256':sha(D/(label+'.stderr'))});print(label,q.returncode,flush=True);assert q.returncode==0,(label,(D/(label+'.stdout')).read_text(),(D/(label+'.stderr')).read_text())
run('raw-image-kernel',[str(T/'lean'),*weak,'--root='+str(O/'source'),str(source),'-o',str(stem)+'.olean','-i',str(stem)+'.ilean','-c',str(stem)+'.c'])
auditEnv=D/'audit-env';auditEnv.mkdir();(auditEnv/'lakefile.toml').write_text('name = "acquire_image_raw_audit"\n');(auditEnv/'lean-toolchain').write_bytes((R/'lean-toolchain').read_bytes());(auditEnv/'lake-manifest.json').write_text('{"version":"1.2.0","packagesDir":".lake/packages","packages":[],"name":"acquire_image_raw_audit","lakeDir":".lake"}\n')
audit=D/'actual-result-image.lean';audit.write_text('import FV.E2E.StockAcquireActualResultImage\n#print axioms E2E.LinkCheck.actual_results_code_image\n')
tool=D/'tools/scripts/axiom-audit.py';tool.parent.mkdir(parents=True);tool.write_bytes(subprocess.check_output(['git','show','8f073980e9630c8d3cd9d6f6f77ab462474c7bcb:scripts/axiom-audit.py']))
bin=D/'tools/bin';bin.mkdir();wrapper=bin/'lake';wrapper.write_text('#!/usr/bin/env python3\nimport os,sys\nassert sys.argv[1:3]==["env","lean"]\nos.execv('+repr(str(T/'lake'))+', ['+repr(str(T/'lake'))+',"env",'+repr(str(T/'lean'))+',"-j1",*sys.argv[3:]])\n');wrapper.chmod(0o755);aenv=dict(env);aenv['PATH']=str(bin)+':'+str(T)+':'+aenv['PATH'];run('real-auditor',['python3',str(tool),'--cwd',str(auditEnv),'--log-dir',str(D/'audit-logs'),str(audit)],aenv,auditEnv)
text=(D/'audit-logs/actual-result-image.log').read_text();ax={n:sorted(v.strip() for v in xs.replace('\n',' ').split(',') if v.strip()) for n,xs in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",text,re.S)};ax.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",text)});assert len(ax)==1 and all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in ax.values()),ax
recheck();receipt={'status':'passed_raw_actual_results_image_leaf_and_real_current_auditor','source_sha256':sha(source),'host_receipt_sha256':sha(H),'commands':commands,'axioms':ax,'raw_outputs':{str(p.relative_to(D)):sha(p) for p in stem.parent.glob(stem.name+'.*')},'real_auditor_sha256':sha(tool),'audit_source_sha256':sha(audit),'audit_environment':'owned tool-only Lake environment; no project normal key claimed for raw output','R_configuration_hashes':h['configuration_hashes'],'all369_context_bytes_unchanged':True,'all_new_outputs_under_A':True,'shared_writes_or_provider_builds':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(D/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print('receipt',sha(D/'receipt.json'))
