from pathlib import Path
import os,json,hashlib,subprocess,tomllib,shutil,re,datetime
O=Path(__file__).resolve().parent;A=O.parent;E=A.parent;D=O/'raw-entry-v1';D.mkdir();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();previous=A/'actual-map-rel-rw-proposal-v4';H=previous/'host-R376-v2/receipt.json';assert sha(H)=='a300104c0c8332492cd6ad6b458ce318dd41155ea240d91059a918671ed20d72';h=json.loads(H.read_text());M=O/'manifest.json';assert sha(M)=='5b7ea96a863d9df08036622cf4e0f1fbc57c23d074a6a398a980b031bede8d19';m=json.loads(M.read_text());R=E/'direct-call-store-live-packet-v1/validation-package-v1';T=Path('/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin');lib=D/'outputs';lib.mkdir();V=previous/'host-R376-v1/metadata';X=A/'outside-avoids-extraction-proposal-v1';outside=X/'light-view-cleanup-v1/preserved-leaf';image=A/'actual-result-image-bridge-v2/raw-leaf-v2';imageReceipt=image/'final-receipt.json';assert sha(imageReceipt)=='d2b6e4cc2e5cb2e2828d2c07d5db76d4f8c42712c6ab90d892cf2cade1158d68';oldOutside=json.loads((X/'light-leaf-v2/final-receipt.json').read_text());reuse=previous/'OutsideAvoids155-reuse-check-v1/receipt.json';assert sha(reuse)=='7e46de3e3696b830b199f6c0d8f90df88466f6cbbb11b31cdba1d2920e74af2d'
def recheck():
 for name,row in h['records'].items():
  rel=name.replace('.','/');assert sha(R/(rel+'.lean'))==row['source_sha256'];assert sha(R/'.lake/build/lib/lean'/(rel+'.trace'))==row['trace_sha256']
  for ext,folder in [('olean','.lake/build/lib/lean'),('ilean','.lake/build/lib/lean'),('c','.lake/build/ir')]:assert sha(R/folder/(rel+'.'+ext))==row['payloads'][ext]['sha256']
 for n,v in h['configuration_hashes'].items():assert sha(R/n)==v
 for rel,v in m['source_hashes'].items():assert sha(O/rel)==v
 for proc in Path('/proc').iterdir():
  if not proc.name.isdigit() or int(proc.name)==os.getpid():continue
  try:
   args=(proc/'cmdline').read_bytes().decode(errors='replace').replace('\0',' ')
   if '/bin/lean ' in args and any(str(R/(n.replace('.','/')+'.lean')) in args for n in h['records']):raise RuntimeError(('overlapping writer',proc.name))
  except (OSError,PermissionError):pass
recheck()
for name in h['records']:
 rel=Path(name.replace('.','/'))
 for ext in ['olean','ilean']:
  p=lib/rel.with_suffix('.'+ext);p.parent.mkdir(parents=True,exist_ok=True);p.symlink_to(R/'.lake/build/lib/lean'/rel.with_suffix('.'+ext))
# Reuse only the already approved leaf after the complete155 comparison and proper native check.
assert sha(O/'source/FV/E2E/OutsideAvoids.lean')==sha(outside/'FV/E2E/OutsideAvoids.lean')
for ext in ['olean','ilean']:(lib/'FV/E2E'/('OutsideAvoids.'+ext)).symlink_to(outside/'.lake/build/lib/lean/FV/E2E'/('OutsideAvoids.'+ext))
ir=json.loads(imageReceipt.read_text())
for rel,v in ir['raw_outputs'].items():assert sha(image/rel)==v
for ext in ['olean','ilean']:(lib/'FV/E2E'/('StockAcquireActualResultImage.'+ext)).symlink_to(image/'outputs/FV/E2E'/('StockAcquireActualResultImage.'+ext))
env=dict(os.environ);env.pop('FV_LAKE_CACHE',None);env.pop('FV_MEMCAP_OFF',None);env.update(PATH=str(T)+':'+env['PATH'],LEAN_PATH=str(lib),OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',LEAN_NUM_THREADS='1',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LAKE_CACHE_DIR=str(D/'disabled-cache'));commands=[]
def run(label,args,cwd=O,e=env):
 with (D/(label+'.stdout')).open('w') as out,(D/(label+'.stderr')).open('w') as err:q=subprocess.run(args,cwd=cwd,env=e,stdout=out,stderr=err)
 commands.append({'label':label,'argv':args,'exit':q.returncode,'stdout_sha256':sha(D/(label+'.stdout')),'stderr_sha256':sha(D/(label+'.stderr'))});print(label,q.returncode,flush=True);assert q.returncode==0,(label,(D/(label+'.stdout')).read_text(),(D/(label+'.stderr')).read_text());return (D/(label+'.stdout')).read_text()
oldraw=previous/'raw-unit-v1';assert (oldraw/'OutsideAvoids-expected-key.stdout').read_text().strip()=='b6c00cc0e27eed0d'
assert (oldraw/'OutsideAvoids-normal.stdout').exists()
modules=['FV.E2E.StockAcquireKeptWorld','FV.E2E.StockAcquireLayoutImage','FV.E2E.StockAcquireMapRelRWWithResults','FV.E2E.StockAcquireMapRelEntryWithResults'];weak=tomllib.loads((R/'lakefile.toml').read_text())['weakLeanArgs'];artifacts={}
for module in modules:
 rel=Path(module.replace('.','/'));src=O/'source'/rel.with_suffix('.lean');stem=lib/rel;stem.parent.mkdir(parents=True,exist_ok=True)
 if module!='FV.E2E.StockAcquireMapRelEntryWithResults':
  assert sha(src)==sha(previous/'source'/rel.with_suffix('.lean'))
  assert not (oldraw/(module.split('.')[-1]+'.stderr')).read_text()
  for ext in ['olean','ilean','c']:(stem.parent/(stem.name+'.'+ext)).symlink_to(oldraw/'outputs'/rel.with_suffix('.'+ext))
 else:
  run(module.split('.')[-1],[str(T/'lean'),*weak,'--root='+str(O/'source'),str(src),'-o',str(stem)+'.olean','-i',str(stem)+'.ilean','-c',str(stem)+'.c'])
 for ext in ['olean','ilean','c']:artifacts[str((stem.parent/(stem.name+'.'+ext)).relative_to(D))]=sha(stem.parent/(stem.name+'.'+ext))
auditEnv=D/'audit-env';auditEnv.mkdir();(auditEnv/'lakefile.toml').write_text('name = "acquire_mapping_raw_audit"\n');(auditEnv/'lean-toolchain').write_bytes((R/'lean-toolchain').read_bytes());(auditEnv/'lake-manifest.json').write_text('{"version":"1.2.0","packagesDir":".lake/packages","packages":[],"name":"acquire_mapping_raw_audit","lakeDir":".lake"}\n');audit=D/'actual-map-rel.lean';roots=[];text=''
for module in modules:
 text+='import '+module+'\n';src=(O/'source'/(module.replace('.','/')+'.lean')).read_text();ns=re.search(r'^namespace (\S+)',src,re.M)[1]
 for name in re.findall(r'^theorem (\w+)',src,re.M):roots.append(ns+'.'+name)
text+=''.join('#print axioms '+n+'\n' for n in roots);audit.write_text(text);tool=D/'tools/scripts/axiom-audit.py';tool.parent.mkdir(parents=True);tool.write_bytes(subprocess.check_output(['git','show','8f073980e9630c8d3cd9d6f6f77ab462474c7bcb:scripts/axiom-audit.py']));bin=D/'tools/bin';bin.mkdir();wrapper=bin/'lake';wrapper.write_text('#!/usr/bin/env python3\nimport os,sys\nassert sys.argv[1:3]==["env","lean"]\nos.execv('+repr(str(T/'lake'))+', ['+repr(str(T/'lake'))+',"env",'+repr(str(T/'lean'))+',"-j1",*sys.argv[3:]])\n');wrapper.chmod(0o755);ae=dict(env);ae['PATH']=str(bin)+':'+ae['PATH'];run('real-auditor',['python3',str(tool),'--cwd',str(auditEnv),'--log-dir',str(D/'audit-logs'),str(audit)],auditEnv,ae)
text=(D/'audit-logs/actual-map-rel.log').read_text();ax={n:sorted(v.strip() for v in xs.replace('\n',' ').split(',') if v.strip()) for n,xs in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",text,re.S)};ax.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",text)});assert len(ax)==len(roots)==13 and all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in ax.values());prior=json.loads((A/'universal-paired-stepF-return-checkpoint-v100/state.json').read_text());oldNames=[n for n in roots if n in prior['axioms']];assert len(oldNames)==10 and all(ax[n]==prior['axioms'][n] for n in oldNames);recheck()
r={'status':'passed_raw_mapping_entry_and_table_image_unit','manifest_sha256':sha(M),'host376_receipt_sha256':sha(H),'OutsideAvoids155_reuse_receipt_sha256':sha(reuse),'image_raw_receipt_sha256':sha(imageReceipt),'commands':commands,'roots':len(roots),'axioms':ax,'all_ten_old_KepWorld_LayoutImage_AX_sets_exact':True,'prior_v100_receipt_sha256':sha(A/'universal-paired-stepF-return-checkpoint-v100/state.json'),'artifact_hashes_including_three_reused_prerequisites':artifacts,'three_passed_kernels_reused':True,'old_failed_run_source_sha256':sha(previous/'manifest.json'),'old_OutsideAvoids_key_log_sha256':sha(oldraw/'OutsideAvoids-expected-key.stdout'),'old_OutsideAvoids_normal_log_sha256':sha(oldraw/'OutsideAvoids-normal.stdout'),'real_auditor_sha256':sha(tool),'audit_source_sha256':sha(audit),'shared_source_config_or_provider_outputs_changed':False,'actual_original_public_MapRelRW_bridge':'open','original_budget_discharge':'open','ELF_and_pipeline_inhabitation':'open','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(D/'receipt.json').write_text(json.dumps(r,indent=2)+'\n');print('receipt',sha(D/'receipt.json'))
