from pathlib import Path
import json,hashlib,shutil
E=Path('/home/lee/clifv/.git/agent-evidence/stock-memory-20261029');D=E/'validated-ExecWrites-broad-12g-v1';D.mkdir();Q=E/'direct-call-store-live-packet-v1/production-validated-return-trace-W-proposal-v2/ExecWrites-bounded-proposal-v1';old=E/'general7-direct31-remaining22-broad-12g-v2';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(Q/'manifest.json')=='2953c07ff948f6c59a9cde558d5e726966ed0347ca3fc69a8b606690768933d9'
gate='''from pathlib import Path
import json,hashlib,os,psutil,re,shutil,subprocess
D=Path(__file__).resolve().parent;E=D.parent;R=E/'direct-call-store-live-packet-v1/validation-package-v1';P=E/'892-joint-current-context-v2/package';Q=E/'direct-call-store-live-packet-v1/production-validated-return-trace-W-proposal-v2/ExecWrites-bounded-proposal-v1';G=Path('/home/lee/clifv/.worktrees/loop-20261102');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(Q/'manifest.json')=='2953c07ff948f6c59a9cde558d5e726966ed0347ca3fc69a8b606690768933d9';I=json.loads((Q/'manifest.json').read_text());release=json.loads((D/'command-release-v1.json').read_text());assert release['approved'] and release['allocation']=='12G' and release['manifest_sha256']==sha(Q/'manifest.json') and release['script_sha256']==sha(Path(__file__))
context=Q.parent/'current-source-context-v1/manifest.json';assert sha(context)==I['final_source_context_sha256'];C=json.loads(context.read_text());sources={rel:h for rel,h in C['sources'].items() if rel!=C['owned']};records=[];target='FV.E2E.ExecWrites'
def guards():
 p=psutil.Process(release['broad_controller_pid']);assert p.create_time()==release['scheduler_birth'] and p.status()==psutil.STATUS_STOPPED;assert not any(q.is_running() and q.status()!=psutil.STATUS_ZOMBIE for q in p.children(recursive=True))
 for q in psutil.process_iter(['uids','name','status','cmdline']):
  try:
   if q.info['uids'].real!=os.getuid() or q.info['name'] not in ['lean','lake'] or q.info['status']=='zombie':continue
   cwd=q.cwd();args=q.info['cmdline'] or [];assert not any(cwd.startswith(str(root)) or any(str(root) in a for a in args) for root in [R,G]),('R/G writer',q.pid)
  except(psutil.NoSuchProcess,psutil.AccessDenied):pass
 for rel,h in sources.items():assert sha(R/rel)==h,rel
 for c,h in I['configs'].items():assert sha(R/c)==h,c
 assert (D/'R-writer-release.json').exists()
env=dict(os.environ)
for k in ['FV_MEMCAP_OFF','FV_LAKE_CACHE','LEAN_PATH','LEAN_SYSROOT','LEAN_SRC_PATH','LAKE_CACHE_DIR']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(R),FV_MEMCAP='12G',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2')
def run(label,args,root=R,allowed=(0,)):
 guards();e=dict(env,FV_ROOT=str(root),FV_MEMCAP_STATS=str(D/(label+'.mem')),FV_MEMCAP_UNIT='worker-o-ExecWrites-current-'+label)
 with (D/(label+'.log')).open('w') as f:rc=subprocess.call([str(P/'scripts/memcap.sh'),'lake',*args],cwd=root,env=e,stdout=f,stderr=subprocess.STDOUT)
 records.append({'label':label,'root':str(root),'argv':['lake',*args],'exit':rc,'log_sha256':sha(D/(label+'.log')),'memory':(D/(label+'.mem')).read_text()});(D/'progress.json').write_text(json.dumps(records,indent=2)+'\\n');print(label,rc,flush=True);assert rc in allowed,(label,rc);return rc
try:
 run('deps128',['build','--no-build',*I['proper_dependencies128']]);run('key',['query','--no-build','+'+target+':depHash']);assert re.findall(r'^[0-9a-f]{16}$',(D/'key.log').read_text(),re.M)==[I['current_key']]
 ready=run('ready',['build','--no-build',target],allowed=(0,3))==0;reused=False
 if not ready:
  donor=P/'.lake/build/lib/lean/FV/E2E/ExecWrites.trace'
  if donor.exists() and json.loads(donor.read_text())['depHash']==I['current_key']:
   data=json.loads(donor.read_text());assert data.get('inputs') and not data.get('synthetic'),'Unsupported donor origin'
   for n,h in I['source_hashes'].items():assert sha(P/Path(n.replace('.','/')+'.lean'))==h,n
   for c in ['lake-manifest.json','lean-toolchain']:assert sha(P/c)==sha(R/c)
   assert (P/'lakefile.toml').read_text().replace('"-j2",','')==(R/'lakefile.toml').read_text().replace('"-j1",','')
   run('donor-normal',['build','--no-build',target],root=P)
   for area in ['lib/lean','ir']:
    stem=P/'.lake/build'/area/'FV/E2E/ExecWrites'
    for source in stem.parent.glob(stem.name+'.*'):
     if not source.is_file() or source.name.endswith(('.c.o','.o','.bc')):continue
     dest=R/source.relative_to(P);h=sha(source)
     if dest.exists():
      saved=D/'old-output'/dest.relative_to(R);saved.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(dest,saved);dest.unlink()
     dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,dest);assert sha(dest)==h and sha(source)==h
   ready=True;reused=True
 if not ready:
  for root in [Path('/home/lee/clifv/.worktrees/driver-proof-resume/.lake/artifact-cache'),E/'892-current-main-context-v1/package/.lake/ci-cache']:assert not(root/'outputs/fv'/str(I['current_key']+'.json')).exists(),'Matching cache needs provenance review'
  for area in ['lib/lean','ir']:
   stem=R/'.lake/build'/area/'FV/E2E/ExecWrites'
   for output in stem.parent.glob(stem.name+'.*'):
    if not output.is_file():continue
    saved=D/'old-output'/output.relative_to(R);saved.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(output,saved)
    if output.is_symlink() or output.stat().st_nlink!=1 or not output.stat().st_mode&0o200:
     tmp=output.with_name(output.name+'.lease-detach');shutil.copyfile(output,tmp);os.replace(tmp,output)
  run('kernel',['-v','build','+'+target+':leanArts'])
 run('normal-target',['build','--no-build',target]);run('proper387',['build','--no-build',*I['final_proper387_targets']]);tr=R/'.lake/build/lib/lean/FV/E2E/ExecWrites.trace';data=json.loads(tr.read_text());assert data.get('inputs') and not data.get('synthetic') and data['depHash']==I['current_key']
 outputs={}
 for area in ['lib/lean','ir']:
  stem=R/'.lake/build'/area/'FV/E2E/ExecWrites'
  for file in stem.parent.glob(stem.name+'.*'):
   if file.is_file():outputs[str(file.relative_to(R))]=sha(file)
 (D/'receipt.json').write_text(json.dumps({'status':'PASSED_EXACT_CURRENT_EXECWRITES_AND_PROPER387','manifest_sha256':sha(Q/'manifest.json'),'target':target,'native_key':data['depHash'],'trace_sha256':sha(tr),'outputs':outputs,'reused_proper_donor':reused,'records':records,'source_change':'none','full_goal_complete':False},indent=2)+'\\n')
finally:(D/'lease-ended.json').write_text(json.dumps({'controller':os.getpid(),'restore_source2_acquire1':True})+'\\n')
'''
(D/'gate.py').write_text(gate)
for name in ['run.py','guard.py','launch.py']:
 s=(old/name).read_text().replace("Q = E / 'general7-main-candidate-v1/direct31-remaining22-continuation-proposal-v1'", "Q = E / 'direct-call-store-live-packet-v1/production-validated-return-trace-W-proposal-v2/ExecWrites-bounded-proposal-v1'").replace('d91c57bccb37d97ba5d5d234e408718fb7043db71de71e7ac8e8f44eac32bb26',sha(Q/'manifest.json')).replace('worker-o-general7-direct31-cone22-','worker-o-ExecWrites-current-').replace('general7-direct31-cone22-broad-resume-v2','ExecWrites-current-broad-resume-v1').replace(sha(old/'gate.py'),sha(D/'gate.py'));(D/name).write_text(s)
shutil.copyfile(old/'R-writer-release.json',D/'R-writer-release.json');(D/'harness-manifest.json').write_text(json.dumps({'manifest_sha256':sha(Q/'manifest.json'),'scripts':{n:sha(D/n) for n in ['run.py','guard.py','gate.py','launch.py']},'prior_cone_receipt_sha256':sha(old/'receipt.json'),'root_approved':'Separate ExecWrites proposal2953c07f after corrected consumer cone; full proper387 required','no_compiler_started':True},indent=2)+'\n');print(sha(D/'harness-manifest.json'))
