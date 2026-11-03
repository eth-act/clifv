from pathlib import Path
import json,hashlib,shutil
E=Path('/home/lee/clifv/.git/agent-evidence/stock-memory-20261029');D=E/'general7-direct33-consumers-broad-12g-v1';D.mkdir();Q=E/'general7-main-candidate-v1/direct33-remaining-kernel-cone-v1';old=E/'general7-direct31-remaining22-broad-12g-v2';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(Q/'manifest.json')=='8e06b3066f562546b31736b7e57f529d26ee2f8b0ff34ee118d08af3c2dde411';I=json.loads((Q/'manifest.json').read_text());(D/'original-G-lakefile.toml').write_text(I['original_G_lakefile']);(D/'config-restoration.json').write_text(json.dumps({'G':'/home/lee/clifv/.worktrees/loop-20261102','original_sha256':I['original_G_config_hashes']['lakefile.toml']},indent=2)+'\n')
helper='''from pathlib import Path
import hashlib,json,os
def restore_config(D):
 data=json.loads((D/'config-restoration.json').read_text());original=(D/'original-G-lakefile.toml').read_bytes();assert hashlib.sha256(original).hexdigest()==data['original_sha256'];path=Path(data['G'])/'lakefile.toml';current=path.read_bytes();projected=original.replace(b'weakLeanArgs = [',b'weakLeanArgs = ["-j1",',1);assert current in [original,projected],('Unexpected G config; preserve it',str(path))
 if current!=original:
  tmp=path.with_name(path.name+'.General7-restore');tmp.write_bytes(original);os.replace(tmp,path)
 assert path.read_bytes()==original
 return {'original_config_restored':True,'original_sha256':data['original_sha256'],'changed':current!=original}
''';(D/'restore_config.py').write_text(helper)
gate='''from pathlib import Path
import json,hashlib,os,psutil,re,shutil,subprocess,tomllib
from restore_config import restore_config
D=Path(__file__).resolve().parent;E=D.parent;G=Path('/home/lee/clifv/.worktrees/loop-20261102');P=E/'892-joint-current-context-v2/package';R=E/'direct-call-store-live-packet-v1/validation-package-v1';Q=E/'general7-main-candidate-v1/direct33-remaining-kernel-cone-v1';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(Q/'manifest.json')=='8e06b3066f562546b31736b7e57f529d26ee2f8b0ff34ee118d08af3c2dde411';I=json.loads((Q/'manifest.json').read_text());release=json.loads((D/'command-release-v1.json').read_text());assert release['approved'] and release['allocation']=='12G' and release['manifest_sha256']==sha(Q/'manifest.json') and release['script_sha256']==sha(Path(__file__));original=(D/'original-G-lakefile.toml').read_bytes();projected=original.replace(b'weakLeanArgs = [',b'weakLeanArgs = ["-j1",',1);records=[];targets={}
def guards():
 p=psutil.Process(release['broad_controller_pid']);assert p.create_time()==release['scheduler_birth'] and p.status()==psutil.STATUS_STOPPED;assert not any(q.is_running() and q.status()!=psutil.STATUS_ZOMBIE for q in p.children(recursive=True))
 for q in psutil.process_iter(['uids','name','status','cmdline']):
  try:
   if q.info['uids'].real!=os.getuid() or q.info['name'] not in ['lean','lake'] or q.info['status']=='zombie':continue
   cwd=q.cwd();args=q.info['cmdline'] or [];assert not any(cwd.startswith(str(root)) or any(str(root) in a for a in args) for root in [R,G]),('R/G writer',q.pid)
  except(psutil.NoSuchProcess,psutil.AccessDenied):pass
 assert (G/'lakefile.toml').read_bytes() in [original,projected]
 for cfg,h in I['original_G_config_hashes'].items():
  if cfg!='lakefile.toml':assert sha(G/cfg)==h,cfg
 for n,h in I['source_hashes1831'].items():assert sha(G/Path(n.replace('.','/')+'.lean'))==h,n
 for rel,h in I['candidate_source_hashes8'].items():assert sha(G/rel)==h,rel
 for rel,h in json.loads((Q/'protected30-current-artifacts.json').read_text()).items():assert sha(G/rel)==h,rel
 assert (D/'R-writer-release.json').exists()
env=dict(os.environ)
for k in ['FV_MEMCAP_OFF','FV_LAKE_CACHE','LEAN_PATH','LEAN_SYSROOT','LEAN_SRC_PATH','LAKE_CACHE_DIR']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(G),FV_MEMCAP='12G',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2')
def run(label,args,allowed=(0,)):
 guards();e=dict(env,FV_MEMCAP_STATS=str(D/(label+'.mem')),FV_MEMCAP_UNIT='worker-o-General7-consumer33-'+label)
 with (D/(label+'.log')).open('w') as f:rc=subprocess.call([str(P/'scripts/memcap.sh'),'lake',*args],cwd=G,env=e,stdout=f,stderr=subprocess.STDOUT)
 records.append({'label':label,'argv':['lake',*args],'exit':rc,'log_sha256':sha(D/(label+'.log')),'memory':(D/(label+'.mem')).read_text()});(D/'progress.json').write_text(json.dumps(records,indent=2)+'\\n');print(label,rc,flush=True);assert rc in allowed,(label,rc);return rc
def artifacts(n):
 out={}
 for area in ['lib/lean','ir']:
  stem=G/'.lake/build'/area/n.replace('.','/')
  for f in stem.parent.glob(stem.name+'.*'):
   if f.is_file():out[str(f.relative_to(G))]=sha(f)
 return out
try:
 guards();assert (G/'lakefile.toml').read_bytes()==original;run('baseline1768',['build','--no-build',*I['baseline1768']]);preserved={}
 for n in I['conditional_topological_order33']:
  preserved[n]=artifacts(n)
  for rel,h in preserved[n].items():
   dest=D/'old-consumer-outputs'/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(G/rel,dest);assert sha(dest)==h
 (D/'preserved-consumer-outputs.json').write_text(json.dumps(preserved,indent=2)+'\\n');(G/'lakefile.toml').write_bytes(projected)
 for i,n in enumerate(I['conditional_topological_order33']):
  run('deps'+str(i),['build','--no-build',*I['records'][n]['dependencies']]);run('key'+str(i),['query','--no-build','+'+n+':depHash']);keys=re.findall(r'^[0-9a-f]{16}$',(D/('key'+str(i)+'.log')).read_text(),re.M);assert len(keys)==1;key=keys[0]
  if I['records'][n]['expected_key'] is not None:assert key==I['records'][n]['expected_key'],(n,'current root key drift')
  (D/('bound-key'+str(i)+'.json')).write_text(json.dumps({'target':n,'key':key,'dependencies_passed':True,'source_sha256':I['source_hashes1831'][n]})+'\\n');ready=run('ready'+str(i),['build','--no-build',n],allowed=(0,3))==0
  if not ready:
   rejected=re.findall(r'✖ .* Building ([\\w.]+)',(D/('ready'+str(i)+'.log')).read_text());assert set(rejected)=={n},(n,rejected)
   cache=[]
   for owner,root in [('A',Path('/home/lee/clifv/.worktrees/driver-proof-resume/.lake/artifact-cache')),('C',E/'892-current-main-context-v1/package/.lake/ci-cache')]:
    path=root/'outputs/fv'/(key+'.json')
    if path.exists():cache.append({'owner':owner,'descriptor':str(path),'sha256':sha(path)})
   (D/('cache'+str(i)+'.json')).write_text(json.dumps(cache,indent=2)+'\\n');assert not cache,(n,'Matching cache needs provenance review',cache)
   for area in ['lib/lean','ir']:
    stem=G/'.lake/build'/area/n.replace('.','/')
    for f in stem.parent.glob(stem.name+'.*'):
     if f.is_file() and (f.is_symlink() or f.stat().st_nlink!=1 or not f.stat().st_mode&0o200):
      tmp=f.with_name(f.name+'.consumer-lease-detach');shutil.copyfile(f,tmp);os.replace(tmp,f)
   run('kernel'+str(i),['-v','build','+'+n+':leanArts'])
  run('normal'+str(i),['build','--no-build',n]);trace=G/'.lake/build/lib/lean'/Path(n.replace('.','/')+'.trace');data=json.loads(trace.read_text());assert data.get('inputs') and not data.get('synthetic') and data['depHash']==key,(n,'candidate trace provenance');targets[n]={'native_key':key,'trace_sha256':sha(trace),'artifacts':artifacts(n),'reused_current_output':ready};(D/'passed-consumer-outputs.json').write_text(json.dumps(targets,indent=2)+'\\n')
finally:
 restoration=restore_config(D);(D/'gate-config-restoration.json').write_text(json.dumps(restoration,indent=2)+'\\n');(D/'lease-ended.json').write_text(json.dumps({'controller':os.getpid(),'config_restored':True})+'\\n')
run('all33-original-config',['build','--no-build',*I['conditional_topological_order33']]);run('complete1831-original-config',['build','--no-build',*sorted(I['source_hashes1831'])]);(D/'receipt.json').write_text(json.dumps({'status':'PASSED_CURRENT_GENERAL7_ALL33_CONSUMERS_AND_COMPLETE1831','manifest_sha256':sha(Q/'manifest.json'),'targets':targets,'records':records,'original_G_config_restored':True,'all30_previous_candidate_artifacts_unchanged':True,'full326_reverse_validation':'OPEN','Main_activation':'OPEN'},indent=2)+'\\n')
''';(D/'gate.py').write_text(gate)
for name in ['run.py','launch.py']:
 s=(old/name).read_text().replace("Q = E / 'general7-main-candidate-v1/direct31-remaining22-continuation-proposal-v1'", "Q = E / 'general7-main-candidate-v1/direct33-remaining-kernel-cone-v1'").replace('d91c57bccb37d97ba5d5d234e408718fb7043db71de71e7ac8e8f44eac32bb26',sha(Q/'manifest.json')).replace('worker-o-general7-direct31-cone22-','worker-o-General7-consumer33-').replace('general7-direct31-cone22-broad-resume-v2','General7-consumer33-broad-resume-v1').replace(sha(old/'gate.py'),sha(D/'gate.py'))
 if name=='run.py':
  s=s.replace("D = Path(__file__).resolve().parent","D = Path(__file__).resolve().parent\nfrom restore_config import restore_config")
  s=s.replace("'full_goal_complete': False}","'full_goal_complete': False, 'config_plan_sha256':sha(D/'config-restoration.json')}")
  s=s.replace("    if paused:\n        while busy():", "    if paused:\n        while busy():")
  s=s.replace("        os.kill(pid, signal.SIGCONT)\n        state.update(same_controller_resumed", "        state['configuration_restoration']=restore_config(D)\n        save()\n        os.kill(pid, signal.SIGCONT)\n        state.update(same_controller_resumed")
 (D/name).write_text(s)
guard=(old/'guard.py').read_text().replace('worker-o-general7-direct31-cone22-','worker-o-General7-consumer33-').replace("D = Path(__file__).resolve().parent","D = Path(__file__).resolve().parent\nimport hashlib\nfrom restore_config import restore_config")
guard=guard.replace("s = read()\n(D / 'guard-armed.json')", "s = read()\nassert hashlib.sha256((D/'config-restoration.json').read_bytes()).hexdigest()==s['config_plan_sha256']\n(D / 'guard-armed.json')")
guard=guard.replace("    if s.get('same_controller_resumed'):\n        break", "    if s.get('same_controller_resumed'):\n        restoration=restore_config(D)\n        break")
guard=guard.replace("        if not busy:\n            if alive", "        if not busy:\n            restoration=restore_config(D)\n            if alive")
guard=guard.replace("'emergency_resume': emergency,", "'emergency_resume': emergency, 'configuration_restoration':restoration,")
(D/'guard.py').write_text(guard);shutil.copyfile(old/'donor-config-allowlist.json',D/'donor-config-allowlist.json');print(D)
