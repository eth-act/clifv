from pathlib import Path
import datetime,fcntl,hashlib,json,os,re,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031';P=E/'direct-call-production-class-packet-v1';accepted=E/'direct-call-result-packet-v1'
lock=(E/'main870-cache-import.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
inventory=json.loads((P/'production-context-inventory-v24.json').read_text());ref=inventory['immutable_production']
assert not inventory['current_main_validation']
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=V,text=True).strip();assert head==inventory['carrier_head']
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=V,text=True).strip()
def blob(data):return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
for name,digest in inventory['configs'].items():assert blob((V/name).read_bytes())==digest,name
accepted_manifest=json.loads((E/'direct-call-result-packet-v1.json').read_text())
for name,digest in accepted_manifest['files'].items():assert hashlib.sha256((accepted/name).read_bytes()).hexdigest()==digest,name
overlays={str(f.relative_to(accepted)):f.read_bytes() for f in (accepted/'FV').rglob('*.lean')}
overlays.update({str(f.relative_to(P)):f.read_bytes() for prefix in ['FV','FVTest'] for f in (P/prefix).rglob('*.lean')})
sources={};imports={};todo=['FV/E2E/ResultCallProductionSelection.lean']
while todo:
 name=todo.pop()
 if name in sources:continue
 assert name in inventory['source_hashes'],('inventory incomplete',name)
 if name in overlays:data=overlays[name]
 else:
  digest=inventory['git_blobs'][name];carrier=V/name
  if carrier.exists() and blob(carrier.read_bytes())==digest:data=carrier.read_bytes()
  else:data=subprocess.check_output(['git','cat-file','blob',digest],cwd=B);assert blob(data)==digest,name
 assert hashlib.sha256(data).hexdigest()==inventory['source_hashes'][name],('source changed after declaration',name)
 sources[name]=data;deps={m.replace('.','/')+'.lean' for m in re.findall(r'^import\s+([\w.]+)',data.decode(),re.M) if m.startswith(('FV.','FVTest.'))};imports[name]=deps;todo.extend(deps-sources.keys())
assert set(sources)<=set(inventory['source_hashes'])
# Any changed source or dependency excludes its original carrier artifact.
affected={n for n,data in sources.items() if not (V/n).exists() or data!=(V/n).read_bytes() or not (V/'.lake/build/lib/lean'/Path(n).with_suffix('.olean')).exists()}
while True:
 delta={n for n,deps in imports.items() if deps&affected}-affected
 if not delta:break
 affected|=delta
root=P/'validation-package-v1';lib=root/'.lake/build/lib/lean';assert lib.exists()
old=json.loads((P/'actual-symbolic-reuse-v2.json').read_text());assert old['status']=='passed'
changed={n for n in affected if not (lib/Path(n).with_suffix('.olean')).exists() or old['source_hashes'].get(n)!=hashlib.sha256(sources[n]).hexdigest()}
while True:
 delta={n for n,deps in imports.items() if deps&changed}-changed
 if not delta:break
 changed|=delta
for name in changed:
 target=root/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(sources[name])
 for suffix in ['.olean','.ilean','.olean.private','.olean.server','.c']:
  artifact=lib/(str(Path(name).with_suffix(''))+suffix)
  if artifact.exists():artifact.unlink()
for name in set(sources)-affected:
 for suffix in ['.olean','.ilean','.olean.private','.olean.server']:
  original=V/'.lake/build/lib/lean'/(str(Path(name).with_suffix(''))+suffix)
  target=lib/(str(Path(name).with_suffix(''))+suffix)
  if original.exists() and not target.exists():target.parent.mkdir(parents=True,exist_ok=True);os.link(original,target)
affected=changed
ordered=[];pending=set(affected)
while pending:
 ready=sorted(n for n in pending if not imports[n]&pending);assert ready;ordered+=ready;pending.difference_update(ready)
logs=P/'actual-symbolic-exec-kernel-v3';assert not logs.exists();logs.mkdir()
context=dict(status='running',context='immutable90c production predecessor plus declared owned changes; not current-main validation',root=str(root),head=head,ordered=ordered,source_hashes={n:hashlib.sha256(d).hexdigest() for n,d in sources.items()},effective_lean_jobs=1,cap='2G',utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(logs/'context.json').write_text(json.dumps(context,indent=2)+'\n');print('Rebuild modules:',len(ordered),flush=True)
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(V),FV_MEMCAP='2G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false');env['LEAN_PATH']=str(lib)+':'+subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,env=env,text=True).strip()
for idx,name in enumerate(ordered):
 env['FV_MEMCAP_STATS']=str(logs/(name.replace('/','_')+'.mem'));env['FV_MEMCAP_UNIT']='worker-o-result-call-generated-consumer-v1-'+str(idx);target=lib/Path(name).with_suffix('');target.parent.mkdir(parents=True,exist_ok=True)
 cmd=['nice','-n','10',str(V/'scripts/memcap.sh'),'lake','env','lean','-j1','-DElab.async=false','--root='+str(root),str(root/name),'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c']
 with (logs/(name.replace('/','_')+'.log')).open('w') as out:result=subprocess.run(cmd,cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT)
 print('KERNEL',name,'exit',result.returncode,flush=True)
 if result.returncode:
  (logs/'failed-source.lean').write_bytes((root/name).read_bytes())
  context.update(status='failed',failed_module=name,exit_code=result.returncode);(logs/'result.json').write_text(json.dumps(context,indent=2)+'\n');raise SystemExit(result.returncode)
context.update(status='passed');(logs/'result.json').write_text(json.dumps(context,indent=2)+'\n')
