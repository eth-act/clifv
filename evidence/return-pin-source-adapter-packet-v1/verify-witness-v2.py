from pathlib import Path
import datetime,fcntl,hashlib,json,os,re,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031';packet=E/'return-pin-source-adapter-packet-v1';root=packet/'validation-package-v1';lib=root/'.lake/build/lib/lean'
lock=(E/'main870-cache-import.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
old=json.loads((packet/'generic-state-v1.json').read_text());assert old['status']=='passed';prior=json.loads((E/'return-pin-consumer-isolated-state-v3.json').read_text());prior_root=E/'return-pin-consumer-isolated-package-v1';manifest=json.loads((E/'return-pin-source-adapter-packet-v1.json').read_text());overlays={}
for name,digest in prior['source_hashes'].items():
 if name.startswith(('FV/','FVTest/')):
  data=(prior_root/name).read_bytes();assert hashlib.sha256(data).hexdigest()==digest,name;overlays[name]=data
for name,digest in manifest['files'].items():
 data=(packet/name).read_bytes();assert hashlib.sha256(data).hexdigest()==digest,name
 if name.startswith('FV/'):overlays[name]=data
sources={};imports={};todo=['FV/Link/ReturnPinExeSourceWitness.lean']
while todo:
 name=todo.pop()
 if name in sources:continue
 data=overlays.get(name)
 if data is None:data=(V/name).read_bytes()
 sources[name]=data;deps={m.replace('.','/')+'.lean' for m in re.findall(r'^import\s+([\w.]+)',data.decode(),re.M) if m.startswith(('FV.','FVTest.'))};imports[name]=deps;todo.extend(deps-sources.keys())
affected={name for name,data in sources.items() if not (V/name).exists() or data!=(V/name).read_bytes()}
while True:
 delta={name for name,deps in imports.items() if deps&affected}-affected
 if not delta:break
 affected|=delta
already={name for name in affected if name in old['modules'] and hashlib.sha256(sources[name]).hexdigest()==old['source_hashes'][name] and (lib/Path(name).with_suffix('.olean')).exists()}
needed={'FV/Link/ReturnPinExeSourceWitness.lean'}
assert all((lib/Path(name).with_suffix('.olean')).exists() for name in affected-needed)
for name in sources:
 if not (lib/Path(name).with_suffix('.olean')).exists():needed.add(name)
assert len(needed)<=20,len(needed)
for name in needed:
 target=root/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(sources[name])
for name in manifest['files']:
 if name.startswith('scripts/audit/'):
  target=root/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((packet/name).read_bytes())
ordered=[];pending=set(needed)
while pending:
 ready=sorted(n for n in pending if not imports[n]&pending);assert ready;ordered+=ready;pending.difference_update(ready)
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(V),FV_MEMCAP='3G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false');env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,env=env,text=True).strip();logs=packet/'witness-kernel-v2';assert not logs.exists();logs.mkdir();print('Incremental modules:',len(ordered),flush=True)
for index,name in enumerate(ordered):
 target=lib/Path(name).with_suffix('');target.parent.mkdir(parents=True,exist_ok=True)
 for suffix in ['.olean','.ilean','.olean.private','.olean.server','.c']:
  artifact=Path(str(target)+suffix)
  if artifact.exists():artifact.unlink()
 env['FV_MEMCAP_STATS']=str(logs/(Path(name).stem+'.mem'));env['FV_MEMCAP_UNIT']='worker-o-source-witness-v2-'+str(index)
 with (logs/(Path(name).stem+'.log')).open('w') as out:subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'lake','env','lean','--root='+str(root),str(root/name),'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c'],cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
 print('KERNEL',name,'passed',flush=True)
env['FV_MEMCAP_STATS']=str(logs/'audits.mem');env['FV_MEMCAP_UNIT']='worker-o-source-witness-v2-audits'
with (logs/'audit-summary.log').open('w') as out:subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'python3',str(V/'scripts/axiom-audit.py'),'--cwd',str(root),'--log-dir',str(logs/'audit'),str(root/'scripts/audit/return-pin-executable-source.lean'),str(root/'scripts/audit/return-pin-executable-source-witness.lean')],cwd=V,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=V,text=True).strip()==old['head']
peaks={p.stem:dict(line.split() for line in p.read_text().splitlines()) for p in logs.glob('*.mem')}
receipt=dict(status='passed',head=old['head'],source_hashes=manifest['files'],isolated_package=str(root),generic_modules_reused=old['modules'],incremental_modules=ordered,generic_roots=2,fixed_roots=2,measured_memory=peaks,requires_current_main_gates=True,full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(packet/'witness-state-v2.json').write_text(json.dumps(receipt,indent=2)+'\n');print('Original-source and peak-source witnesses passed in both cleanup modes with arbitrary arguments.',flush=True)
