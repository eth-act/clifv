from pathlib import Path
import datetime,fcntl,hashlib,json,os,re,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031';packet=E/'typed-compiler-modes-packet-v1';prior_root=E/'return-pin-consumer-isolated-package-v1';prior=json.loads((E/'return-pin-consumer-isolated-state-v3.json').read_text())
lock=(E/'main870-cache-import.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=V,text=True).strip()=='a4c0726d46c5908b4ac06cf797ee939af8644703'
manifest=json.loads((E/'typed-compiler-modes-packet-v1.json').read_text());overlays={}
for name,digest in prior['source_hashes'].items():
 if name.startswith(('FV/','FVTest/')):
  data=(prior_root/name).read_bytes();assert hashlib.sha256(data).hexdigest()==digest,name;overlays[name]=data
for name,digest in manifest['files'].items():
 data=(packet/name).read_bytes();assert hashlib.sha256(data).hexdigest()==digest,name
 if name.startswith('FV/'):overlays[name]=data

for extra in ['void-call-file-packet-v1','return-pin-source-adapter-packet-v1']:
 for f in (E/extra).rglob('*.lean'):
  name=str(f.relative_to(E/extra))
  if name.startswith(('FV/','FVTest/')):overlays[name]=f.read_bytes()
for name in manifest['files']:
 if name.startswith(('FV/','FVTest/')):overlays[name]=(packet/name).read_bytes()
roots={name for name in manifest['files'] if name.startswith(('FV/','FVTest/'))};imports={};sources={};todo=list(roots)
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
for name in sources:
 if not (V/'.lake/build/lib/lean'/Path(name).with_suffix('.olean')).exists():affected.add(name)
while True:
 delta={name for name,deps in imports.items() if deps&affected}-affected
 if not delta:break
 affected|=delta
assert len(affected)<=100,len(affected)
root=packet/'validation-package-v1';assert not root.exists();root.mkdir();(root/'lakefile.toml').write_text('name = "returnpinsourcegate"\nversion = "0.1.0"\n\n[[lean_lib]]\nname = "FV"\n');(root/'lean-toolchain').write_bytes((V/'lean-toolchain').read_bytes())
for name in affected:
 target=root/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(sources[name])
for name in manifest['files']:
 if name.startswith('scripts/audit/'):
  target=root/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((packet/name).read_bytes())
lib=root/'.lake/build/lib/lean';lib.mkdir(parents=True)
for f in (V/'.lake/build/lib/lean').rglob('*'):
 if not f.is_file() or not any(f.name.endswith(s) for s in ['.olean','.ilean','.olean.private','.olean.server']):continue
 rel=f.relative_to(V/'.lake/build/lib/lean')
 if any(str(rel).startswith(str(Path(n).with_suffix(''))+'.') for n in affected):continue
 target=lib/rel;target.parent.mkdir(parents=True,exist_ok=True);os.link(f,target)
ordered=[];pending=set(affected)
while pending:
 ready=sorted(n for n in pending if not imports[n]&pending);assert ready;ordered+=ready;pending.difference_update(ready)
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(V),FV_MEMCAP='3G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false');env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,env=env,text=True).strip();logs=packet/'kernel-v1';assert not logs.exists();logs.mkdir();context=dict(root=str(root),head='a4c0726d46c5908b4ac06cf797ee939af8644703',modules=ordered,source_hashes={n:hashlib.sha256(d).hexdigest() for n,d in sources.items()},status='running');(logs/'context.json').write_text(json.dumps(context,indent=2)+'\n');print('Rebuild modules:',len(ordered),flush=True)
for idx,name in enumerate(ordered):
 env['FV_MEMCAP_STATS']=str(logs/(name.replace('/','_')+'.mem'));env['FV_MEMCAP_UNIT']='worker-o-activation-fresh-v1-'+str(idx)
 target=lib/Path(name).with_suffix('');target.parent.mkdir(parents=True,exist_ok=True)
 with (logs/(name.replace('/','_')+'.log')).open('w') as out:subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'lake','env','lean','--root='+str(root),str(root/name),'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c'],cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
 print('KERNEL',name,'passed',flush=True)
with (logs/'audit-summary.log').open('w') as out:subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'python3',str(V/'scripts/axiom-audit.py'),'--cwd',str(root),'--log-dir',str(logs/'audit'),str(root/'scripts/audit/typed-compiler-modes.lean')],cwd=V,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=V,text=True).strip()==context['head'];context.update(status='passed',generic_roots=10,fixed_roots=0,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(packet/'state-v1.json').write_text(json.dumps(context,indent=2)+'\n');print('Production activation modules and mixed-mode witnesses passed.',flush=True)
