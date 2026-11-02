from pathlib import Path
import datetime,fcntl,hashlib,json,os,re,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031'
lock=(E/'main870-cache-import.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
pre=json.loads((E/'return-pin-consumer-isolated-preflight-v1.json').read_text())
def git(*args):return subprocess.check_output(['git',*args],cwd=V,text=True).strip()
head=git('rev-parse','HEAD');assert head=='a4c0726d46c5908b4ac06cf797ee939af8644703' and not git('status','--porcelain')
root=E/'return-pin-consumer-isolated-package-v1';assert not root.exists();root.mkdir()
(root/'lakefile.toml').write_text('name = "returnpinconsumergate"\nversion = "0.1.0"\n\n[[lean_lib]]\nname = "FV"\n\n[[lean_lib]]\nname = "FVTest"\n')
(root/'lean-toolchain').write_bytes((V/'lean-toolchain').read_bytes())
sources={};hashes={};audits=[]
for packet in pre['packets']:
 manifest=json.loads((E/(packet+'.json')).read_text())
 for name,digest in manifest['files'].items():
  data=(E/packet/name).read_bytes();assert hashlib.sha256(data).hexdigest()==digest
  target=root/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data);hashes[name]=digest
  if name.startswith(('FV/','FVTest/')):sources[name]=data
  elif name.startswith('scripts/audit/'):audits.append(name)
imports={};pending=list(sources)
while pending:
 name=pending.pop()
 if name in imports:continue
 if name not in sources:sources[name]=(V/name).read_bytes()
 deps={m.replace('.','/')+'.lean' for m in re.findall(r'^import\s+([\w.]+)',sources[name].decode(),re.M) if m.startswith(('FV.','FVTest.'))};imports[name]=deps;pending.extend(deps-imports.keys())
affected=set(pre['affected']);assert affected<=sources.keys()
for name in affected:
 p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(sources[name]);hashes[name]=hashlib.sha256(sources[name]).hexdigest()
# Import modules whose current output is absent must also compile. Keep all inherited imports coherent.
for name in imports:
 if not (V/'.lake/build/lib/lean'/Path(name).with_suffix('.olean')).exists():affected.add(name)
while True:
 delta={n for n,d in imports.items() if d&affected}-affected
 if not delta:break
 affected|=delta
for name in affected:
 p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(sources[name]);hashes[name]=hashlib.sha256(sources[name]).hexdigest()
ordered=[];pending=set(affected)
while pending:
 ready=sorted(n for n in pending if not imports[n]&pending);assert ready,'Import cycle';ordered+=ready;pending.difference_update(ready)
assert len(ordered)<=60,('Unexpected rebuild growth',len(ordered))
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(V),LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',FV_MEMCAP='3G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2')
env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,env=env,text=True).strip()
lib=root/'.lake/build/lib/lean';lib.mkdir(parents=True)
for prefix in ['FV','FVTest']:
 for f in (V/'.lake/build/lib/lean'/prefix).rglob('*'):
  if not f.is_file() or not any(f.name.endswith(s) for s in ['.olean','.ilean','.olean.private','.olean.server']):continue
  rel=f.relative_to(V/'.lake/build/lib/lean')
  if any(str(rel).startswith(str(Path(n).with_suffix(''))+'.') for n in affected):continue
  target=lib/rel;target.parent.mkdir(parents=True,exist_ok=True);os.link(f,target)
logs=E/'return-pin-consumer-isolated-kernel-v1';assert not logs.exists();logs.mkdir()
context=dict(head=head,packets=pre['packets'],modules=ordered,source_hashes=hashes,import_source_hashes={n:hashlib.sha256(d).hexdigest() for n,d in sources.items()},status='running',isolated_package=str(root),full_goal_complete=False)
(logs/'context.json').write_text(json.dumps(context,indent=2)+'\n')
print('Actual closure',len(imports),'rebuild modules',len(ordered),flush=True)
for name in ordered:
 target=lib/Path(name).with_suffix('');target.parent.mkdir(parents=True,exist_ok=True)
 with (logs/(Path(name).stem+'.log')).open('w') as out:
  subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'lake','env','lean','--root='+str(root),str(root/name),'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c'],cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
 print('KERNEL',name,'passed',flush=True)
for name in audits:
 label=Path(name).stem
 with (logs/(label+'-audit-summary.log')).open('w') as out:
  subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'python3',str(V/'scripts/axiom-audit.py'),'--cwd',str(root),'--log-dir',str(logs/(label+'-audit')),str(root/name)],cwd=V,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
 print('AUDIT',name,'passed',flush=True)
assert git('rev-parse','HEAD')==head and not git('status','--porcelain')
context.update(status='passed',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),requires_current_main_gates=True)
(E/'return-pin-consumer-isolated-state-v1.json').write_text(json.dumps(context,indent=2)+'\n')
print('All candidate modules and unchanged audits passed. Current-main importer and publication gates remain required.',flush=True)
