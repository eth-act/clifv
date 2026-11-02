from pathlib import Path
import datetime,fcntl,hashlib,json,os,re,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031';packet=E/'direct-call-result-packet-v1';prior_root=E/'return-pin-consumer-isolated-package-v1';prior=json.loads((E/'return-pin-consumer-isolated-state-v3.json').read_text())
lock=(E/'main870-cache-import.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=V,text=True).strip()=='a4c0726d46c5908b4ac06cf797ee939af8644703'
manifest={'files':{str(f.relative_to(packet)):hashlib.sha256(f.read_bytes()).hexdigest() for root in ['FV','FVTest','scripts/audit'] for f in (packet/root).rglob('*.lean')}};overlays={}
for name,digest in prior['source_hashes'].items():
 if name.startswith(('FV/','FVTest/')):
  data=(prior_root/name).read_bytes();assert hashlib.sha256(data).hexdigest()==digest;overlays[name]=data
for extra in ['void-call-file-packet-v1','return-pin-source-adapter-packet-v1','return-pin-production-activation-packet-v1','return-pin-typed-proof-packet-v1']:
 for prefix in ['FV','FVTest']:
  for f in (E/extra/prefix).rglob('*.lean'):overlays[str(f.relative_to(E/extra))]=f.read_bytes()
for name in manifest['files']:
 if name.startswith(('FV/','FVTest/')):overlays[name]=(packet/name).read_bytes()
roots={'FV/Backend/Proof/StockDirectCallResultWitness.lean'};imports={};sources={};todo=list(roots)
while todo:
 name=todo.pop()
 if name in sources:continue
 data=overlays.get(name)
 if data is None:data=(V/name).read_bytes()
 sources[name]=data;deps={m.replace('.','/')+'.lean' for m in re.findall(r'^import\s+([\w.]+)',data.decode(),re.M) if m.startswith(('FV.','FVTest.'))};imports[name]=deps;todo.extend(deps-sources.keys())
root=packet/'validation-package-v1';lib=root/'.lake/build/lib/lean';old=json.loads((packet/'state-v2.json').read_text());assert old['status']=='passed'
affected={n for n,data in sources.items() if not (lib/Path(n).with_suffix('.olean')).exists() or (old['source_hashes'].get(n)!=hashlib.sha256(data).hexdigest() and (not (V/n).exists() or data!=(V/n).read_bytes()))}
while True:
 delta={n for n,deps in imports.items() if deps&affected}-affected
 if not delta:break
 affected|=delta
for name in affected:
 target=root/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(sources[name])
 for suffix in ['.olean','.ilean','.olean.private','.olean.server','.c']:
  artifact=Path(str(lib/Path(name).with_suffix(''))+suffix)
  if artifact.exists():artifact.unlink()

for f in (packet/'scripts/audit').glob('*.lean'):
 target=root/'scripts/audit'/f.name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(f.read_bytes())
ordered=[];pending=set(affected)
while pending:
 ready=sorted(n for n in pending if not imports[n]&pending);assert ready;ordered+=ready;pending.difference_update(ready)
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(V),FV_MEMCAP='3G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false');env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,env=env,text=True).strip();logs=packet/'witness-kernel-v6';assert not logs.exists();logs.mkdir();context=dict(root=str(root),head='a4c0726d46c5908b4ac06cf797ee939af8644703',modules=ordered,source_hashes={n:hashlib.sha256(d).hexdigest() for n,d in sources.items()},status='running');(logs/'context.json').write_text(json.dumps(context,indent=2)+'\n');print('Rebuild modules:',len(ordered),flush=True)
for idx,name in enumerate(ordered):
 env['FV_MEMCAP_STATS']=str(logs/(name.replace('/','_')+'.mem'));env['FV_MEMCAP_UNIT']='worker-o-activation-fresh-v1-'+str(idx)
 target=lib/Path(name).with_suffix('');target.parent.mkdir(parents=True,exist_ok=True)
 with (logs/(name.replace('/','_')+'.log')).open('w') as out:subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'lake','env','lean','--root='+str(root),str(root/name),'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c'],cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
 print('KERNEL',name,'passed',flush=True)
with (logs/'audit-summary.log').open('w') as out:subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'python3',str(V/'scripts/axiom-audit.py'),'--cwd',str(root),'--log-dir',str(logs/'audit'),str(root/'scripts/audit/stock-direct-call-result.lean'),str(root/'scripts/audit/stock-direct-call-result-witness.lean')],cwd=V,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=V,text=True).strip()==context['head'];context.update(status='passed',generic_roots=10,fixed_roots=1,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(packet/'witness-state-v6.json').write_text(json.dumps(context,indent=2)+'\n');print('Production activation modules and mixed-mode witnesses passed.',flush=True)
