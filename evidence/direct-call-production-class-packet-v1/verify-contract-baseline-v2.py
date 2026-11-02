from pathlib import Path
import datetime,fcntl,hashlib,json,os,re,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031';P=E/'direct-call-production-class-packet-v1';accepted=E/'direct-call-result-packet-v1'
lock=(E/'main870-cache-import.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
declaration=json.loads((E/'result-call-immutable-contract-baseline-context-v2.json').read_text())
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=V,text=True).strip()
assert head==declaration['observed_view']
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=V,text=True).strip()
def tree(ref):
 out=subprocess.check_output(['git','ls-tree','-r',ref],cwd=B,text=True)
 return {line.split('\t',1)[1]:line.split()[2] for line in out.splitlines()}
def blob(data):return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
baseline=tree(declaration['immutable_baseline']);carrier=tree(head);production=tree(declaration['prior_production_baseline'])
for name,digest in declaration['project_source_closure'].items():
 assert baseline[name]==carrier[name]==production[name]==digest,name
 assert blob((V/name).read_bytes())==digest,name
config_names=[n for n in ['lakefile.toml','lakefile.lean','lake-manifest.json','lean-toolchain'] if (V/n).exists()]
assert len(config_names)==3,config_names
for name in config_names:
 assert baseline[name]==carrier[name]==production[name]==blob((V/name).read_bytes()),name
overlays={str(x.relative_to(accepted)):x.read_bytes() for x in (accepted/'FV').rglob('*.lean')}
overlays.update({str(x.relative_to(P)):x.read_bytes() for x in (P/'FV').rglob('*.lean')})
baseline_files=json.loads((P/'shared-baseline-v1/manifest.json').read_text())['files']
for name,digest in baseline_files.items():
 data=(P/'shared-baseline-v1'/name).read_bytes();assert hashlib.sha256(data).hexdigest()==digest
 overlays[name]=data
accepted_manifest=json.loads((E/'direct-call-result-packet-v1.json').read_text())
for name,sha in accepted_manifest['files'].items():assert hashlib.sha256((accepted/name).read_bytes()).hexdigest()==sha,name
sources={};imports={};todo=list(overlays)
while todo:
 name=todo.pop()
 if name in sources:continue
 data=overlays[name] if name in overlays else (V/name).read_bytes();sources[name]=data
 deps={m.replace('.','/')+'.lean' for m in re.findall(r'^import\s+([\w.]+)',data.decode(),re.M) if m.startswith(('FV.','FVTest.'))};imports[name]=deps;todo.extend(deps-sources.keys())
for name,data in sources.items():
 if name not in overlays:
  assert baseline[name]==blob(data),name
affected={n for n,data in sources.items() if not (V/n).exists() or data!=(V/n).read_bytes() or not (V/'.lake/build/lib/lean'/Path(n).with_suffix('.olean')).exists()}
while True:
 delta={n for n,deps in imports.items() if deps&affected}-affected
 if not delta:break
 affected|=delta
root=P/'validation-package-v1';assert root.exists();root.mkdir(exist_ok=True);(root/'lakefile.toml').write_text('name = "resultcallgate"\nversion = "0.1.0"\n\n[[lean_lib]]\nname = "FV"\n');(root/'lean-toolchain').write_bytes((V/'lean-toolchain').read_bytes());lib=root/'.lake/build/lib/lean';lib.mkdir(parents=True)
for name in sources:
 if name in affected:
  target=root/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(sources[name])
 else:
  stem=Path(name).with_suffix('')
  for suffix in ['.olean','.ilean','.olean.private','.olean.server']:
   original=V/'.lake/build/lib/lean'/(str(stem)+suffix)
   if original.exists():
    target=lib/(str(stem)+suffix);target.parent.mkdir(parents=True,exist_ok=True);os.link(original,target)
ordered=[];pending=set(affected)
while pending:
 ready=sorted(n for n in pending if not imports[n]&pending);assert ready;ordered+=ready;pending.difference_update(ready)
logs=P/'contract-baseline-kernel-v2';assert not logs.exists();logs.mkdir()
context=dict(status='running',context='preserved frozen source; fast inner loop only, not current-main validation',root=str(root),head=head,ordered=ordered,source_hashes={n:hashlib.sha256(d).hexdigest() for n,d in sources.items()},effective_lean_jobs=1,cap='2G',utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(logs/'context.json').write_text(json.dumps(context,indent=2)+'\n');print('Rebuild modules:',len(ordered),flush=True)
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(V),FV_MEMCAP='2G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false');env['LEAN_PATH']=str(lib)+':'+subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,env=env,text=True).strip()
for idx,name in enumerate(ordered):
 env['FV_MEMCAP_STATS']=str(logs/(name.replace('/','_')+'.mem'));env['FV_MEMCAP_UNIT']='worker-o-result-call-contract-baseline-v2-'+str(idx);target=lib/Path(name).with_suffix('');target.parent.mkdir(parents=True,exist_ok=True)
 cmd=['nice','-n','10',str(V/'scripts/memcap.sh'),'lake','env','lean','-j1','-DElab.async=false','--root='+str(root),str(root/name),'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c']
 with (logs/(name.replace('/','_')+'.log')).open('w') as out:result=subprocess.run(cmd,cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT)
 print('KERNEL',name,'exit',result.returncode,flush=True)
 if result.returncode:
  (logs/'failed-source.lean').write_bytes((root/name).read_bytes())
  context.update(status='failed',failed_module=name,exit_code=result.returncode);(logs/'result.json').write_text(json.dumps(context,indent=2)+'\n');raise SystemExit(result.returncode)
context.update(status='passed');(logs/'result.json').write_text(json.dumps(context,indent=2)+'\n')
