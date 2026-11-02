from pathlib import Path
import datetime,hashlib,json,os,re,shutil,subprocess,psutil
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';T=Path(__file__).resolve().parent;Q=T.parent;R=Q/'validation-package-v1';J=E/'892-joint-current-context-v2/package';L=T/'nine-providers-v1';L.mkdir();base='37fc00cb91cf37557777f0664878a164c59587cf';todo=['FV/E2E/RegLevelTrapCall.lean','FV/E2E/DeadCleanupTrapCall.lean','FV/E2E/LinkTrapCall.lean'];sources={};dag={}
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
 return h.hexdigest()
while todo:
 n=todo.pop()
 if n in sources:continue
 data=subprocess.check_output(['git','show',base+':'+n],cwd=B);assert (J/n).read_bytes()==data,n;sources[n]=data;dag[n]=[x.replace('.','/')+'.lean' for x in re.findall(r'^import\s+([\w.]+)',data.decode(),re.M) if x.startswith(('FV.','FVTest.'))];todo.extend(dag[n])
missing=set(json.loads((T/'trap-link-missing-providers-v1.json').read_text())['missing']);assert len(sources)==386 and len(missing)==9
active=[]
for p in psutil.process_iter(['pid','name','cmdline','status']):
 try:
  if p.info['name']!='lean' or p.info['status']=='zombie':continue
  for arg in p.info['cmdline'] or []:
   if arg.startswith(str(J)+'/') and arg.endswith('.lean') and str(Path(arg).relative_to(J)) in sources:active.append(dict(pid=p.pid,path=arg))
 except(psutil.NoSuchProcess,psutil.AccessDenied):pass
assert not active,('Active baseline provider',active)
for n,data in sources.items():
 p=R/n;p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():assert p.read_bytes()==data,n
 else:p.write_bytes(data)
 if n in missing:continue
 stem=Path(n).with_suffix('')
 for area in ['lib/lean','ir']:
  p=J/'.lake/build'/area/stem
  for src in p.parent.glob(p.name+'.*'):
   if not src.is_file():continue
   dest=R/src.relative_to(J)
   if dest.exists():continue
   dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest)
configs={n:sha(R/n) for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']}
for n in configs:
 published=subprocess.check_output(['git','show',base+':'+n],cwd=B);expected=published.replace(b'weakLeanArgs = [',b'weakLeanArgs = ["-j1",',1) if n=='lakefile.toml' else published;assert (R/n).read_bytes()==expected,n
keys={}
def key(n):
 if n not in keys:keys[n]=hashlib.sha256(json.dumps([configs,hashlib.sha256(sources[n]).hexdigest(),[(d,key(d)) for d in sorted(dag[n])]],sort_keys=True).encode()).hexdigest()
 return keys[n]
for n in sources:key(n)
provider_records={}
for n in sorted(set(sources)-missing):
 stem=R/'.lake/build/lib/lean'/Path(n).with_suffix('');trace=json.loads(stem.with_suffix('.trace').read_text());assert not trace.get('synthetic',False),n
 provider_records[n]=dict(native_key=trace['depHash'],outputs=trace['outputs'],artifact_hashes={str(p.relative_to(R)):sha(p) for p in stem.parent.glob(stem.name+'.*') if p.is_file()},dependency_source_key=keys[n])
ordered=[];pending=set(missing)
while pending:
 ready=sorted(n for n in pending if not set(dag[n])&pending);assert ready;ordered+=ready;pending.difference_update(ready)
context=dict(status='prepared377-provider-normal-check',base=base,source_hashes={n:hashlib.sha256(v).hexdigest() for n,v in sources.items()},imports=dag,dependency_source_keys=keys,configs=configs,other377=provider_records,nine_order=ordered,no_duplicate_active_provider=True,budget='3G-j1; temporary extra1G lease',no_shared_writes=True,native_nine_keys_recorded_after_each_real_kernel=True);(L/'context.json').write_text(json.dumps(context,indent=2)+'\n')
env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LAKE_CACHE_DIR']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(R),FV_MEMCAP='3G',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1');records=[]
def run(label,argv):
 env['FV_MEMCAP_STATS']=str(L/(label+'.mem'));env['FV_MEMCAP_UNIT']='worker-o-call-store-nine-'+label
 with (L/(label+'.log')).open('w') as stream:rc=subprocess.call([str(J/'scripts/memcap.sh'),*argv],cwd=R,env=env,stdout=stream,stderr=subprocess.STDOUT)
 records.append(dict(label=label,argv=argv,exit=rc,stats=(L/(label+'.mem')).read_text() if (L/(label+'.mem')).exists() else None));(L/'progress.json').write_text(json.dumps(dict(status='running' if rc==0 else 'failed',records=records),indent=2)+'\n');print(label,'exit',rc,flush=True)
 if rc:raise SystemExit(rc)
run('other377-normal',['lake','build','--no-build',*[n[:-5].replace('/','.') for n in sorted(set(sources)-missing)]])
new_outputs={}
for i,n in enumerate(ordered):
 run('leaf-'+str(i),['lake','build','+'+n[:-5].replace('/','.')+':leanArts'])
 stem=R/'.lake/build/lib/lean'/Path(n).with_suffix('');trace=json.loads(stem.with_suffix('.trace').read_text());assert not trace.get('synthetic',False),n
 new_outputs[n]=dict(native_key=trace['depHash'],outputs=trace['outputs'],artifact_hashes={str(p.relative_to(R)):sha(p) for p in stem.parent.glob(stem.name+'.*') if p.is_file()},dependency_source_key=keys[n]);(L/'completed-outputs.json').write_text(json.dumps(new_outputs,indent=2)+'\n')
run('complete386-normal',['lake','build','--no-build',*[n[:-5].replace('/','.') for n in sorted(sources)]])
context.update(status='passed386-normal-keys-nine-owned-leaves',records=records,nine_outputs=new_outputs,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(L/'receipt.json').write_text(json.dumps(context,indent=2)+'\n');print('nine-provider batch passed',flush=True)
