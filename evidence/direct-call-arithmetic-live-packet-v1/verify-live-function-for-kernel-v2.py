from pathlib import Path
import hashlib,json,os,re,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';Q=E/'direct-call-arithmetic-live-packet-v1';V=B/'.worktrees/stock-extending-production-20261031';R=Q/'validation-package-v1';lib=R/'.lake/build/lib/lean';logs=Q/'live-function-for-kernel-v2';logs.mkdir()
base=json.loads((Q/'predecessor-source-context-v1.json').read_text());assert base['carrier_head']==subprocess.check_output(['git','rev-parse','HEAD'],cwd=V,text=True).strip()
accepted=E/'direct-call-result-packet-v1';am=json.loads((E/'direct-call-result-packet-v1.json').read_text())
for n,h in am['files'].items():assert hashlib.sha256((accepted/n).read_bytes()).hexdigest()==h
ref=base['immutable_production'];sources={};dag={};todo=['FV/E2E/StockLiveCallFunction.lean']
while todo:
 n=todo.pop()
 if n in sources:continue
 if (Q/n).exists():data=(Q/n).read_bytes()
 elif (accepted/n).exists():data=(accepted/n).read_bytes()
 elif (E/'direct-call-production-class-packet-v1'/n).exists():
  data=(E/'direct-call-production-class-packet-v1'/n).read_bytes();assert hashlib.sha256(data).hexdigest()==base['owned_predecessor_sources'][n],('immutable predecessor changed',n)
 else:data=subprocess.check_output(['git','show',ref+':'+n],cwd=B);assert (V/n).read_bytes()==data,('carrier dependency source changed',n)
 sources[n]=data;deps={m.replace('.','/')+'.lean' for m in re.findall(r'^import\s+([\w.]+)',data.decode(),re.M) if m.startswith(('FV.','FVTest.'))};dag[n]=deps;todo.extend(deps-sources.keys())
changed={n for n,data in sources.items() if not (V/n).exists() or (V/n).read_bytes()!=data or not (V/'.lake/build/lib/lean'/Path(n).with_suffix('.olean')).exists()}
while True:
 extra={n for n,deps in dag.items() if deps&changed}-changed
 if not extra:break
 changed|=extra
for n in set(sources)-changed:
 for suffix in ['.olean','.olean.private','.olean.server','.ilean']:
  src=V/'.lake/build/lib/lean'/Path(n).with_suffix(suffix);dst=lib/Path(n).with_suffix(suffix)
  if src.exists() and not dst.exists():dst.parent.mkdir(parents=True,exist_ok=True);os.link(src,dst)
keys={}
def key(n):
 if n not in keys:keys[n]=hashlib.sha256(json.dumps([base['configs'],hashlib.sha256(sources[n]).hexdigest(),[(d,key(d)) for d in sorted(dag[n])]],sort_keys=True).encode()).hexdigest()
 return keys[n]
for n in sources:key(n)
previous=json.loads((Q/'live-function-kernel-v2/result.json').read_text());assert previous['status']=='passed';completed=previous['ordered']+list(json.loads((Q/'live-function-kernel-v2/reused-module-keys.json').read_text()))
reused={n:keys[n] for n in completed if n in changed and previous['dependency_keys'].get(n)==keys[n] and (lib/Path(n).with_suffix('.olean')).exists()}
changed.difference_update(reused)
(logs/'reused-module-keys.json').write_text(json.dumps(reused,indent=2)+'\n')
for n in changed:
 dst=R/n;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(sources[n])
 for suffix in ['.olean','.olean.private','.olean.server','.ilean','.c']:
  dst=lib/Path(n).with_suffix(suffix)
  if dst.exists():dst.unlink()
ordered=[];pending=set(changed)
while pending:
 ready=sorted(n for n in pending if not dag[n]&pending);assert ready;ordered+=ready;pending.difference_update(ready)
context=dict(status='running',source_hashes={n:hashlib.sha256(d).hexdigest() for n,d in sources.items()},dependency_keys=keys,configs=base['configs'],ordered=ordered,cap='2G',lean_jobs=1,current_main_validation=False);(logs/'context.json').write_text(json.dumps(context,indent=2)+'\n')
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(V),FV_MEMCAP='2G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false');env['LEAN_PATH']=str(lib)+':'+subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,env=env,text=True).strip()
for index,n in enumerate(ordered):
 env['FV_MEMCAP_STATS']=str(logs/(n.replace('/','_')+'.mem'));env['FV_MEMCAP_UNIT']='worker-o-live-arithmetic-v1-'+str(index);target=lib/Path(n).with_suffix('');target.parent.mkdir(parents=True,exist_ok=True)
 with (logs/(n.replace('/','_')+'.log')).open('w') as out:r=subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'lake','env','lean','-j1','-DElab.async=false','--root='+str(R),str(R/n),'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c'],cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT)
 print(n,'exit',r.returncode,flush=True)
 if r.returncode:
  (logs/'failed-source.lean').write_bytes(sources[n]);context.update(status='failed',failed_module=n,exit_code=r.returncode);(logs/'result.json').write_text(json.dumps(context,indent=2)+'\n');raise SystemExit(r.returncode)
context.update(status='passed');(logs/'result.json').write_text(json.dumps(context,indent=2)+'\n')
