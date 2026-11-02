from pathlib import Path
import datetime,fcntl,hashlib,json,os,re,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031';source='a4c0726d46c5908b4ac06cf797ee939af8644703'
lock=(E/'main870-cache-import.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=V,text=True).strip()==source
packet=E/'void-call-file-packet-v1';manifest=json.loads((E/'void-call-file-packet-v1.json').read_text());root=E/'865-independent-package-v1';assert not root.exists();root.mkdir();(root/'lakefile.toml').write_text('name = "voidcallfilegate"\nversion = "0.1.0"\n\n[[lean_lib]]\nname = "FV"\n');(root/'lean-toolchain').write_bytes((V/'lean-toolchain').read_bytes())
modules={n for n in manifest['files'] if n.startswith('FV/')}
for name,digest in manifest['files'].items():
 data=(packet/name).read_bytes();assert hashlib.sha256(data).hexdigest()==digest;p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
ordered=[];pending=set(modules)
while pending:
 ready=sorted(n for n in pending if not {m.replace('.','/')+'.lean' for m in re.findall(r'^import\s+([\w.]+)',(root/n).read_text(),re.M)}&pending);assert ready;ordered+=ready;pending.difference_update(ready)
lib=root/'.lake/build/lib/lean';lib.mkdir(parents=True)
for f in (V/'.lake/build/lib/lean/FV').rglob('*'):
 if not f.is_file() or not any(f.name.endswith(s) for s in ['.olean','.ilean','.olean.private','.olean.server']):continue
 rel=f.relative_to(V/'.lake/build/lib/lean')
 if any(str(rel).startswith(str(Path(n).with_suffix(''))+'.') for n in modules):continue
 p=lib/rel;p.parent.mkdir(parents=True,exist_ok=True);os.link(f,p)
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(V),FV_MEMCAP='3G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false');env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,env=env,text=True).strip();logs=E/'865-independent-isolated-kernel-v1';assert not logs.exists();logs.mkdir()
for name in ordered:
 target=lib/Path(name).with_suffix('');target.parent.mkdir(parents=True,exist_ok=True)
 with (logs/(Path(name).stem+'.log')).open('w') as out:subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'lake','env','lean','--root='+str(root),str(root/name),'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c'],cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
 print('KERNEL',name,'passed',flush=True)
with (logs/'audit-summary.log').open('w') as out:subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'python3',str(V/'scripts/axiom-audit.py'),'--cwd',str(root),'--log-dir',str(logs/'audit'),str(root/'scripts/audit/void-call-file-production.lean')],cwd=V,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=V,text=True).strip()==source
receipt=dict(status='passed',validated_source=source,source_hashes=manifest['files'],modules=ordered,generic_roots=11,fixed_roots=8,isolated_package=str(root),requires_current_main_import_source_equality=True,full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(E/'865-independent-isolated-state-v1.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(dict(status='passed',modules=len(ordered),generic_roots=11,fixed_roots=8)),flush=True)
