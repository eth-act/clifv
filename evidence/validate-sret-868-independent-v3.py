from pathlib import Path
import datetime,fcntl,hashlib,json,os,re,subprocess
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029';r=b/'.worktrees/stock-extending-production-20261031'
pub=json.loads((e/'sret-full-cfg-publication-v1.json').read_text());pre=json.loads((e/'sret-868-independent-preflight-v1.json').read_text());base=pre['base'];view=pre['view']
lock=(e/'main870-cache-import.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
# The isolated package pins its imports and preserves the source-view head guards.
def git(*args):return subprocess.check_output(['git',*args],cwd=b,text=True).strip()
assert git('-C',str(r),'rev-parse','HEAD')==view
changed=set(git('diff','--name-only',view,base).splitlines());assert not(changed&set(pub['closure']))
assert not(changed&{'lakefile.toml','lakefile.lean','lake-manifest.json','lean-toolchain','scripts/axiom-audit.py'})
root=e/'sret-868-independent-package-v1';assert root.exists()
(root/'lakefile.toml').write_text('name = "sret868gate"\nversion = "0.1.0"\n\n[[lean_lib]]\nname = "FV"\n')
(root/'lean-toolchain').write_bytes(subprocess.check_output(['git','show',base+':lean-toolchain'],cwd=b))
files=dict(pub['source_hashes']);support=[n.replace('.','/')+'.lean' for n in pre['missing']]
for n in list(files)+support:
 data=subprocess.check_output(['git','show',(pub['source'] if n in files else base)+':'+n],cwd=b)
 if n in files:assert hashlib.sha256(data).hexdigest()==files[n]
 else:assert data==(r/n).read_bytes()
 target=root/n;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
modules=[n for n in files if n.startswith('FV/')]+support
ordered=[];pending=set(modules)
while pending:
 ready=sorted(n for n in pending if not({m.replace('.','/')+'.lean' for m in re.findall(r'^import\s+([\w.]+)',(root/n).read_text(),re.M)}&pending))
 assert ready,'Import cycle in the isolated target set'
 ordered.extend(ready);pending.difference_update(ready)
env=dict(os.environ);env.update(json.loads((e/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(r),LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',FV_MEMCAP='3G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2')
normal_path=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=r,env=env,text=True).strip();env['LEAN_PATH']=normal_path
actual_path=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=root,env=env,text=True).strip();lib=root/'.lake/build/lib/lean';assert actual_path.split(os.pathsep)[0]==str(lib),actual_path
logs=e/'sret-868-independent-kernel-v3';assert not logs.exists();logs.mkdir()
(logs/'lean-path.txt').write_text(actual_path+'\n')
# Pin existing import artifacts by hardlink. Only the six targets get new output files.
linked=0
for name in pub['closure']:
 if name in modules or not name.endswith('.lean'):continue
 origin=r/'.lake/build/lib/lean'/Path(name).with_suffix('')
 for artifact in origin.parent.glob(origin.name+'.*'):
  if not artifact.is_file() or not any(artifact.name.endswith(ext) for ext in ['.olean','.ilean','.olean.private','.olean.server']):continue
  target=lib/artifact.relative_to(r/'.lake/build/lib/lean');target.parent.mkdir(parents=True,exist_ok=True)
  if not target.exists():os.link(artifact,target);linked+=1
print('Pinned existing imports without copying cache bytes:',linked,flush=True)
for name in ordered:
 target=lib/Path(name).with_suffix('');target.parent.mkdir(parents=True,exist_ok=True)
 with (logs/(Path(name).stem+'.log')).open('w') as log:
  subprocess.run(['nice','-n','10',str(r/'scripts/memcap.sh'),'lake','env','lean','--root='+str(root),str(root/name),'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c'],cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
 print('KERNEL',name,'passed',flush=True)
with (logs/'audit-summary.log').open('w') as log:
 subprocess.run(['nice','-n','10',str(r/'scripts/memcap.sh'),'python3',str(r/'scripts/axiom-audit.py'),'--cwd',str(root),'--log-dir',str(logs/'audit'),str(root/'scripts/audit/stock-sret-full-values.lean')],cwd=r,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
def axioms(p):
 text=p.read_text();found={n:sorted(x.strip() for x in a.split(',') if x.strip()) for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text,re.S)};found.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",text)});return found
old=axioms(e/'sret-full-cfg-packet-kernel-v2/audit/stock-sret-full-values.log');new=axioms(logs/'audit/stock-sret-full-values.log');assert len(old)==12 and new==old
assert git('-C',str(r),'rev-parse','HEAD')==view and git('-C',str(r),'status','--porcelain')==''
receipt=dict(status='passed',base=base,view=view,source=pub['source'],source_hashes=files,closure_source_differences=[],toolchain_configuration_differences=[],original_axiom_sets_exact=12,generic_roots=10,fixed_roots=2,modules=ordered,isolated_package=str(root),full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(e/'sret-868-independent-validation-v3.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
