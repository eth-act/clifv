from pathlib import Path
import datetime,fcntl,hashlib,json,os,re,subprocess
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029';r=b/'.worktrees/stock-extending-production-20261031'
pre=json.loads((e/'sret-869-independent-source-preflight-v1.json').read_text());ready=json.loads((e/'sret-869-expanded-readiness-v1.json').read_text());packet=e/'sret-entry-value-packet-v3';manifest=json.loads((e/'sret-entry-value-packet-v3.json').read_text());view=pre['view'];base=pre['base']
lock=(e/'main870-cache-import.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
def git(*args):return subprocess.check_output(['git',*args],cwd=b,text=True).strip()
assert b'return-pin-call-consumer-recovery-v3' in Path('/proc/3477137/cmdline').read_bytes()
assert git('-C',str(r),'rev-parse','HEAD')==view and git('-C',str(r),'status','--porcelain')==''
root=e/'sret-869-expanded-package-v1';assert not root.exists();root.mkdir()
(root/'lakefile.toml').write_text('name = "sret869gate"\nversion = "0.1.0"\n\n[[lean_lib]]\nname = "FV"\n')
(root/'lean-toolchain').write_bytes((r/'lean-toolchain').read_bytes())
support=pre['main_only_sources']+[m.replace('.','/')+'.lean' for m in ready['support_modules']]
modules=[n for n in manifest['files'] if n.startswith('FV/')]+support
assert len(modules)==len(set(modules));support_hashes={}
for name,digest in manifest['files'].items():
 data=(packet/name).read_bytes();assert hashlib.sha256(data).hexdigest()==digest
 target=root/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
for name in support:
 data=subprocess.check_output(['git','show',(base if name in pre['main_only_sources'] else view)+':'+name],cwd=b)
 support_hashes[name]=hashlib.sha256(data).hexdigest();target=root/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
old=json.loads((e/'sret-entry-value-publication-v1.json').read_text())
for name,digest in old['source_hashes'].items():
 if name.startswith('FV/'):assert manifest['files'][name]==digest,'An original source file changed'
ordered=[];pending=set(modules)
while pending:
 candidates=sorted(n for n in pending if not({m.replace('.','/')+'.lean' for m in re.findall(r'^import\s+([\w.]+)',(root/n).read_text(),re.M)}&pending));assert candidates,'Import cycle';ordered.extend(candidates);pending.difference_update(candidates)
env=dict(os.environ);env.update(json.loads((e/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(r),LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',FV_MEMCAP='3G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2')
env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=r,env=env,text=True).strip()
lib=root/'.lake/build/lib/lean';lib.mkdir(parents=True)
actual=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=root,env=env,text=True).strip();assert actual.split(os.pathsep)[0]==str(lib)
linked=0
for f in (r/'.lake/build/lib/lean/FV').rglob('*'):
 if not f.is_file() or not any(f.name.endswith(ext) for ext in ['.olean','.ilean','.olean.private','.olean.server']):continue
 rel=f.relative_to(r/'.lake/build/lib/lean')
 if any(str(rel).startswith(str(Path(n).with_suffix(''))+'.') for n in modules):continue
 target=lib/rel;target.parent.mkdir(parents=True,exist_ok=True);os.link(f,target);linked+=1
assert git('-C',str(r),'rev-parse','HEAD')==view
logs=e/'sret-869-expanded-isolated-kernel-v1';assert not logs.exists();logs.mkdir();(logs/'lean-path.txt').write_text(actual+'\n')
print('Pinned imports:',linked,'; target modules:',len(ordered),flush=True)
for name in ordered:
 target=lib/Path(name).with_suffix('');target.parent.mkdir(parents=True,exist_ok=True)
 with (logs/(Path(name).stem+'.log')).open('w') as out:
  subprocess.run(['nice','-n','10',str(r/'scripts/memcap.sh'),'lake','env','lean','--root='+str(root),str(root/name),'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c'],cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
 print('KERNEL',name,'passed',flush=True)
with (logs/'audit-summary.log').open('w') as out:
 subprocess.run(['nice','-n','10',str(r/'scripts/memcap.sh'),'python3',str(r/'scripts/axiom-audit.py'),'--cwd',str(root),'--log-dir',str(logs/'audit'),str(root/'scripts/audit/stock-sret-entry-value.lean')],cwd=r,env=env,stdout=out,stderr=subprocess.STDOUT,check=True)
def axioms(p):
 s=p.read_text();d={n:sorted(x.strip() for x in a.split(',') if x.strip()) for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",s,re.S)};d.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",s)});return d
prior=axioms(e/'sret-entry-value-packet-kernel-v1/audit/stock-sret-entry-value.log');now=axioms(logs/'audit/stock-sret-entry-value.log');assert len(prior)==28 and len(now)==34 and all(now[n]==a for n,a in prior.items())
assert git('-C',str(r),'rev-parse','HEAD')==view and git('-C',str(r),'status','--porcelain')==''
receipt=dict(status='passed',view=view,dependency_base=base,source_hashes=manifest['files'],support_source_hashes=support_hashes,original_source_files_exact=6,original_axiom_sets_exact=28,generic_roots=30,fixed_roots=4,modules=ordered,isolated_package=str(root),requires_main_dependencies=pre['normal_source_differences'],full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(e/'sret-869-expanded-isolated-state-v1.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ['status','view','original_source_files_exact','original_axiom_sets_exact','generic_roots','fixed_roots','requires_main_dependencies']}),flush=True)
