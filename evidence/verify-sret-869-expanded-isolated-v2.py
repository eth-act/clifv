from pathlib import Path
import datetime,fcntl,hashlib,json,os,re,subprocess
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029';r=b/'.worktrees/stock-extending-production-20261031'
pre=json.loads((e/'sret-869-independent-source-preflight-v1.json').read_text());ready=json.loads((e/'sret-869-expanded-readiness-v1.json').read_text());packet=e/'sret-entry-value-packet-v4';manifest=json.loads((e/'sret-entry-value-packet-v4.json').read_text());view=pre['view'];base=pre['base']
lock=(e/'main870-cache-import.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
def git(*args):return subprocess.check_output(['git',*args],cwd=b,text=True).strip()
assert b'return-pin-call-consumer-recovery-v3' in Path('/proc/3477137/cmdline').read_bytes()
assert git('-C',str(r),'rev-parse','HEAD')==view and git('-C',str(r),'status','--porcelain')==''
root=e/'sret-869-expanded-package-v1'
assert root.exists()
modules=[n for n in manifest['files'] if n.startswith('FV/')]
support_hashes={}
for name in modules:
 data=(packet/name).read_bytes();assert hashlib.sha256(data).hexdigest()==manifest['files'][name]
 target=root/name
 if not target.exists() or target.read_bytes()!=data:target.write_bytes(data)
ordered=['FV/E2E/StockSretPointerPaired.lean','FV/E2E/StockSretPointerWorldWitness.lean','FV/E2E/StockSretPointerPairedWitness.lean']
env=dict(os.environ);env.update(json.loads((e/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(r),LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',FV_MEMCAP='3G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2')
env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=r,env=env,text=True).strip()
lib=root/'.lake/build/lib/lean'
logs=e/'sret-869-expanded-isolated-kernel-v2';assert not logs.exists();logs.mkdir()
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
receipt=dict(status='passed',view=view,dependency_base=base,source_hashes=manifest['files'],support_source_hashes=support_hashes,reused_kernel_logs=str(e/'sret-869-expanded-isolated-kernel-v1'),original_source_files_exact=6,original_axiom_sets_exact=28,generic_roots=30,fixed_roots=4,modules=ordered,isolated_package=str(root),requires_main_dependencies=pre['normal_source_differences'],full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(e/'sret-869-expanded-isolated-state-v2.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ['status','view','original_source_files_exact','original_axiom_sets_exact','generic_roots','fixed_roots','requires_main_dependencies']}),flush=True)
