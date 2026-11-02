from pathlib import Path
import datetime,hashlib,json,os,psutil,re,subprocess,fcntl,shutil
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';Q=E/'direct-call-arithmetic-live-packet-v1';R=Q/'validation-package-v1';M=json.loads((Q/'standalone-class-source-v1/manifest.json').read_text());C=json.loads((Q/'standalone-current-prepare-v1/receipt.json').read_text());L=Q/'standalone-current-gate-v1';L.mkdir();lock=(Q/'standalone-current-owner.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in M['source_hashes'].items():assert sha(R/n)==h,n
for n,h in C['effective_configs'].items():assert sha(R/n)==h,n
# Native restore may replace outputs. Detach each borrowed product first, so no live inode can change.
detached=0
for p in (R/'.lake/build').rglob('*'):
 if p.is_file() and p.stat().st_nlink>1:
  tmp=p.with_name(p.name+'.isolated-copy');shutil.copyfile(p,tmp);os.replace(tmp,p);detached+=1
(L/'detached-products.json').write_text(json.dumps({'count':detached,'reason':'native cache restoration must not write shared inodes'})+'\n')
env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(R),FV_MEMCAP='2G',LAKE_CACHE_DIR=C['normal_native_cache'],LAKE_ARTIFACT_CACHE='true',LAKE_RESTORE_ARTIFACTS='true',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1')
records=[]
def run(label,argv):
 targets=set(x for x in argv if x.startswith('FV.'))
 conflicts=[]
 for proc in psutil.process_iter(['pid','name','cmdline','status']):
  try:
   a=proc.info['cmdline'] or []
   if proc.info['name']=='lean' and proc.info['status']!='zombie':
    for target in targets:
     if any(target.replace('.','/')+'.lean' in x for x in a):conflicts.append({'pid':proc.pid,'module':target})
  except (psutil.NoSuchProcess,psutil.AccessDenied):pass
 assert not conflicts,('active module owner',conflicts)
 env['FV_MEMCAP_STATS']=str(L/(label+'.mem'));env['FV_MEMCAP_UNIT']='worker-o-live-current-'+label
 with (L/(label+'.log')).open('w') as stream:rc=subprocess.call([str(B/'.worktrees/stock-extending-production-20261031/scripts/memcap.sh'),*argv],cwd=R,env=env,stdout=stream,stderr=subprocess.STDOUT)
 records.append(dict(label=label,argv=argv,exit=rc,stats=(L/(label+'.mem')).read_text() if (L/(label+'.mem')).exists() else None));(L/'progress.json').write_text(json.dumps(dict(status='running' if rc==0 else 'failed',base=M['base'],records=records),indent=2)+'\n');print(label,'exit',rc,flush=True)
 if rc:raise SystemExit(rc)
external=[n[:-5].replace('/','.') for n in M['source_hashes'] if n not in M['owned_sources']]
# This step restores exact native cache entries and forbids compiling any provider.
run('all-provider-normal-check',['lake','build','--no-build',*external])
new=[n[:-5].replace('/','.') for n in M['owned_sources'] if n.startswith('FV/')];pending=set(new);ordered=[]
while pending:
 ready=sorted(n for n in pending if not ({d[:-5].replace('/','.') for d in M['imports'][n.replace('.','/')+'.lean']}&pending));assert ready;ordered+=ready;pending.difference_update(ready)
for i,mod in enumerate(ordered):run('candidate-'+str(i),['lake','build',mod])
run('candidate-normal-check',['lake','build','--no-build',*new])
env['LEAN_PATH']=str(R/'.lake/build/lib/lean')+':/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/lib/lean'
run('audit',['python3',str(E/'direct-call-delivery-units-v1/axiom-audit-j1.py'),'--cwd',str(R),'--log-dir',str(L/'audit'),str(R/'scripts/audit/stock-live-call-class.lean')])
axes={}
for p in (L/'audit').glob('*.log'):
 text=' '.join(p.read_text().split())
 for name,value in re.findall(r"'(.+?)' depends on axioms: \[([^]]*)\]",text):axes[name]=[x.strip() for x in value.split(',') if x.strip()]
 for name in re.findall(r"'(.+?)' does not depend on any axioms",text):axes[name]=[]
std={'propext','Classical.choice','Quot.sound'};fixed=sum(any(x not in std for x in v) for v in axes.values());assert len(axes)==47 and fixed==3,(len(axes),fixed)
for n,h in M['source_hashes'].items():assert sha(R/n)==h,n
state=dict(status='passed',base=M['base'],source_hashes=M['source_hashes'],owned_sources=M['owned_sources'],original_configs=M['configs'],effective_configs=C['effective_configs'],normal_provider_check=True,all_candidates_normal_keys=True,axiom_sets=axes,standard_roots=len(axes)-fixed,fixed_roots=fixed,records=records,full_production_class_complete=False,no_live_package_writes=True,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(L/'receipt.json').write_text(json.dumps(state,indent=2)+'\n');print('CURRENT STANDALONE PASSED',len(axes),'ROOTS',flush=True)
