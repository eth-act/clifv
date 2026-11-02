from pathlib import Path
import datetime,hashlib,json,os,psutil,re,subprocess,fcntl
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';Q=E/'direct-call-arithmetic-live-packet-v1';R=Q/'validation-package-v1';C=json.loads((Q/'live-production-context-v2/context.json').read_text());L=Q/'live-production-consumer-kernel-v2';L.mkdir();lock=(Q/'live-production-owner.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in C['source_hashes'].items():assert sha(R/n)==h,n
for n,h in C['effective_configs'].items():assert sha(R/n)==h,n
assert C['proofslot_grant']=='live-production-2G'
env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(R),FV_MEMCAP='2G',LAKE_CACHE_DIR=C['native_cache'],LAKE_ARTIFACT_CACHE='true',LAKE_RESTORE_ARTIFACTS='true',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1')
records=[]
def run(label,argv):
 # Read-only --no-build probes cannot compile a provider. Candidate builds reject an identical active provider.
 if '--no-build' not in argv:
  targets={x.replace('.','/')+'.lean' for x in argv if x.startswith(('FV.','FVTest.'))};conflicts=[]
  for p in psutil.process_iter(['pid','name','cmdline','status']):
   try:
    if p.info['name']!='lean' or p.info['status']=='zombie':continue
    for arg in p.info['cmdline'] or []:
     for n in targets:
      if arg.endswith('/'+n) and Path(arg).exists() and sha(Path(arg))==C['source_hashes'][n]:conflicts.append(dict(pid=p.pid,module=n,path=arg))
   except(psutil.NoSuchProcess,psutil.AccessDenied):pass
  assert not conflicts,('identical active normal provider',conflicts)
 env['FV_MEMCAP_STATS']=str(L/(label+'.mem'));env['FV_MEMCAP_UNIT']='worker-o-live-production-'+label
 with (L/(label+'.log')).open('w') as stream:rc=subprocess.call(['nice','-n','10',str(B/'.worktrees/stock-extending-production-20261031/scripts/memcap.sh'),*argv],cwd=R,env=env,stdout=stream,stderr=subprocess.STDOUT)
 records.append(dict(label=label,argv=argv,exit=rc,stats=(L/(label+'.mem')).read_text() if (L/(label+'.mem')).exists() else None,log_sha256=sha(L/(label+'.log'))));(L/'progress.json').write_text(json.dumps(dict(status='running' if rc==0 else 'failed',records=records),indent=2)+'\n');print(label,'exit',rc,flush=True)
 if rc:
  if len(argv)==3 and argv[:2]==['lake','build']:
   n=argv[2].replace('.','/')+'.lean';(L/'failed-source.lean').write_bytes((R/n).read_bytes())
  raise SystemExit(rc)
affected=set(C['affected']);unchanged=[n[:-5].replace('/','.') for n in C['source_hashes'] if n not in affected]
prior=json.loads((Q/'live-production-consumer-kernel-v1/progress.json').read_text());oldcontext=json.loads((Q/'live-production-context-v1/context.json').read_text());oldorder=json.loads((Q/'live-production-consumer-kernel-v1/ordered.json').read_text());completed=oldorder[:66]
assert prior['records'][-1]['exit']!=0 and prior['records'][-1]['label']=='module-66'
for n in completed:assert oldcontext['dependency_keys'][n]==C['dependency_keys'][n],('completed dependency changed',n)
run('preserved-provider-normal-check',['lake','build','--no-build',*unchanged,*[n[:-5].replace('/','.') for n in completed]])
ordered=[];pending=set(affected)
while pending:
 ready=sorted(n for n in pending if not set(C['imports'][n])&pending);assert ready;ordered+=ready;pending.difference_update(ready)
(L/'ordered.json').write_text(json.dumps(ordered,indent=2)+'\n')
for i,n in enumerate(ordered):
 if i>=66:run('module-'+str(i),['lake','build',n[:-5].replace('/','.')])
run('affected-normal-check',['lake','build','--no-build',*[n[:-5].replace('/','.') for n in ordered]])
state=dict(C,status='passed',records=records,ordered=ordered,all_normal_keys=True,full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(L/'receipt.json').write_text(json.dumps(state,indent=2)+'\n');print('STAGED LIVE PRODUCTION KERNEL PASSED',len(ordered),'AFFECTED MODULES',flush=True)
