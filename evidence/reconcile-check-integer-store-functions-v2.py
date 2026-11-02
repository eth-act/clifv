from pathlib import Path
import subprocess,json,hashlib,os,time,datetime,psutil,re
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029';r=b/'.worktrees/stock-extending-production-20261031';state=e/'integer-store-functions-pr-gates-v1.json';paused=None;records=[];published=None;head=None

def save(status,**x):state.write_text(json.dumps(dict(status=status,records=records,publication=published,head=head,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),**x),indent=2)+'\n')
def git(*args,env=None):return subprocess.check_output(['git',*args],cwd=r,env=env,text=True).strip()
def live(p):
 try:return p.is_running() and p.status()!=psutil.STATUS_ZOMBIE
 except psutil.NoSuchProcess:return False
try:
 while True:
  landing=json.loads((e/'integer-store-records-landing-v1.json').read_text())
  if landing['status']=='passed':break
  assert landing['status']!='failed',landing
  save('waiting',phase='parent797-landing');time.sleep(10)
 published=json.loads((e/'integer-store-functions-publication-v1.json').read_text());assert published['status']=='passed'
 assert git('rev-parse','HEAD')==landing['commit'] and not git('status','--porcelain')
 subprocess.run(['git','fetch','origin','main'],cwd=r,check=True);main=git('rev-parse','origin/main')
 assert main==landing['merge'],'Inspect newer main drift before reconciling the packet'
 assert git('rev-parse',main+'^{tree}')==git('rev-parse',published['base']+'^{tree}')
 old=published['commit'];branch=published['branch'];assert git('rev-parse',branch)==old
 assert git('ls-remote','origin','refs/heads/'+branch).split()[0]==old
 # A normal merge commit preserves the published source history and needs no force push.
 head=git('commit-tree',git('rev-parse',old+'^{tree}'),'-p',old,'-p',main,'-m','Reconcile complete store functions onto current main')
 git('update-ref','refs/heads/'+branch,head,old);subprocess.run(['git','push','origin',branch],cwd=r,check=True)
 assert git('ls-remote','origin','refs/heads/'+branch).split()[0]==head
 subprocess.run(['gh','pr','edit',str(published['pr']),'--repo','eth-act/clifv','--base','main'],cwd=r,check=True)
 subprocess.run(['git','switch',branch],cwd=r,check=True)
 hashes=published['source_hashes']
 def frozen():
  assert git('rev-parse','HEAD')==head and not git('status','--porcelain')
  assert all(hashlib.sha256((r/n).read_bytes()).hexdigest()==h for n,h in hashes.items())
 frozen();save('running',phase='source-reconciled',base=main,branch=branch,remote_verified=True)
 normal=psutil.Process(3167178);schedulers=[]
 for c in normal.children(recursive=True):
  try:
   if c.name().startswith('python') and any(a=='scripts/lake-serial-build.py' or a.endswith('/lake-serial-build.py') for a in c.cmdline()):schedulers.append(c)
  except psutil.NoSuchProcess:pass
 assert len(schedulers)==1,'Inspect the old normal/runtime phase before reserving resources'
 paused=schedulers[0];paused.suspend()
 while any(live(c) for c in paused.children()):save('waiting',phase='finish-old-active-source',base=main);time.sleep(3)
 env=dict(os.environ);env.update(json.loads((e/'author-env-v1.json').read_text()));env.update(FV_ROOT=str(r),OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LEAN_NUM_THREADS='2',CARGO_BUILD_JOBS='2',PYTHONDONTWRITEBYTECODE='1')
 for k in ['FV_PIPELINE_T','BLESS']:env.pop(k,None)
 def run(label,args,cap='16G'):
  frozen();save('running',phase=label,base=main);env['FV_MEMCAP']=cap;env['FV_MEMCAP_STATS']=str(e/('integer-store-functions-pr-'+label+'-v1.stats'))
  with (e/('integer-store-functions-pr-'+label+'-v1.log')).open('w') as out:done=subprocess.run(['nice','-n','10',str(r/'scripts/memcap.sh'),*args],cwd=r,env=env,stdout=out,stderr=subprocess.STDOUT)
  records.append(dict(label=label,returncode=done.returncode));assert done.returncode==0,(label,done.returncode)
 run('FV-FVTest',['python3','scripts/lake-serial-build.py','--budget','16G','--max-jobs','2','--max-cap','16G','--default-cap','4G','--profile',str(r/'scripts/lake-module-peaks.tsv'),'--profile',str(r/'.lake/lake-module-peaks.tsv'),'--out',str(e/'integer-store-functions-full-modules-v1'),'FV','FVTest'])
 # Both consumers retain their exact source/import closure in this proof-only packet.
 run('e2e-link-tools',['lake','build','lean-e2e-check','link-check'])
 run('lean-e2e-check',[str(r/'.lake/build/bin/lean-e2e-check')])
 linkRoot=e/'integer-extending-production-consumers-i32-v3'
 prior=json.loads((linkRoot/'receipt.json').read_text());assert prior['state']=='passed'
 bundle=linkRoot/'generated/StockMemoryProductionPlainFallbackGlobal-bundle'
 for name,digest in prior['artifacts'].items():
  path=linkRoot/name
  if path.suffix in ['.clif','.json','.elf']:assert hashlib.sha256(path.read_bytes()).hexdigest()==digest
 run('link-check',[str(r/'.lake/build/bin/link-check'),str(bundle),'--no-dead-cleanup'])
 run('audit',['lake','env','lean','-j1','scripts/audit/stock-memory-store-functions.lean'],'4G')
 def axioms(p):
  t=p.read_text();a={n:set(x.strip() for x in s.split(',')) for n,s in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",t,re.S)};a.update({n:set() for n in re.findall(r"'([^']+)' does not depend on any axioms",t)});return a
 now=axioms(e/'integer-store-functions-pr-audit-v1.log');oldA=axioms(e/'integer-store-records-pr-audit-v1.log')
 assert len(now)==44 and all(a<={'propext','Classical.choice','Quot.sound'} for a in now.values())
 assert len(oldA)==29 and all(now[n]==a for n,a in oldA.items())
 frozen();save('passed',base=main,branch=branch,audit_roots=44,prior_axiom_sets_exact=29,all_axioms_standard=True,source_hashes=hashes,scope='Complete per-PR FV/FVTest, E2E/link checks and44-root audit. No production consumer changed.')
except BaseException as error:save('failed',error=repr(error));raise
finally:
 if paused is not None and live(paused):paused.resume()
