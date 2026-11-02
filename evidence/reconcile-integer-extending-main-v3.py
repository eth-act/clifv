from pathlib import Path
import subprocess,json,hashlib,datetime,time,psutil
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029';state=e/'integer-extending-main-reconciliation-state-v3.json'
def save(status,**extra):state.write_text(json.dumps(dict(status=status,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),**extra),indent=2)+'\n')
def live(pid):
 try:p=psutil.Process(pid);return p.is_running() and p.status()!=psutil.STATUS_ZOMBIE
 except psutil.NoSuchProcess:return False
def git(*args,cwd=b):return subprocess.check_output(['git',*args],cwd=cwd,text=True).strip()
try:
 while live(3852640):save('waiting',phase='finish-frozen-native-gate',dependency_pid=3852640);time.sleep(3)
 gate=json.loads((e/'integer-extending-production-gates-state-v2.json').read_text())
 assert (e/'integer-extending-main-handoff-v1.json').exists(),'No deliberate handoff receipt'
 assert gate['records'][-1]==dict(label='official',returncode=75),gate
 assert all(x['returncode']==0 for x in gate['records'][:-1])
 assert len([x for x in gate['records'] if x['label'].startswith('consumers-')])==17
 p=json.loads((e/'integer-extending-production-source-v1.json').read_text());r=Path(p['root'])
 published=json.loads((e/'integer-extending-production-published-v1.json').read_text());target=published['commit']
 assert git('rev-parse','HEAD',cwd=r)==p['base']
 for name,digest in p['files'].items():assert hashlib.sha256((r/name).read_bytes()).hexdigest()==digest,name
 modified=set(git('diff','--name-only',cwd=r).splitlines())
 untracked=set(git('ls-files','--others','--exclude-standard',cwd=r).splitlines())
 assert modified|untracked <= set(p['files']),(modified,untracked)
 assert not git('diff','--cached','--name-only',cwd=r),'Unexpected staged changes'
 upstream=set(git('diff','--name-only',p['base'],published['base']).splitlines())
 assert not upstream.intersection(p['files'])
 for name in upstream:
  if git('ls-tree',p['base'],'--',name):
   old=subprocess.check_output(['git','show',p['base']+':'+name],cwd=b)
   assert (r/name).read_bytes()==old,name
  else:
   assert not (r/name).exists(),('Unpublished path would be overwritten',name)
 # These operations retain every candidate byte. Only verified unchanged upstream paths are replaced.
 subprocess.run(['git','reset','--mixed',target],cwd=r,check=True,stdout=subprocess.DEVNULL)
 subprocess.run(['git','restore','--source='+target,'--worktree','--',*sorted(upstream)],cwd=r,check=True)
 assert not git('status','--porcelain',cwd=r),'Combined source is not clean'
 files=set(p['files'])|upstream
 packet=dict(base=target,root=str(r),utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),files={n:hashlib.sha256((r/n).read_bytes()).hexdigest() for n in sorted(files)},combined_main=published['base'],isolated_packet='integer-extending-production-source-v1.json')
 (e/'integer-extending-production-source-v3.json').write_text(json.dumps(packet,indent=2)+'\n')
 save('passed',head=target,main=published['base'],candidate_files_unchanged=len(p['files']),reconciled_paths=len(upstream),isolated_matrices_passed=17,next='Validate combined ABI consumers and official/captured/rejection preservation before landing794. Isolated results remain separate.',full_goal_complete=False)
except BaseException as error:save('failed',error=repr(error));raise
