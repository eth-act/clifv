from pathlib import Path
import os,subprocess,json,datetime,time,re,tomllib,hashlib,shutil
b=Path('/home/lee/clifv');r=b/'.worktrees/stock-memory-delivery-20261030';e=b/'.git/agent-evidence/stock-memory-20261029'
state=e/'production-reverse-gates-state-v5.json';records=[]
def save(status,**extra):state.write_text(json.dumps(dict(status=status,records=records,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),**extra),indent=2)+'\n')
def git(*args):return subprocess.check_output(['git',*args],cwd=r)
env=dict(os.environ);env.update(json.loads((e/'author-env-v1.json').read_text()));env.update(FV_ROOT=str(r),FV_MEMCAP='8G',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LEAN_NUM_THREADS='2',CARGO_BUILD_JOBS='2')
for key in ['FV_PIPELINE_T','BLESS']:env.pop(key,None)
def run(label,args):
 save('running',phase=label)
 with (e/('production-'+label+'-v5.log')).open('w') as log:result=subprocess.run(['nice','-n','10',str(r/'scripts/memcap.sh'),*args],cwd=r,env=env,stdout=log,stderr=subprocess.STDOUT)
 records.append(dict(id=label,returncode=result.returncode))
 if result.returncode:raise RuntimeError(str((label,result.returncode)))
def inputs():
 names=git('ls-files','--cached','--others','--exclude-standard','-z').decode().split('\0')
 return {n:hashlib.sha256((r/n).read_bytes()).hexdigest() for n in names if n and (r/n).is_file()}
try:
 save('running',phase='adopt-landed-main-optimizations')
 subprocess.run(['git','fetch','origin','main'],cwd=r,check=True);main=git('rev-parse','origin/main').decode().strip();head=git('rev-parse','HEAD').decode().strip()
 packet=json.loads((e/'memory-activation-packet.json').read_text());owned=set(packet['files'])
 # Add new main files without replacing any saved source. Existing conflicts stop here.
 for path in git('diff','--name-only',head,main).decode().splitlines():
  if path in owned:continue
  data=git('show',main+':'+path);f=r/path
  if f.exists():
   if f.read_bytes()!=data:
    previous=subprocess.run(['git','show',head+':'+path],cwd=r,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
    assert previous.returncode==0 and f.read_bytes()==previous.stdout,('Unpublished-source conflict',path)
    f.write_bytes(data)
  else:f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(data)
 assert git('branch','--show-current').decode().strip()=='agent/stock-memory-delivery-20261030'
 subprocess.run(['git','merge-base','--is-ancestor',head,main],cwd=r,check=True)
 index=Path(git('rev-parse','--git-path','index').decode().strip());index=index if index.is_absolute() else r/index;shutil.copy2(index,e/'delivery-index-before-main-v5')
 before=inputs();subprocess.run(['git','reset','--mixed',main],cwd=r,stdout=subprocess.PIPE,check=True);assert inputs()==before,'Metadata reconciliation changed saved source'
 deps={}
 for folder in ['FV','FVTest','Corpus']:
  for f in (r/folder).rglob('*.lean'):deps[str(f.relative_to(r))[:-5].replace('/','.')]=set(re.findall(r'^import\s+(\S+)',f.read_text(),re.M))
 affected={p[:-5].replace('/','.') for p in owned if p.endswith('.lean') and not p.startswith('scripts/')}
 while True:
  new=affected|{m for m,imports in deps.items() if imports&affected}
  if new==affected:break
  affected=new
 roots=sorted(affected);config=tomllib.loads((r/'lakefile.toml').read_text());exes=[x['name'] for x in config['lean_exe'] if x.get('root',x['name']) in affected]
 (e/'production-current-main-closure-v5.json').write_text(json.dumps(dict(main=main,roots=roots,executables=exes),indent=2)+'\n');original=inputs();(e/'production-current-source-v5.json').write_text(json.dumps(original,indent=2)+'\n')
 run('reverse-closure',['python3','scripts/lake-serial-build.py','--budget','8G','--max-jobs','1','--max-cap','8G','--default-cap','6G','--out',str(e/'production-reverse-modules-v5'),*roots])
 run('executables',['lake','build',*exes])
 run('memory-audit',['lake','env','lean','scripts/audit/stock-memory-source.lean'])
 def axioms(text):return {n:set(x.strip() for x in a.split(',')) for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text,re.S)}
 old=axioms((e/'author-normal-gates-v1/all-axioms/stock-memory-source.log').read_text());current=axioms((e/'production-memory-audit-v5.log').read_text());assert len(old)==105 and current==old,'Memory axiom sets changed'
 for test in ['test_lowering_trace.py','test_stock_lowering_schedule.py','test_stock_compiler_compare.py','test_stock_pipeline.py','test_stock_exporter.py']:run(test,['python3','-m','unittest','discover','-s','scripts','-p',test,'-v'])
 for kind in ['parameter','conditional-forward','conditional','forward','linear','scalar-entry','entry','cfg']:run('retained-'+kind,[str(r/'.lake/build/bin/stock-memory-retained'),kind])
 run('memory-consumers',['python3','scripts/check-stock-memory-integration.py','--output',str(e/'production-memory-consumers-v5')])
 assert inputs()==original,'Production validation source changed'
 save('passed',main=main,reverse_roots=len(roots),executables=exes,audit_roots=105,axiom_sets_exact=True,official_comparison='Reuse validated delivery-runtime-final-v1:1187/4455, no lost identities')
except BaseException as error:save('failed',error=repr(error));raise
