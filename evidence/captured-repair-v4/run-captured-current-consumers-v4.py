from pathlib import Path
import os,json,subprocess,datetime,time,re,hashlib,psutil,tomllib
b=Path('/home/lee/clifv');r=b/'.worktrees/stock-cfg-source-20261025';e=b/'.git/agent-evidence/stock-memory-20261029';env=dict(os.environ);env.update(json.loads((e/'author-env-v1.json').read_text()));env.update(FV_ROOT=str(r),FV_MEMCAP='8G',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LEAN_NUM_THREADS='2',CARGO_BUILD_JOBS='2');env.pop('FV_PIPELINE_T',None);state=e/'captured-current-consumers-state-v4.json';records=[]
def save(status,**x):state.write_text(json.dumps(dict(status=status,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),records=records,**x),indent=2)+'\n')
def git(*args):return subprocess.check_output(['git',*args],cwd=r).decode().strip()
def run(label,args):
 save('running',phase=label)
 with (e/('captured-current-consumers-'+label+'-v4.log')).open('w') as log:result=subprocess.run(['nice','-n','10',str(r/'scripts/memcap.sh'),*args],cwd=r,env=env,stdout=log,stderr=subprocess.STDOUT)
 records.append(dict(label=label,returncode=result.returncode))
 if result.returncode:raise RuntimeError((label,result.returncode))
def fingerprint():
 names=git('ls-files','--cached','--others','--exclude-standard','-z').split('\0')
 return {n:hashlib.sha256((r/n).read_bytes()).hexdigest() for n in names if n and (r/n).is_file()}
try:
 assert json.loads((e/'captured-repair-state-v4.json').read_text())['status']=='passed'
 assert json.loads((e/'captured-current-proof-receipt-v4.json').read_text())['status']=='passed'
 deps={}
 for folder in ['FV','FVTest','Corpus']:
  for f in (r/folder).rglob('*.lean'):deps[str(f.relative_to(r))[:-5].replace('/','.')]=set(re.findall(r'^import\s+(\S+)',f.read_text(),re.M))
 changed=git('diff','--name-only','b6cdec54').splitlines();affected={n[:-5].replace('/','.') for n in changed if n.endswith('.lean') and not n.startswith('scripts/')}
 while True:
  more=affected|{m for m,imports in deps.items() if imports&affected}
  if more==affected:break
  affected=more
 config=tomllib.loads((r/'lakefile.toml').read_text());exes=[x['name'] for x in config['lean_exe'] if x.get('root',x['name']) in affected]
 (e/'captured-current-consumer-closure-v4.json').write_text(json.dumps(dict(base='b6cdec54',roots=sorted(affected),executables=exes),indent=2)+'\n')
 before=fingerprint();(e/'captured-current-consumer-source-v4.json').write_text(json.dumps(before,indent=2)+'\n')
 run('reverse-build',['python3','scripts/lake-serial-build.py','--budget','8G','--max-jobs','1','--max-cap','8G','--default-cap','8G','--out',str(e/'captured-current-consumer-modules-v4'),*sorted(affected)])
 for exe in exes:run('build-'+exe,['lake','build',exe])
 run('old-memory-audit',['lake','env','lean','scripts/audit/stock-memory-source.lean'])
 def axioms(text):return {n:set(x.strip() for x in a.split(',')) for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text,re.S)}
 assert axioms((e/'captured-current-consumers-old-memory-audit-v4.log').read_text())==axioms((e/'author-normal-gates-v1/all-axioms/stock-memory-source.log').read_text())
 run('trace-regression',['python3','-m','unittest','discover','-s','scripts','-p','test_lowering_trace.py','-v'])
 for cfg in [False,True]:run('integration-'+('cfg' if cfg else 'singleton'),['python3','scripts/check-stock-memory-integration.py','--output',str(e/('captured-current-integration-'+('cfg' if cfg else 'singleton')+'-v4')),*(['--memory-cfg'] if cfg else [])])
 assert before==fingerprint(),'Source changed during current consumer validation'
 save('passed',reverse_roots=len(affected),executables=exes,old_axioms_exact=True)
except BaseException as error:save('failed',error=repr(error));raise
