from pathlib import Path
import os,subprocess,json,datetime,time,hashlib,re,tomllib,psutil
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029';r=b/'.worktrees/stock-extending-production-20261031';state=e/'integer-store-load-store-main-reconciliation-state-v1.json';records=[]
env=dict(os.environ);env.update(json.loads((e/'author-env-v1.json').read_text()));env.update(FV_ROOT=str(r),FV_MEMCAP='16G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',CARGO_BUILD_JOBS='2',PYTHONDONTWRITEBYTECODE='1')
for k in ['FV_PIPELINE_T','BLESS']:env.pop(k,None)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def cmd(*a):return subprocess.check_output(a,cwd=r,text=True).strip()
def save(status,**x):state.write_text(json.dumps(dict(status=status,records=records,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),**x),indent=2)+'\n')
def wait(name,pid,label):
 while True:
  x=json.loads((e/name).read_text());assert x['status']!='failed',x
  if x['status']=='passed':return x
  proc=psutil.Process(pid);assert proc.is_running() and proc.status()!=psutil.STATUS_ZOMBIE and label in ' '.join(proc.cmdline());time.sleep(10)
def axiom_sets(directory):
 out={}
 for p in directory.glob('*.log'):
  for name,axioms in re.findall(r"'(\S+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",' '.join(p.read_text().split())):
   used=sorted(x.strip() for x in axioms.split(',') if x.strip());assert name not in out or out[name]==used,(name,p);out[name]=used
 return out
try:
 save('waiting',phase='preserve-complete-original-gates-before-main-reconciliation')
 full=wait('integer-store-load-store-full-state-v1.json',3015749,'integer-store-load-store-full-v1')
 preserve=wait('integer-store-load-store-preservation-state-v1.json',3025882,'integer-store-load-store-preservation-v1')
 hashes=dict(full['source_hashes']);hashes['scripts/test_stock_configured_provider.py']=preserve['configured_test_sha256']
 assert all(sha(r/n)==h for n,h in hashes.items())
 assert cmd('git','rev-parse','HEAD')==full['head']
 assert cmd('git','branch','--show-current')=='agent/stock-load-store-production-20261031'
 assert not cmd('git','diff','--cached','--name-only')
 subprocess.run(['git','fetch','origin','main'],cwd=r,check=True)
 expected='00d6d8f693ba948fb0f057c64c9ca6389359386c';assert cmd('git','rev-parse','origin/main')==expected,'Inspect further main drift before this reconciliation'
 changed=set(cmd('git','diff','--name-only','HEAD..origin/main').splitlines());allowed={'FV/Opt/Proof/RuleArith5.lean','FV/Opt/Proof/RuleInfraShiftAmt.lean','LEARNINGS.md','docs/TO-PROVE.md','scripts/ci-build-plan.py','scripts/lake-module-peaks.tsv','scripts/lake-serial-build.py'}
 assert changed==allowed and not changed&set(hashes),(changed,set(hashes))
 tools=[x['gate'][6:] for x in full['records'] if x['gate'].startswith('build-')]
 roots={x['name']:x['root'] for x in tomllib.loads((r/'lakefile.toml').read_text())['lean_exe']}
 cone=set(json.loads((e/'integer-store-load-store-main-drift-triage-v1.json').read_text())['static_importer_cone'])
 assert all(roots[n] not in cone for n in tools)
 binaries={n:sha(r/'.lake/build/bin'/n) for n in tools}
 save('running',phase='adopt-reviewed-814-816',old_head=full['head'],new_head=expected,source_hashes=hashes,binary_hashes_before=binaries)
 subprocess.run(['git','merge','--ff-only','origin/main'],cwd=r,check=True)
 assert all(sha(r/n)==h for n,h in hashes.items())
 def frozen():
  assert cmd('git','rev-parse','HEAD')==expected and all(sha(r/n)==h for n,h in hashes.items())
 def run(label,args):
  frozen();save('running',phase=label,old_head=full['head'],new_head=expected,source_hashes=hashes,binary_hashes_before=binaries)
  with (e/('integer-store-load-store-reconcile-'+label+'-v1.log')).open('w') as log:
   p=subprocess.run(['nice','-n','10',str(r/'scripts/memcap.sh'),*map(str,args)],cwd=r,env=env,stdout=log,stderr=subprocess.STDOUT)
  records.append(dict(gate=label,returncode=p.returncode));assert p.returncode==0,(label,p.returncode)
 run('modules',['python3','scripts/lake-serial-build.py','--budget','16G','--max-jobs','2','--max-cap','16G','--default-cap','4G','--profile',r/'scripts/lake-module-peaks.tsv','--profile',e/'production-cold-overrides-v6.tsv','--out',e/'integer-store-load-store-reconcile-modules-v1','FV','FVTest'])
 run('audit',['python3','scripts/axiom-audit.py','--log-dir',e/'integer-store-load-store-reconcile-audit-v1'])
 old=axiom_sets(e/'integer-store-load-store-full-audit-v1');now=axiom_sets(e/'integer-store-load-store-reconcile-audit-v1');assert len(old)>=4756 and all(now.get(n)==v for n,v in old.items()),[(n,v,now.get(n)) for n,v in old.items() if now.get(n)!=v]
 audit=e/'integer-store-load-store-main-new-lemmas-v1.lean';audit.write_text("import FV.Opt.Proof.RuleInfraShiftAmt\n#print axioms Opt.Proof.ShiftAmt.shl_xor_shl_of\n#print axioms Opt.Proof.ShiftAmt.ushr_xor_ushr_of\n#print axioms Opt.Proof.ShiftAmt.sshr_xor_sshr_of\n")
 run('new-main-lemmas',['python3','scripts/axiom-audit.py','--log-dir',e/'integer-store-load-store-reconcile-new-lemmas-v1',audit])
 for tool in tools:run('build-'+tool,['lake','build',tool])
 after={n:sha(r/'.lake/build/bin'/n) for n in tools};assert binaries==after,'Changed executable: inspect and repeat its affected production stages'
 assert all(sha(r/n)==h for n,h in hashes.items());subprocess.run(['git','diff','--check'],cwd=r,check=True)
 save('passed',old_head=full['head'],new_head=expected,source_hashes=hashes,binary_hashes_before=binaries,binary_hashes_after=after,all26_executables_exact=True,all_saved_sources_exact=True,prior_axiom_roots=len(old),all_prior_axiom_sets_exact=True,reused_full_gate='integer-store-load-store-full-state-v1.json',reused_preservation_gate='integer-store-load-store-preservation-state-v1.json',scope='Main814/816 change only proof automation,scheduling and docs. Full current proof/policy gates pass. Every production executable remains byte-identical;all completed runtime,matrix,configured,capture,settings and identity gates remain applicable. Exact-current-head official CI and publication remain mandatory. Full140 is incomplete.')
except BaseException as error:save('failed',error=repr(error));raise
