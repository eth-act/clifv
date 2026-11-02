from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,shutil
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';Q=E/'direct-call-arithmetic-live-packet-v1';P=E/'direct-call-production-class-packet-v1';R=Q/'validation-package-v1';L=Q/'live-consumer-audit-v2';L.mkdir();C=json.loads((Q/'live-exec-facades-v1/receipt.json').read_text());assert C['status']=='passed'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in C['source_hashes'].items():assert sha(R/n)==h,n
old=sorted((Q/'scripts/audit').glob('stock-live-call-old-*.lean'));new=[Q/f'scripts/audit/stock-live-call-{s}.lean' for s in ['binary-results','executable-results','compiler-results','generated-results','production-complete']]
# The result-call APIs are previous APIs for this additive live-result batch.
extra=[]
for name in ['binary-results','executable-results','compiler-results','generated-results','contract-additions']:
 src=P/f'scripts/audit/stock-result-call-{name}.lean';target=L/src.name;target.write_bytes(src.read_bytes());extra.append(target)
env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(R),FV_MEMCAP='2G',FV_MEMCAP_STATS=str(L/'audit.mem'),FV_MEMCAP_UNIT='worker-o-live-consumer-audit-v1',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false');env['LEAN_PATH']=str(R/'.lake/build/lib/lean')+':/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/lib/lean'
files=[*old,*extra,*new]
# Retain the 17 completed axiom checks. The added facades change no old dependency key.
prior_context=json.loads((Q/'live-production-consumer-kernel-v2/receipt.json').read_text())
assert all(C['dependency_keys'][n]==k for n,k in prior_context['dependency_keys'].items())
prior=Q/'live-consumer-audit-v1';summary=(prior/'summary.log').read_text();(L/'audit').mkdir();reused={};pending=[]
for file in files:
 log=prior/'audit'/(file.stem+'.log');queries=re.findall(r'#print axioms ([\w.]+)',file.read_text())
 success=re.search(r'(?m)^ok\s+'+re.escape(file.name)+r': theorems (\d+)/(\d+) rc=0 errors=0 other_axioms=\[\]',summary)
 if success:
  assert int(success.group(1))==int(success.group(2))==len(queries),(file,success.groups())
  text=' '.join(log.read_text().split());roots=set(re.findall(r"'(.+?)' (?:depends on axioms:|does not depend on any axioms)",text));assert roots==set(queries),(file,roots,queries)
  shutil.copyfile(log,L/'audit'/log.name);reused[file.name]=dict(source_hash=sha(file),log_hash=sha(log),roots=queries,all_old_module_keys_exact=True)
 else:pending.append(file)
assert len(reused)==17 and len(pending)==2
(L/'reused-passed-audits.json').write_text(json.dumps(reused,indent=2)+'\n')
with (L/'summary.log').open('w') as stream:rc=subprocess.call([str(B/'.worktrees/stock-extending-production-20261031/scripts/memcap.sh'),'python3',str(E/'direct-call-delivery-units-v1/axiom-audit-j1.py'),'--cwd',str(R),'--log-dir',str(L/'audit'),*map(str,pending)],cwd=R,env=env,stdout=stream,stderr=subprocess.STDOUT)
print('audit exit',rc,flush=True)
if rc:(L/'failed.json').write_text(json.dumps(dict(status='failed',exit=rc))+'\n');raise SystemExit(rc)
def axes(paths):
 roots={}
 for p in paths:
  text=' '.join(p.read_text().split())
  for n,v in re.findall(r"'(.+?)' depends on axioms: \[([^]]*)\]",text):roots[n]=sorted(x.strip() for x in v.split(',') if x.strip())
  for n in re.findall(r"'(.+?)' does not depend on any axioms",text):roots[n]=[]
 return roots
now=axes((L/'audit').glob('*.log'));baseline=json.loads((P/'final-old-axiom-comparison-v1.json').read_text())['roots'];prior=axes((P/'final-contract-audit-v1/audit').glob('*.log'));wanted=set(baseline)
for f in extra:
 wanted.update(re.findall(r'#print axioms ([\w.]+)',f.read_text()))
expected={n:sorted(baseline[n] if n in baseline else prior[n]) for n in wanted};bad={n:dict(expected=v,actual=now.get(n)) for n,v in expected.items() if now.get(n)!=v};assert not bad,bad
std={'Classical.choice','propext','Quot.sound'};fixed=sum(any(x not in std for x in v) for v in now.values());state=dict(status='passed',old_axiom_sets_exact=len(expected),old_roots=expected,axiom_sets=now,standard_roots=len(now)-fixed,fixed_roots=fixed,audit_hashes={str(p.relative_to(Q)):sha(p) for p in files},stats=(L/'audit.mem').read_text(),source_context=C['source_context'],source_keys=C['dependency_keys'],full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(L/'receipt.json').write_text(json.dumps(state,indent=2)+'\n');print('AX PASSED old',len(expected),'standard',len(now)-fixed,'fixed',fixed,flush=True)
