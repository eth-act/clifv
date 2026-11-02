from pathlib import Path
import datetime,hashlib,json,re
Q=Path(__file__).resolve().parent;P=Q.parent/'direct-call-production-class-packet-v1';L=Q/'live-consumer-audit-v2';C=json.loads((Q/'live-exec-facades-v1/receipt.json').read_text());D=Q/'live-consumer-audit-final-v1';D.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def axes(paths):
 roots={}
 for p in paths:
  text=' '.join(p.read_text().split())
  # A name cannot contain an apostrophe. Do not consume a preceding no-axioms record.
  for n,v in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text):roots[n]=sorted(x.strip() for x in v.split(',') if x.strip())
  for n in re.findall(r"'([^']+)' does not depend on any axioms",text):roots[n]=[]
 return roots
old=sorted((Q/'scripts/audit').glob('stock-live-call-old-*.lean'));new=[Q/f'scripts/audit/stock-live-call-{s}.lean' for s in ['binary-results','executable-results','compiler-results','generated-results','production-complete']];extra=sorted(L.glob('stock-result-call-*.lean'));files=[*old,*new,*extra]
summary=(L/'summary.log').read_text();assert 'axiom audit: 2/2 files ok' in summary,summary
reused=json.loads((L/'reused-passed-audits.json').read_text());assert len(reused)==17
now=axes((L/'audit').glob('*.log'));query_roots={n for f in files for n in re.findall(r'#print axioms ([\w.]+)',f.read_text())};assert set(now)==query_roots,(set(now)-query_roots,query_roots-set(now))
baseline=json.loads((P/'final-old-axiom-comparison-v1.json').read_text())['roots'];prior=axes((P/'final-contract-audit-v1/audit').glob('*.log'));wanted=set(baseline)
for file in extra:wanted.update(re.findall(r'#print axioms ([\w.]+)',file.read_text()))
expected={n:sorted(baseline[n] if n in baseline else prior[n]) for n in wanted};bad={n:dict(expected=v,actual=now.get(n)) for n,v in expected.items() if now.get(n)!=v};assert not bad,bad
std={'Classical.choice','propext','Quot.sound'};fixed=sum(any(x not in std for x in v) for v in now.values());state=dict(status='passed',old_axiom_sets_exact=len(expected),old_roots=expected,axiom_sets=now,standard_roots=len(now)-fixed,fixed_roots=fixed,audit_hashes={str(p.relative_to(Q)):sha(p) for p in files},queried_logs={str(p.relative_to(Q)):sha(p) for p in (L/'audit').glob('*.log')},reused_completed_audits=17,repaired_missing_facade_audits=2,aggregation_fix='Stop theorem-name regex at closing apostrophe. All19 actual proof checks already passed.',stats=(L/'audit.mem').read_text(),source_context=C['source_context'],source_keys=C['dependency_keys'],full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(D/'receipt.json').write_text(json.dumps(state,indent=2)+'\n');print('AX PASSED old',len(expected),'standard',len(now)-fixed,'fixed',fixed,flush=True)
