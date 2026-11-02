from pathlib import Path
import os,json,subprocess,hashlib,datetime,re
b=Path('/home/lee/clifv');r=b/'.worktrees/stock-extending-production-20261031';e=b/'.git/agent-evidence/stock-memory-20261029'
g=json.loads((e/'call-return-pins-reviewed-gate-v1.json').read_text());g['head']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()
assert all(hashlib.sha256((r/n).read_bytes()).hexdigest()==h for n,h in g['source_hashes'].items())
env=dict(os.environ);env.update(json.loads((e/'author-env-v1.json').read_text()));env.update(FV_MEMCAP='12G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2')
state=e/'call-return-pins-publication-gate-v1.json'
def save(status,**kw):state.write_text(json.dumps(dict(g,status=status,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),**kw),indent=2)+'\n')
def run(label,args):
 save('running',phase=label)
 with (e/('call-return-pins-reconcile-'+label+'-v2.log')).open('w') as out:p=subprocess.run(['nice','-n','10',str(r/'scripts/memcap.sh'),*map(str,args)],cwd=r,env=env,stdout=out,stderr=subprocess.STDOUT)
 assert p.returncode==0,(label,p.returncode)
def axioms(path):
 result={}
 for p in path.glob('*.log'):
  for name,used in re.findall(r"'(\S+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",' '.join(p.read_text().split())):result[name]=sorted(v.strip() for v in used.split(',') if v.strip())
 return result
try:
 run('kernel',['python3','scripts/lake-serial-build.py','--budget','12G','--max-jobs','1','--max-cap','12G','--default-cap','6G','--profile','scripts/lake-module-peaks.tsv','--out',e/'call-return-pins-reconcile-modules-v2','FV.E2E.StockTrapWitness','FV.Backend.Proof.StockConditionalTrapLeafWitness'])
 run('audit',['python3','scripts/axiom-audit.py','--log-dir',e/'call-return-pins-reconcile-audit-v2'])
 old=axioms(e/'sret-abi-consumer-full-audit-v1');now=axioms(e/'call-return-pins-reconcile-audit-v2');assert len(old)==4937
 assert all(now.get(n)==v for n,v in old.items()),[(n,v,now.get(n)) for n,v in old.items() if now.get(n)!=v]
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()==g['head']
 assert all(hashlib.sha256((r/n).read_bytes()).hexdigest()==h for n,h in g['source_hashes'].items())
 save('passed',all_prior_axiom_sets_exact=True,reviewed_proof_gate_passed=True,prior_axiom_roots=len(old),scope='Reconciled through838. The earlier current linker kernel check passed. The missing trap witness and838 dependency builds now pass. Fresh full repository policy passes. All4937 prior axiom sets remain exact. Retain completed proof/tool/focused checks and one approved direct peer review. Broad remaining production matrices were intentionally cancelled. Default ABI activation and full140 remain open.')
 print('Current kernel dependencies and repository policy passed.')
except BaseException as error:save('failed',error=repr(error));raise
