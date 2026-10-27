from pathlib import Path
import re,json

def roots(directory):
 result={}
 for p in Path(directory).glob('*.log'):
  s=p.read_text()
  for n,axes in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",s):
   value=sorted(x.strip() for x in axes.split(',') if x.strip())
   assert n not in result or result[n]==value,(n,p)
   result[n]=value
  for n in re.findall(r"'([^']+)' does not depend on any axioms",s):result[n]=[]
 return result
old=roots('/tmp/stock-memory-paired-normal-gates-v1/all-axioms');new=roots('/tmp/stock-memory-reconciled-normal-gates-v1/all-axioms')
assert len(old)==3839,len(old)
missing=sorted(set(old)-set(new));changed={n:[v,new[n]] for n,v in old.items() if n in new and v!=new[n]};assert not missing and not changed,(missing,changed)
prior=roots('/tmp/stock-memory-paired-return-normal-gates-v1/all-axioms');assert len(prior)==84;assert all(new.get(n)==v for n,v in prior.items())
memory=roots('/tmp/stock-memory-reconciled-normal-gates-v1/all-axioms')
focused=Path('/tmp/stock-memory-reconciled-normal-gates-v1/all-axioms/stock-memory-source.log').read_text();names=re.findall(r"'([^']+)' (?:depends on axioms|does not depend)",focused)
std={'propext','Classical.choice','Quot.sound'};native={n:new[n] for n in names if not set(new[n])<=std}
assert set(native)=={'E2E.StockMemoryEffectKernel.source_checked','E2E.StockMemoryActivationWitness.default_memory_route_witness'},native
headers=json.loads(Path('/tmp/stock-memory-reconciled-header-parity-v1.json').read_text());assert headers['all_modified_old_public_headers_exact']
old_per_file=0;new_per_file=0
for path in Path('/tmp/stock-memory-paired-normal-gates-v1/all-axioms').glob('*.log'):
 def one(path):
  text=path.read_text();r={n:sorted(x.strip() for x in axes.split(',') if x.strip()) for n,axes in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text)}
  r.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",text)});return r
 a=one(path);b=one(Path('/tmp/stock-memory-reconciled-normal-gates-v1/all-axioms')/path.name)
 assert all(b.get(n)==v for n,v in a.items()),path.name
 old_per_file+=len(a);new_per_file+=len(b)
assert old_per_file==3994 and new_per_file>=4025,(old_per_file,new_per_file)
r=dict(state='passed',old_per_file_axiom_sets=3994,current_per_file_axiom_sets=new_per_file,old_roots=len(old),current_roots=len(new),all_old_axiom_sets_exact=True,all84_prior_memory_roots_exact=True,current_memory_roots=len(names),standard_only_memory_roots=len(names)-len(native),fixed_native_witness_roots=native,old_public_headers_exact=len(headers['headers']),axiom_sets=new)
Path('/tmp/stock-memory-reconciled-contract-parity-v1.json').write_text(json.dumps(r,indent=2)+'\n');print('EXACT_OLD_AX_HEADER_PARITY_PASS',len(old),len(new),len(names),len(headers['headers']))
