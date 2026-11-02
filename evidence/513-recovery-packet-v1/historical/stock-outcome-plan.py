from pathlib import Path
import json,subprocess,importlib.util,collections
spec=importlib.util.spec_from_file_location('m','scripts/lake-serial-build.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);_,mods,deps=m.load_modules(Path.cwd());paths=subprocess.check_output(['git','diff','--name-only','ef499aca','HEAD'],text=True).splitlines();seeds={p[:-5].replace('/','.') for p in paths if p.startswith(('FV/','FVTest/')) and p.endswith('.lean')};affected=set(seeds)
while True:
 n=affected|{x for x,ds in deps.items() if set(ds)&affected}
 if n==affected:break
 affected=n
Path('/tmp/stock-outcome-affected.txt').write_text('\n'.join(sorted(affected))+'\n');audit=[]
for p in Path('scripts/audit').glob('*.lean'):
 imports={line.split()[1] for line in p.read_text().splitlines() if line.startswith('import ')}
 if imports&affected:audit.append(str(p))
impact={}
for root in ['FV.Backend.Proof.IselShpTotal','FV.Backend.Proof.DefGenWrap','FV.Backend.Proof.IselPrgTryLast']:
 c={root}
 while True:
  n=c|{d for x in c for d in deps.get(x,[])}
  if n==c:break
  c=n
 assert 'FV.Backend.Proof.LowerSim' not in c,root;impact[root]={'module_imports':len(c),'does_not_import_lower_sim':True}
a={'base':'ef499acae962dbd60cd00e46c43f04c449265944','head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'seeds':sorted(seeds),'affected':sorted(affected),'affected_audits':sorted(audit),'actual_import_boundary':impact};Path('/tmp/stock-outcome-plan.json').write_text(json.dumps(a,indent=2)+'\n');print('Affected',len(affected),'audits',len(audit));print(impact)
