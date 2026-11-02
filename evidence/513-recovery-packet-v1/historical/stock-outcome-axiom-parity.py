from pathlib import Path
import json,re,subprocess
plan=json.load(open('/tmp/stock-outcome-plan.json'));newdir=Path('/tmp/stock-outcome-audits');old1=Path('/tmp/stock-highmul-reconciled-audits');old2=Path('/tmp/stock-div-current-affected-audits')
def roots(paths):
 result={}
 for p in paths:
  text=' '.join(p.read_text().split())
  for name,axes in re.findall(r"'(.+?)' depends on axioms: \[([^]]*)\]",text):result[name]=sorted(set(x.strip() for x in axes.split(',') if x.strip()))
  for name in re.findall(r"'(.+?)' does not depend on any axioms",text):result[name]=[]
 return result
required={}; all_old={}
for old in [old1,old2]:
 all_old.update(roots(sorted(old.glob('*.log'))))
 required.update(roots([old/(Path(p).stem+'.log') for p in plan['affected_audits'] if (old/(Path(p).stem+'.log')).exists()]))
current=roots(sorted(newdir.glob('*.log')));missing=sorted(set(required)-set(current));changed=[n for n in required if n in current and required[n]!=current[n]]
r={'head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'base':plan['base'],'historical_sources':['highmul reconciled audits (actual original recorded heads)','division current affected audits b1ef0c67 (exact implementation reconciled to512)'],'current_roots':len(current),'prior_roots_required':len(required),'missing':missing,'changed':changed,'unrerun_unaffected_historical_roots':len(set(all_old)-set(required)),'exact_required_axiom_sets_preserved':not missing and not changed};Path('/tmp/stock-outcome-axiom-parity.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r));assert not missing and not changed
