"""Review retained standalone diagnostics and exact historical axiom policy. No Lean call."""
from pathlib import Path
import hashlib, json, re

OUT=Path(__file__).resolve().parent
state=json.loads((OUT/'state-v2.json').read_text())
assert state['status']=='passed', 'Inspect the first failed command; do not retry or clean passed outputs automatically'
logs=OUT/'kernel-v2'
baseline=next(logs.glob('baseline-*-Types.log')).read_bytes()
candidate=next(logs.glob('candidate-*-Types.log')).read_bytes()
assert baseline==candidate
sets={}
for name,axes in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",baseline.decode(),re.S):
    sets[name]=sorted(x.strip() for x in axes.split(',') if x.strip())
for name in re.findall(r"'([^']+)' does not depend on any axioms",baseline.decode()):sets[name]=[]
expected={
 'VTrapFrom':['propext'], 'VRetFrom':['propext'],
 'VTrapFrom.prefix':['propext'], 'VRetFrom.prefix':['propext'],
 'ArgsAtEntry':['Quot.sound','propext'], 'Reach':[],
 'dfgCons_congr':['Quot.sound','propext'], 'loadVal_congr':['Quot.sound','propext'],
}
assert len(sets)==8
for name,axes in expected.items():
    raw=sets['Backend.Proof.Driver.'+name]
    normalized=sorted(re.sub(r'\.\{[^}]*\}','',a) for a in raw)
    assert normalized==sorted(axes),('Historical required axiom set changed',name,raw,axes)
peaks=[]
for item in state['command_records']:
    assert item['exit']==0
    match=re.search(r'(?m)^peak (\d+)$',item['memstats'])
    assert match,('Missing command memory evidence',item['source'])
    peaks.append((int(match[1]),item['stage'],item['source']))
peak=max(peaks)
result={'status':'reviewed_passed','base':state['base'],'candidate_tree':state['candidate_tree'],'standalone_without892':True,'fresh_baseline_project_kernels':state['fresh_baseline_project_kernels'],'candidate_kernels':7,'exact_elaborated_types':8,'exact_raw_axiom_outputs':sets,'historical_required_sets_exact':True,'peak_bytes':peak[0],'peak_stage':peak[1],'peak_module':peak[2],'limit':'3G (first119commands used2G)','no_frozen_project_artifacts':True,'no_interface_bridge':True,'full_affected_gates_passed':False,'kernel_receipt_sha256':hashlib.sha256((OUT/'state-v2.json').read_bytes()).hexdigest()}
(OUT/'reviewed-state-v2.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','base','candidate_tree','fresh_baseline_project_kernels','candidate_kernels','exact_elaborated_types','peak_bytes','peak_module','full_affected_gates_passed']}))
