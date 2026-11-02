"""Record textual moved-declaration parity and historical type/axiom evidence."""
from pathlib import Path
import hashlib, io, json, re, subprocess, tarfile

OUT = Path(__file__).resolve().parent
receipt = json.loads((OUT/'recovery-receipt.json').read_text())
git = lambda *args: subprocess.check_output(['git', *args], cwd='/home/lee/clifv')
# Use the recorded original main baseline before the extraction.
original = git('show', 'ef499aca:FV/Backend/Proof/LowerSim.lean').decode()
current = git('show', receipt['base']+':FV/Backend/Proof/LowerSim.lean').decode()
providers = ''.join((OUT/'source/FV/Backend/Proof'/p).read_text() for p in ['LowerOutcomes.lean','LowerValueRelations.lean'])
records = []
for name in ['VTrapFrom','VRetFrom','VTrapFrom.prefix','VRetFrom.prefix','ArgsAtEntry','Reach','dfgCons_congr','loadVal_congr']:
    pattern = r'(?m)^(?:def|theorem|inductive) '+re.escape(name)+r'\b[\s\S]*?(?=\n\n)'
    found = re.search(pattern, original)
    assert found, name
    block = found.group()
    assert block in current, ('current main changed moved declaration', name)
    assert block in providers, ('candidate changed moved declaration', name)
    records.append({'name':'Backend.Proof.Driver.'+name,'sha256':hashlib.sha256(block.encode()).hexdigest(),'bytes':len(block.encode()),'old_current_candidate_exact':True})
archive = tarfile.open(fileobj=io.BytesIO(git('show','385dc1fc:evidence/outcome-and-mixed-recovery.tar.gz')),mode='r:gz')
evidence = []
for m in archive.getmembers():
    if m.isfile() and (m.name.startswith('stock-outcome-interface-audits/') or m.name.startswith('stock-outcome-value-interface-check/')) and m.name.endswith(('.lean','.log')):
        data = archive.extractfile(m).read()
        dest = OUT/'historical'/m.name
        dest.parent.mkdir(parents=True,exist_ok=True)
        dest.write_bytes(data)
        evidence.append({'path':str(dest.relative_to(OUT)),'sha256':hashlib.sha256(data).hexdigest()})
old = (OUT/'historical/stock-outcome-value-interface-check/old-types.log').read_bytes()
new = (OUT/'historical/stock-outcome-value-interface-check/new-types.log').read_bytes()
assert old == new
result = {'base':receipt['base'],'tree':receipt['candidate_tree'],'moved_declarations':records,'historical_type_and_axiom_outputs_exact':True,'historical_outputs':evidence,'current_kernel_type_axiom_gates':'PENDING; textual identity and old output are not current elaboration evidence'}
(OUT/'moved-declaration-parity.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'moved_declarations_exact':len(records),'historical_type_axiom_outputs_exact':True,'saved_evidence':len(evidence)}))
