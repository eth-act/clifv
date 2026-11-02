"""Compare complete source-bound baseline and combined audit receipts."""
from pathlib import Path
import argparse, hashlib, json, subprocess

p=argparse.ArgumentParser()
p.add_argument('--baseline',type=Path,required=True)
p.add_argument('--combined',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
a=p.parse_args()
assert not a.out.exists(), 'Preserve previous evidence'
plan=json.loads((Path(__file__).resolve().parent/'snapshot-plan.json').read_text())
old_receipt=json.loads((a.baseline/'receipt.json').read_text())
new_receipt=json.loads((a.combined/'receipt.json').read_text())
assert old_receipt['status']==new_receipt['status']=='passed'
assert old_receipt['phase']==new_receipt['phase']=='audits'
assert old_receipt['stage']=='baseline' and new_receipt['stage']=='combined'
expected_base_tree=subprocess.check_output(['git','rev-parse',plan['base']+'^{tree}'],cwd='/home/lee/clifv',text=True).strip()
assert old_receipt['context']['tree']==expected_base_tree
assert new_receipt['context']['tree']==plan['combined_tree']
old=json.loads((a.baseline/'exact-axiom-sets.json').read_text())
new=json.loads((a.combined/'exact-axiom-sets.json').read_text())
missing=sorted(set(old)-set(new))
changed=sorted(n for n in old if n in new and old[n]!=new[n])
result={'baseline':str(a.baseline),'combined':str(a.combined),'old_roots':len(old),'new_roots':len(new),'missing':missing,'changed':changed,'exact_old_sets_preserved':not missing and not changed,'source_guarded_receipt_hashes':{str(x):hashlib.sha256(x.read_bytes()).hexdigest() for x in [a.baseline/'receipt.json',a.combined/'receipt.json']}}
a.out.write_text(json.dumps(result,indent=2)+'\n')
assert not missing and not changed
print(json.dumps({k:v for k,v in result.items() if k!='source_guarded_receipt_hashes'}))
