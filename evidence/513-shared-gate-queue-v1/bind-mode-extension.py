"""Bind only a final coordinator-approved compiler-mode manifest. Never run Lean."""
from pathlib import Path
import argparse, hashlib, json

OUT=Path(__file__).resolve().parent
E=OUT.parent
p=argparse.ArgumentParser()
p.add_argument('--manifest',type=Path,required=True)
p.add_argument('--approval',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
a=p.parse_args()
assert not a.out.exists(), 'Preserve earlier bindings'
approval=json.loads(a.approval.read_text())
assert approval['approved_by']=='worker-O execution coordinator'
assert approval['finalized'] is True and approval['final_cli_sources'] is True
assert approval['actual_attempt_and_nonvacuity']=='passed'
assert approval['manifest_sha256']==hashlib.sha256(a.manifest.read_bytes()).hexdigest()
manifest=json.loads(a.manifest.read_text())
assert manifest['files'], 'Use the final publication source inventory, not a broad import-context receipt'
plan=json.loads((OUT/'snapshot-plan.json').read_text())
prior=plan['activation_sources']|plan['typed_sources']
files,overrides={},{}
for name,value in manifest['files'].items():
    assert name.startswith(('FV/','FVTest/','scripts/audit/')) and name.endswith('.lean')
    if isinstance(value,str):
        packet='typed-compiler-modes-packet-v1';digest=value
    else:
        packet=value.get('packet','typed-compiler-modes-packet-v1');digest=value['sha256']
    source=E/packet/name
    assert source.resolve().is_relative_to(E)
    assert hashlib.sha256(source.read_bytes()).hexdigest()==digest,('Final source changed',name)
    files[name]={'owner':'final typed compiler modes','path':str(source),'sha256':digest}
    if name in prior and prior[name]['sha256']!=digest:
        overrides[name]={'prior_sha256':prior[name]['sha256'],'replacement_sha256':digest}
assert approval['allowed_overrides']==overrides, 'The coordinator must bind each final source replacement exactly'
receipts=approval['required_receipts']
assert receipts
for path,digest in receipts.items():
    assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==digest
binding={'status':'final-source-binding','source_manifest':str(a.manifest.resolve()),'source_manifest_sha256':approval['manifest_sha256'],'approval_receipt':str(a.approval.resolve()),'approval_receipt_sha256':hashlib.sha256(a.approval.read_bytes()).hexdigest(),'source_files':files,'overrides':overrides,'required_receipts':receipts,'no_builds':True,'no_materialization':True}
a.out.write_text(json.dumps(binding,indent=2)+'\n')
print(json.dumps({'status':binding['status'],'files':len(files),'overrides':len(overrides),'no_builds':True}))
