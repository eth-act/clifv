"""Verify terminal evidence before preparing the arithmetic activation PR.
Read-only while gates run; never edits a worktree or pushes/merges anything.
"""
from pathlib import Path
import ast,datetime,hashlib,json,subprocess as sp
view=Path('/home/lee/clifv/.worktrees/stock-driver-incremental')
root=Path('/tmp/stock-arithmetic-spill-repaired-author-gates')
controller=Path('/tmp/stock-arithmetic-spill-repaired-author-gates.py')
expected_head='c2449401454c4b5e000b13074a8aec6149732694'
expected_base='08020ed34bea4a3656c1b080c55087da40f2ebbe'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def git(*args):return sp.check_output(['git',*args],cwd=view,text=True).strip()
def emit(state,**kw):print(json.dumps({'state':state,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),**kw}),flush=True)
state=json.loads((root/'progress.json').read_text())
assert state['head']==expected_head
if state['state']!='per_pr_gates_passed':
 pid=state['pid'];cmd=Path(f'/proc/{pid}/cmdline')
 live=cmd.exists() and str(controller).encode() in cmd.read_bytes()
 emit('author_gate_in_progress' if live else 'author_gate_not_live',controller_live=live,controller_pid=pid,gate_state=state['state'],phase=state.get('phase'),evidence=str(root/'progress.json'))
 raise SystemExit(0)
strict_path=root/'arithmetic-strict-regalloc.json'
assert strict_path.exists(),'actual current-primary strict runtime receipt missing'
strict=json.loads(strict_path.read_text())
assert strict['state']=='strict_real_oracle_runtime_passed' and strict['head']==expected_head
assert strict['runtime_sha256']=='b00043a15c8616e6b4b78bfa2d24634eeacb825bbd75d56db6aa1b1626641b1c'
assert sha(strict['log'])==strict['log_sha256']
strict_text=Path(strict['log']).read_text()
assert strict_text.count('Stock arithmetic lean ')==6 and strict_text.count('Stock arithmetic regalloc2 ')==6
assert 'Stock arithmetic missing-binary negative control passed' in strict_text
assert git('rev-parse','HEAD')==expected_head
assert git('branch','--show-current')=='agent/stock-spill-cycle-resource-repair-20261021'
assert not git('diff','--name-only') and not git('diff','--cached','--name-only')
frozen=json.loads((root/'inputs.json').read_text());assert frozen['head']==expected_head
actual={str(p.relative_to(view)):sha(p) for d in ['FV','FVTest','rust/crates','examples/fv-demo/src','scripts/audit'] for p in (view/d).rglob('*') if p.is_file() and p.suffix in ['.lean','.rs']}
assert actual==frozen['sources'],'frozen source set/hash changed'
headers=json.loads((root/'retained-theorem-source-preflight.json').read_text())
assert headers['head']==expected_head and headers['base']==expected_base
assert headers['retained_old_headers']==39 and len(headers['files'])==6
assert headers['all_old_theorem_headers_unchanged'] and not headers['deleted_existing_Lean_files']
for entry in headers['files']:assert sha(view/entry['file'])==entry['head_sha256']

required=set()
for node in ast.walk(ast.parse(controller.read_text())):
 if isinstance(node,ast.Call) and isinstance(node.func,ast.Name) and node.func.id=='run' and node.args and isinstance(node.args[0],ast.Constant):required.add(node.args[0].value)
required.update(['e2e','legacy-e2e','verified-fv-demo','verified-survey','generated-StockD0MixedPlain','generated-StockD0MixedCleanup'])
logs=state['logs'];assert required<=logs.keys(),sorted(required-logs.keys())
assert any(k.startswith('link-check-') for k in logs),'missing actual example bundle link-check'
for name,record in logs.items():assert sha(record['path'])==record['sha256'],('gate output changed',name)
axioms=json.loads((root/'axiom-set-parity.json').read_text())
assert axioms['previous_roots']>=1181 and axioms['all_previous_axiom_sets_preserved']
assert not axioms['missing'] and not axioms['changed_sets']
identity=json.loads((root/'identity-stage-parity.json').read_text())
assert set(identity)=={'e2e','legacy-e2e'}
for mode,record in identity.items():
 assert record['original']==1150 and record['prior_shipped']==1159 and record['current']>=1159 and record['all_original_and_prior_identities_and_ordered_stages_preserved'],(mode,record)
# Also require the supplemental positive compiler-commit check, after the
# strict real-oracle runtime gate. Keep this independent of the frozen source.
extra_path=root/'committed-route-extra-gate.json'
extra=json.loads(extra_path.read_text())
assert extra['sha256']=='c370fc8cafbe994d6af73a1c4d367b484e6d4d38ac7c0ece33c04fd637665a32'
assert sha(extra['source'])==extra['sha256']
if extra['state']!='passed':
 emit('additional_committed_route_runtime_required',source=extra['source'],expected_pass_records=24,required_prior_gate='arithmetic-dual-allocator-runtime',receipt=str(extra_path))
 raise SystemExit(0)
assert extra['head']==expected_head and extra['pass_records']==24
assert sha(extra['log'])==extra['log_sha256']
assert Path(extra['log']).read_text().count('Stock arithmetic committed ')==24

# Fetch only after terminal validation; new main requires an explicit reconciliation review.
git('fetch','origin','main');current_main=git('rev-parse','origin/main')
result={'state':'ready_for_receipt_and_pr' if current_main==expected_base else 'main_reconciliation_required','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'validated_head':expected_head,'base_main':expected_base,'current_main':current_main,'source_files_verified':len(actual),'gate_records_verified':len(logs),'identity_stage_parity':identity,'axiom_set_parity':axioms,'gate_logs':logs,'strict_regalloc_runtime':strict,'supplemental_committed_route':extra,'remaining':'Write the terminal source+receipt documentation commit (strict runtime repair is already in the frozen candidate), open non-draft substantive PR, author squash after final source/tree review, verify squash tree, notify integrator; full original#140 remains active.'}
Path('/tmp/stock-arithmetic-spill-repaired-ready-to-land.json').write_text(json.dumps(result,indent=2)+'\n')
emit(result['state'],validated_head=expected_head,current_main=current_main,source_files_verified=len(actual),gate_records_verified=len(logs),receipt='/tmp/stock-arithmetic-spill-repaired-ready-to-land.json')
