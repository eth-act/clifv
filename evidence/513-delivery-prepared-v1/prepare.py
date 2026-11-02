"""Prepare a fast-forward-safe #513 update. Do not update refs, push, or build."""
from pathlib import Path
import hashlib, json, re, subprocess, datetime

ROOT=Path('/home/lee/clifv')
OUT=Path(__file__).resolve().parent
E=OUT.parent
OLD='5aae55c32030e3e9f15ab6515a2cccf268751646'
PROD='90c51c880b9d614f7c5f9730b8363a6321c840de'
BRANCH='agent/stock-outcome-interface-20261022'
SHARED=E/'513-shared-gate-queue-v2'
RECOVERY=E/'513-recovery-packet-v1'
assert not (OUT/'prepared-state.json').exists(), 'Preserve the prepared commit; use a new version'

def git(*args,input=None):
    return subprocess.check_output(['git',*args],cwd=ROOT,input=input)
def gh(*args):
    return json.loads(subprocess.check_output(['gh',*args],cwd=ROOT,text=True))
def save(name,value):
    (OUT/name).write_bytes(value if isinstance(value,bytes) else (json.dumps(value,indent=2)+'\n').encode())

pr=gh('pr','view','513','--repo','eth-act/clifv','--json','headRefName,headRefOid,state')
parent=gh('pr','view','892','--repo','eth-act/clifv','--json','headRefOid,state,mergeCommit')
assert pr['headRefName']==BRANCH and pr['headRefOid']==OLD and pr['state']=='OPEN'
assert parent['headRefOid']==PROD
save('remote-pr-state.json',{'513':pr,'892':parent})
tree=git('merge-tree','--write-tree',PROD,OLD).decode().strip()
plan=json.loads((SHARED/'snapshot-plan.json').read_text())
assert tree==plan['combined_tree'], ('Prospective joint tree changed',tree,plan['combined_tree'])
changed=git('diff','--name-only',PROD,tree).decode().splitlines()
assert len(changed)==207
save('source.patch',git('diff','--binary',PROD,tree))
old_hashes=json.loads((RECOVERY/'recovery-receipt.json').read_text())['source_sha256']
assert set(changed)==set(old_hashes)
for p,h in old_hashes.items():
    assert hashlib.sha256(git('show',tree+':'+p)).hexdigest()==h,p

# Reuse the exact lexical reader, without running its filesystem or build operations.
reader=(RECOVERY/'historical/stock-outcome-header-parity.py').read_text().split('\ncurrent={}')[0]
namespace={};exec(compile(reader,'preserved-header-reader','exec'),namespace)
declarations=namespace['declarations']
new_headers={}
for p in changed:
    if p.endswith('.lean'):new_headers.update(declarations(git('show',tree+':'+p).decode()))
required=json.loads((RECOVERY/'current-header-parity.json').read_text())['headers']
assert len(required)==372 and all(new_headers.get(k)==v for k,v in required.items())
body_receipt=json.loads((RECOVERY/'consumer-body-parity.json').read_text())
assert len(body_receipt['exact_non_import_source'])==203
strip=lambda b:re.sub(rb'(?m)^import [^\n]*\n',b'',b)
for p in body_receipt['exact_non_import_source']:
    assert strip(git('show',PROD+':'+p))==strip(git('show',tree+':'+p)),p

focused=json.loads((RECOVERY/'focused-context-v1.json').read_text())
tree_blobs={line.split('\t')[1]:line.split()[2] for line in git('ls-tree','-r',tree).decode().splitlines()}
prod_blobs={line.split('\t')[1]:line.split()[2] for line in git('ls-tree','-r',PROD).decode().splitlines()}
focused_paths={p:item for d in focused['focused_targets'].values() for p,item in d['sources'].items()}
for p,item in focused_paths.items():
    assert tree_blobs.get(p)==item['candidate_blob'],('Passed candidate dependency source changed',p)
    assert prod_blobs.get(p)==item['main_blob'],('Passed baseline dependency source changed',p)
save('focused-context-equality.json',{'production_parent':PROD,'candidate_tree':tree,'source_paths':focused_paths,'all230candidate_sources_exact':True,'all228baseline_sources_exact':True,'new_provider_paths_still_absent_from_parent':2,'passed_kernel_receipt':str(RECOVERY/'focused-current-main-state-v1.json'),'passed_kernel_receipt_sha256':hashlib.sha256((RECOVERY/'focused-current-main-state-v1.json').read_bytes()).hexdigest(),'reusable_passed_kernels':7,'reusable_exact_types':8,'reusable_exact_axiom_sets':8,'full_affected_kernel_gate':'UNRUN on this source; direct cheap peer review remains a per-PR alternative'})

message=('Separate stable outcomes and frame values from simulation proof imports\n\n'
         'Recover the preserved #513 extraction on the prospective production checkpoint.\n'
         'Retain original #513 ancestry for a normal fast-forward push.\n'
         'The tree matches the final shared validation source exactly.\n'
         'Preserve all207 source files,372 public headers,203 consumer bodies,\n'
         'and the eight unchanged moved declarations.\n\n'
         'Seven focused kernels and eight current type/axiom comparisons pass\n'
         'in an exact matching source context. Full affected normal, audit, tool,\n'
         'runtime, comparison and generated-consumer gates remain mandatory.\n'
         'The production parent is prospective until #892 lands and source\n'
         'reconciliation, direct review, exact-head CI and tree gates pass.\n')
head=git('commit-tree',tree,'-p',PROD,'-p',OLD,input=message.encode()).decode().strip()
assert subprocess.run(['git','merge-base','--is-ancestor',OLD,head],cwd=ROOT).returncode==0
assert subprocess.run(['git','merge-base','--is-ancestor',PROD,head],cwd=ROOT).returncode==0
save('prepared-commit.raw',git('cat-file','commit',head))
pack=git('pack-objects','--stdout','--revs',input=(head+'\n^'+PROD+'\n^'+OLD+'\n').encode())
save('prepared-objects.pack',pack)
state={'status':'prepared, not pushed','branch':BRANCH,'old_remote_head':OLD,'prospective_production_parent':PROD,'production_parent_pr':892,'production_parent_state':parent,'prepared_head':head,'prepared_tree':tree,'joint_tree_equals_final_shared_queue':True,'changed_files_relative_to_production':207,'source_sha256':old_hashes,'old_public_headers_exact':372,'consumer_bodies_exact':203,'moved_declarations_exact':8,'focused_kernels_reusable':7,'exact_type_axiom_roots_reusable':8,'candidate_context_sources_exact':230,'baseline_context_sources_exact':228,'old_head_is_ancestor':True,'production_head_is_ancestor':True,'normal_push_safe_only_if_remote_head_remains':OLD,'pack_sha256':hashlib.sha256(pack).hexdigest(),'pack_bytes':len(pack),'refs_updated':False,'pushed':False,'builds_run':False,'temporary_indexes':[],'remaining_gates':['Actual892 landed receipt and fresh source reconciliation','After squash landing, add a normal reconciliation descendant with actual main first parent; preserve this head ancestry','One QUICK DIRTY CHEAP direct peer review OR applicable all-tests gate','Exact-head CI','Actual tested/merged tree equality','All broad original union executions remain mandatory; not claimed complete'],'scope_note':'Focused proof and lexical/source parity only. Full affected normal/audit/tool/runtime/filetest/encoder/identity/generated-consumer execution is not claimed.','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
save('prepared-state.json',state)
print(json.dumps({k:state[k] for k in ['status','prepared_head','prepared_tree','changed_files_relative_to_production','old_public_headers_exact','consumer_bodies_exact','focused_kernels_reusable','exact_type_axiom_roots_reusable','pack_bytes','refs_updated','pushed']}))
