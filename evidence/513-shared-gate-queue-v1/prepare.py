"""Prepare a shared gate queue. Never materialize a checkout or run a build."""
from pathlib import Path
import argparse, collections, hashlib, json, os, shutil, subprocess, tempfile, tomllib

ROOT = Path('/home/lee/clifv')
SCRIPT_DIR = Path(__file__).resolve().parent
E = SCRIPT_DIR.parent
args=argparse.ArgumentParser()
args.add_argument('--out',type=Path,default=SCRIPT_DIR)
args.add_argument('--extension-binding',type=Path)
cli=args.parse_args()
OUT=cli.out.resolve()
assert OUT.parent==E and OUT.name.startswith('513-shared-gate-queue-')
assert not (OUT/'snapshot-plan.json').exists(), 'Preserve old snapshots. Select a new output version.'
OUT.mkdir(exist_ok=True)
RECOVERY = E/'513-recovery-packet-v1'
FROZEN = 'a4c0726d46c5908b4ac06cf797ee939af8644703'

def git(*args,env=None,input=None):
    return subprocess.check_output(['git',*args],cwd=ROOT,env=env,input=input)

def save(name,data):
    path=OUT/name
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_bytes(data if isinstance(data,bytes) else (json.dumps(data,indent=2)+'\n').encode())

BASE = git('rev-parse','origin/main').decode().strip()
remote=subprocess.check_output(['gh','api','repos/eth-act/clifv/commits/main','--jq','.sha'],cwd=ROOT,text=True).strip()
assert BASE==remote, 'Reconcile actual current main before preparing the next queue version'
TREE513 = git('merge-tree','--write-tree',BASE,'5aae55c32030e3e9f15ab6515a2cccf268751646').decode().strip()
activation = E/'return-pin-production-activation-packet-v1'
typed = E/'return-pin-typed-proof-packet-v1'
act_manifest = json.loads((E/'return-pin-production-activation-packet-v1.json').read_text())
activation_files = {}
for name,digest in act_manifest['files'].items():
    data=(activation/name).read_bytes()
    assert hashlib.sha256(data).hexdigest()==digest,('Activation changed; obtain reviewed final manifest',name)
    activation_files[name]={'owner':'production activation','path':str(activation/name),'sha256':digest}
typed_files = {}
for prefix in ['FV','FVTest','scripts']:
    for p in (typed/prefix).rglob('*.lean'):
        name=str(p.relative_to(typed))
        typed_files[name]={'owner':'typed production','path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
# The typed adapter intentionally replaces the earlier CLI implementation; record the precise overlap.
overlap={p:{'prior':activation_files[p],'replacement':typed_files[p]} for p in set(activation_files)&set(typed_files)}
assert set(overlap)=={'FVTest/E2E/LinkCheckMain.lean'},('Unreviewed packet overlap',set(overlap))
combined_files=activation_files|typed_files
extension=None
if cli.extension_binding:
    extension=json.loads(cli.extension_binding.read_text())
    assert extension['status']=='final-source-binding'
    approval=Path(extension['approval_receipt'])
    assert hashlib.sha256(approval.read_bytes()).hexdigest()==extension['approval_receipt_sha256']
    for name,item in extension['source_files'].items():
        assert hashlib.sha256(Path(item['path']).read_bytes()).hexdigest()==item['sha256']
        if name in combined_files:
            assert extension['overrides'][name]['prior_sha256']==combined_files[name]['sha256']
        combined_files[name]=item

def overlay(tree,files):
    fd,index=tempfile.mkstemp(prefix='owned-index-',dir=OUT)
    os.close(fd);os.unlink(index)
    env=dict(os.environ,GIT_INDEX_FILE=index)
    try:
        git('read-tree',tree,env=env)
        for name,item in sorted(files.items()):
            data=Path(item['path']).read_bytes()
            oid=git('hash-object','-w','--stdin',input=data).decode().strip()
            git('update-index','--add','--cacheinfo','100644',oid,name,env=env)
        return git('write-tree',env=env).decode().strip()
    finally:
        Path(index).unlink(missing_ok=True)
        Path(index+'.lock').unlink(missing_ok=True)

ACT_TREE=overlay(BASE,combined_files)
TREE=overlay(TREE513,combined_files)
def blobs(tree):
    return {line.split('\t')[1]:line.split()[2] for line in git('ls-tree','-r',tree).decode().splitlines()}
baseblobs,fullblobs,frozenblobs=blobs(BASE),blobs(TREE),blobs(FROZEN)
def graph(tree):
    g=collections.defaultdict(set)
    for line in git('grep','-n','-E','^import ',tree,'--','*.lean').decode().splitlines():
        _,p,_,text=line.split(':',3)
        for module in text[7:].split('--')[0].split():
            path=module.replace('.','/')+'.lean'
            if path in fullblobs:g[p].add(path)
    return g
g=graph(TREE)
rev=collections.defaultdict(set)
for p,deps in g.items():
    for d in deps:rev[d].add(p)
def reverse(seeds):
    found=set(seeds);todo=list(found)
    while todo:
        for p in rev[todo.pop()]-found:found.add(p);todo.append(p)
    return found
def closure(seeds):
    found=set(seeds);todo=list(found)
    while todo:
        for p in g.get(todo.pop(),set())-found:found.add(p);todo.append(p)
    return found
changed513=set(git('diff','--name-only',BASE,TREE513).decode().splitlines())
affected513=reverse(p for p in changed513 if p.endswith('.lean'))
affected_activation=reverse(p for p in combined_files if p.endswith('.lean'))
all_modules=sorted(p for p in fullblobs if p.endswith('.lean') and p.startswith(('FV/','FVTest/','corpus/dsl/')))
audits=sorted(p for p in fullblobs if p.startswith('scripts/audit/') and p.endswith('.lean'))
crates=sorted(p for p in fullblobs if p.startswith('crate-proofs/') and p.endswith('.lean'))
lake=tomllib.loads(git('show',TREE+':lakefile.toml').decode())
exes=[x['name'] for x in lake['lean_exe']]
module_closure_equal={p for p in all_modules if all(fullblobs[x]==frozenblobs.get(x) for x in closure([p]))}
focused=json.loads((RECOVERY/'focused-context-v1.json').read_text())
focused_paths={p:d for v in focused['focused_targets'].values() for p,d in v['sources'].items()}
focused_reusable=all(fullblobs.get(p)==d['candidate_blob'] for p,d in focused_paths.items())
assert focused_reusable,'Previously passed focused context changed'
snapshot={'owner':'worker-O execution coordinator','base':BASE,'pr513_tree':TREE513,'activation_without513_tree':ACT_TREE,'combined_tree':TREE,'frozen_source':FROZEN,'activation_sources':activation_files,'typed_sources':typed_files,'extension_sources':extension['source_files'] if extension else {},'required_extension':{'packet':'typed-compiler-modes-packet-v1','status':'bound' if extension else 'pending final manifest; no draft source hashes selected','binding':extension},'intentional_overlaps':overlap,'all_source_blobs':fullblobs,'all_modules':all_modules,'all_audits':audits,'all_crate_sources':crates,'executables':exes,'affected513':sorted(affected513),'affected_activation':sorted(affected_activation),'shared_affected':sorted(affected513&affected_activation),'frozen_source_closure_equal_modules':sorted(module_closure_equal),'focused_pass_reusable_by_exact_source_context':True,'focused_receipt':str(RECOVERY/'focused-current-main-state-v1.json'),'focused_paths':focused_paths,'resource_cap':'12GiB sequential gates; LEAN/OMP/CARGO threads2; aggregate O cap16GiB','no_builds':True,'materialized_snapshot':False,'full_goal_complete':False}
save('snapshot-plan.json',snapshot)
accept=json.loads((SCRIPT_DIR/'source-overlap-acceptance-v1.json').read_text())
assert accept['prior_sha256']==overlap['FVTest/E2E/LinkCheckMain.lean']['prior']['sha256']
assert accept['replacement_sha256']==overlap['FVTest/E2E/LinkCheckMain.lean']['replacement']['sha256']
save('source-overlap-decision.json',{'status':'accepted exact typed CLI replacement','intentional_typed_cli_replacement':overlap,'acceptance':accept,'mode_extension_binding':extension,'no_other_packet_conflicts':True})
save('combined.patch',git('diff','--binary',BASE,TREE))
for label,paths in [('affected-513',affected513),('affected-activation',affected_activation),('shared-affected',affected513&affected_activation)]:
    save(label+'.txt',('\n'.join(sorted(paths))+'\n').encode())
save('fresh-full-gates.json',{'normal_libraries':['FV','FVTest','Corpus'],'all_modules':len(all_modules),'all_audit_files':audits,'crate_sources':crates,'executables':exes,'additional_required':['exact old theorem types/definition values/axioms','runtime matrices with original captured input and retained routes','encoder against LLVM','both cleanup E2E identity and successful-stage preservation','actual linker/checker/generated-proof bundles including typed mixed programs','official Cranelift function agreement and raw Stock comparison','verified fv-demo/survey/deps and unwind examples','exact-head CI and independent per-PR tested/merged tree receipts'],'green_comparison_ci_is_not_full_validation':True})
if OUT!=SCRIPT_DIR:
    for name in ['preflight.py','run-phase.py','compare-axioms.py']:
        shutil.copyfile(SCRIPT_DIR/name,OUT/name)
print(json.dumps({'base':BASE,'combined_tree':TREE,'project_modules':len(all_modules),'audits':len(audits),'crate_sources':len(crates),'executables':len(exes),'affected513':len(affected513),'affected_activation':len(affected_activation),'shared_affected':len(affected513&affected_activation),'frozen_source_equal_closures':len(module_closure_equal),'focused_receipt_reusable':focused_reusable,'no_builds':True}))
