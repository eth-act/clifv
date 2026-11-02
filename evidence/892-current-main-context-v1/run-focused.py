"""Validate final892, real matrices, then seven513 kernels in a coherent current context."""
from pathlib import Path
import argparse, datetime, fcntl, hashlib, json, os, re, shutil, subprocess

OUT=Path(__file__).resolve().parent
E=OUT.parent
V=Path('/home/lee/clifv/.worktrees/stock-extending-production-20261031')
PKG=OUT/'package'
P513=OUT/'package-513'
args=argparse.ArgumentParser();args.add_argument('--attempt',required=True);a=args.parse_args()
assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='892-current-main'
grant=json.loads((OUT/'kernel-grant.json').read_text())
assert grant['owner']=='worker-O execution coordinator' and grant['slot']=='3G'
assert grant['explicit_grant_after_io_split'] is True
assert grant['head892']=='36dd36a6c1746acb1741dd5c984b0ead1b8a2d18'
assert a.attempt.replace('-','').replace('_','').isalnum()
recovery=json.loads((OUT/'ci-recovery-state.json').read_text())
assert recovery['status']=='coherent_current_context_ready', 'No build is permitted before coherent actual-current context exists'
targets=json.loads((OUT/'reconciled-targets.json').read_text())
context=json.loads((OUT/'context.json').read_text())
logs=OUT/'runs'/a.attempt;assert not logs.exists();logs.mkdir(parents=True)
lock=(OUT/'focused-owner.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()))
env.pop('FV_LAKE_CACHE',None)
env.update(FV_ROOT=str(PKG),FV_MEMCAP='3G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',CARGO_BUILD_JOBS='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false')
env['LAKE_CACHE_DIR']=str(PKG/'.lake/ci-cache')
env['LEAN_REGALLOC']=str(V/'rust/target/release/lean-regalloc')
toolpath=subprocess.check_output(['lake','env','printenv','PATH'],cwd=PKG,env=env,text=True).strip()
lean=shutil.which('lean',path=toolpath);assert lean
leanpath=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=PKG,env=env,text=True).strip()
env['PATH']=toolpath
lib=PKG/'.lake/build/lib/lean'
env['LEAN_PATH']=str(lib)+':'+leanpath
records=[]
def sha(p):
    result=hashlib.sha256()
    with Path(p).open('rb') as stream:
        for chunk in iter(lambda:stream.read(1024*1024),b''):result.update(chunk)
    return result.hexdigest()

# The I/O watcher can predate this recording helper. Never compile without retained import hashes.
baseline_hash_file=OUT/'coherent-baseline-output-hashes.json'
if not baseline_hash_file.exists():
    outputs={}
    for module in (OUT/'baseline-normal-targets.txt').read_text().splitlines():
        stem=lib/module.replace('.','/');assert Path(str(stem)+'.olean').is_file()
        outputs[module]={}
        for suffix in ['.olean','.ilean','.olean.private','.olean.server','.ir','.trace','.c']:
            path=Path(str(stem)+suffix)
            if path.is_file():outputs[module][suffix]={'path':str(path.relative_to(PKG)),'sha256':sha(path),'bytes':path.stat().st_size}
    baseline_hash_file.write_text(json.dumps({'head':context['base'],'producer_run':recovery['run'],'normal_key_attempt':recovery['context_attempt'],'modules':outputs},indent=2)+'\n')

def source_guard():
    for p,h in context['source_hashes'].items():assert sha(PKG/p)==h,('Candidate source changed',p)
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=V,text=True).strip()==context['frozen_source']

def run(label,argv,*,root=PKG,extra=None):
    child=dict(env);child.update(extra or {})
    child['FV_MEMCAP_STATS']=str(logs/(label+'.mem'));child['FV_MEMCAP_UNIT']='worker-o-current892-'+a.attempt+'-'+label.lower()
    output=logs/(label+'.log')
    assert not output.exists(), 'Use a fresh attempt; preserve all diagnostics'
    with output.open('w') as stream:result=subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),*map(str,argv)],cwd=root,env=child,stdout=stream,stderr=subprocess.STDOUT)
    records.append({'label':label,'argv':list(map(str,argv)),'exit':result.returncode,'log_sha256':sha(output)})
    (logs/'progress.json').write_text(json.dumps({'records':records},indent=2)+'\n')
    assert result.returncode==0,('Inspect exact diagnostic before retry',label,result.returncode)
    print('PASSED',label,flush=True)

def kernel(label,source,library,root=PKG):
    target=library/Path(source).with_suffix('');target.parent.mkdir(parents=True,exist_ok=True)
    # Never write through an artifact/cache hardlink; every destination is owned.
    for p in target.parent.glob(target.name+'.*'):
        if p.is_file() or p.is_symlink():p.unlink()
    run(label,[lean,'--root='+str(root),root/source,'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c'],root=root,extra={'LEAN_PATH':str(library)+':'+leanpath})

source_guard()
for n,p in enumerate(targets['queue892']):kernel('892-kernel-'+str(n),p,lib)
run('892-audits',['python3',V/'scripts/axiom-audit.py','--cwd',PKG,'--log-dir',logs/'892-audit',*[PKG/p for p in targets['892_audits']]])
axioms={}
for path in (logs/'892-audit').glob('*.log'):
    text=' '.join(path.read_text().split())
    for name,axes in re.findall(r"'(.+?)' depends on axioms: \[([^]]*)\]",text):axioms[name]=sorted(x.strip() for x in axes.split(',') if x.strip())
    for name in re.findall(r"'(.+?)' does not depend on any axioms",text):axioms[name]=[]
old_variants=json.loads((E/'typed-compiler-modes-packet-v1/old-variant-parity-v1.json').read_text())['pairs']
assert len(old_variants)==6
for pair in old_variants.values():
    assert axioms[pair['old']]==axioms[pair['new']]==sorted(pair['axioms']),('Old typed axiom set changed',pair)
(logs/'exact-old-typed-axiom-parity.json').write_text(json.dumps({'status':'passed','pairs':old_variants,'actual_audit_roots':axioms},indent=2)+'\n')
run('892-backend-object-smoke',[lean,PKG/'matrix/BackendEntrySmoke.lean'])
run('892-prepare-integer',[lean,'--run',PKG/'matrix/PrepareActualBundles.lean',logs/'integer-bundles'])
run('892-prepare-typed',[lean,'--run',PKG/'matrix/PrepareTypedBundles.lean',logs/'typed-bundles'])
cases=json.loads((logs/'integer-bundles/manifest.json').read_text())+json.loads((logs/'typed-bundles/manifest.json').read_text())
assert len(cases)==6
oldcases=json.loads((E/'return-pin-production-activation-packet-v1/actual-bundle-state-v9.json').read_text())['cases']+json.loads((E/'return-pin-typed-proof-packet-v1/actual-bundle-state-v1.json').read_text())['cases']
old_by_name={c['module']:c for c in oldcases}
generated={};root_count=0;stable_inputs={}
def check_bundle(case,*,backend=True):
    global root_count
    label=case['module'];directory=Path(case['dir']);flag='--dead-cleanup' if case['cleanup'] else '--no-dead-cleanup'
    reference=old_by_name.get(label)
    if reference:
        assert sha(case['input'])==sha(reference['input']),('Original complete input changed',label)
    if backend:
        ra=directory/'actual-ra.json'
        run(label+'-backend',[lean,'--run',PKG/'FVTest/Backend/Main.lean',case['input'],directory/'actual.o','--regalloc','lean','--dump',directory/'actual-dump',flag],extra={'FV_RA_OUT':str(ra)})
        answers=json.loads(ra.read_text())['functions'];bundle=json.loads((directory/'bundle.json').read_text())
        functions=bundle['units'][0]['functions'];assert len(answers)==len(functions)
        for entry,answer in zip(functions,answers):Path(entry['ra']).write_text(json.dumps({'functions':[answer]})+'\n')
        if reference:assert json.loads((Path(reference['dir'])/'actual-ra.json').read_text())==json.loads(ra.read_text()),('Actual allocator answers changed',label)
        template='ReflowTypedBundle.lean' if 'Typed' in label else 'ReflowActualBundle.lean'
        run(label+'-reflow',[lean,'--run',PKG/'matrix'/template,directory,str(case['cleanup']).lower()])
        layout=json.loads((directory/'actual-layout.json').read_text());bundle['markers']=layout;bundle['symbols']=layout
        (directory/'bundle.json').write_text(json.dumps(bundle,indent=2)+'\n')
    stable={str(p.relative_to(directory)):sha(p) for p in directory.iterdir() if p.name.endswith(('.clif','.ra.json')) or p.name=='actual-ra.json'}
    stable_inputs[label]=stable
    run(label+'-linker',[lean,'--run',PKG/'FVTest/Link/LeanLinkMain.lean',directory,flag])
    if 'Typed' in label:
        text=(logs/(label+'-linker.log')).read_text()
        assert 'written by Link.TypedCompilerWith.attempt' in text and 'Link.TypedCompilerWith.attempt_correct_source_peak' in text
        assert 'coverage: none' not in text
    output=logs/'generated/Crates'/(label+'.lean');output.parent.mkdir(parents=True,exist_ok=True)
    run(label+'-checker',[lean,'--run',PKG/'FVTest/E2E/LinkCheckMain.lean',directory,flag,'--lean',output,'--module',label])
    text=(logs/(label+'-checker.log')).read_text();assert 'okB: true' in text and 'binary: ok' in text
    if 'Typed' in label:assert 'checker: typed Stock' in text
    kernel(label+'-generated','Crates/'+label+'.lean',lib,root=logs/'generated')
    public=['okB_input','link_ok','base_closed','bin_ok']+[f'correct_{n}' for n in range(len(case['entries']))]+[f'correct_stack_{n}' for n in range(len(case['entries']))]
    audit=logs/(label+'-audit.lean');audit.write_text('import Crates.'+label+'\n'+'\n'.join('#print axioms Crates.'+label+'.'+n+' -- witness: native_decide' for n in public)+'\n')
    run(label+'-audit',['python3',V/'scripts/axiom-audit.py','--cwd',PKG,'--log-dir',logs/(label+'-audit'),audit])
    assert all(sha(directory/p)==h for p,h in stable.items())
    generated[str(output.relative_to(logs))]=sha(output);root_count+=len(public)

for case in cases:check_bundle(case)
# Preserve the two additional real compiler-mode executions from the final packet's matrix.
for case in [c for c in cases if 'Typed' in c['module']]:
    label='WorkerOTypedCompiler'+('Cleanup' if case['cleanup'] else 'Raw')
    directory=logs/'typed-compiler-bundles'/label;shutil.copytree(case['dir'],directory)
    bundle=json.loads((directory/'bundle.json').read_text());bundle['exe']=str(directory/'program.elf')
    for unit in bundle['units']:
        unit['data']=str(directory/Path(unit['data']).name)
        for entry in unit['functions']:
            for k in ['dump','ra']:entry[k]=str(directory/Path(entry[k]).name)
    (directory/'bundle.json').write_text(json.dumps(bundle,indent=2)+'\n')
    clone=dict(case,module=label,dir=str(directory),exe=str(directory/'program.elf'),input=str(directory/'input.clif'))
    check_bundle(clone,backend=False)
assert root_count==68
source_guard()
run('513-current-baseline-types',[lean,PKG/'Baseline513Types.lean'])
# Stage513 inherits only this owned, completed892 context. No frozen/shared path is a writer.
lib513=P513/'.lake/build/lib/lean';lib513.mkdir(parents=True,exist_ok=True)
owned513={str(Path(p).with_suffix('')) for p in targets['queue513']}
for source in lib.rglob('*'):
    if not source.is_file() or not any(source.name.endswith(x) for x in ['.olean','.ilean','.olean.private','.olean.server']):continue
    rel=source.relative_to(lib)
    if any(str(rel).startswith(p+'.') for p in owned513):continue
    target=lib513/rel;target.parent.mkdir(parents=True,exist_ok=True);assert not target.exists();os.link(source,target)
for n,p in enumerate(targets['queue513']):kernel('513-kernel-'+str(n),p,lib513,root=P513)
run('513-current-candidate-types',[lean,P513/'Candidate513Types.lean'],root=P513,extra={'LEAN_PATH':str(lib513)+':'+leanpath})
assert (logs/'513-current-baseline-types.log').read_bytes()==(logs/'513-current-candidate-types.log').read_bytes()
source_guard()
result={'status':'passed','baseline':context['base'],'head892':targets['head892'],'tree892':targets['tree892'],'head513':targets['head513'],'tree513':targets['tree513'],'coherent_ci_recovery_receipt_sha256':sha(OUT/'ci-recovery-state.json'),'892_kernels':len(targets['queue892']),'892_audit_files':len(targets['892_audits']),'actual_backend_object_comparisons':6,'actual_complete_bundles':6,'actual_additional_typed_compiler_modes':2,'actual_generated_roots':root_count,'generated_sources':generated,'original_inputs_and_allocator_answers':stable_inputs,'513_kernels':len(targets['queue513']),'513_exact_type_axiom_roots':targets['513_exact_type_axiom_roots'],'records':records,'owned_output_sha256':{p:sha(lib/Path(p).with_suffix('.olean')) for p in targets['queue892']}|{p:sha(lib513/Path(p).with_suffix('.olean')) for p in targets['queue513']},'normal_key_scope':'Verified current baseline imports only. Final candidate direct kernels are not full reverse-importer/library normal keys.','full_goal_complete':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(logs/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'passed','892_kernels':12,'actual_bundles':6,'generated_roots':68,'513_kernels':7,'exact_types_axiom_sets':8,'full_goal_complete':False}),flush=True)
