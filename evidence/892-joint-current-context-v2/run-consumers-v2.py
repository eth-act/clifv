"""Validate final892, real matrices, then seven513 kernels in a coherent current context."""
from pathlib import Path
import argparse, datetime, fcntl, hashlib, json, os, re, shutil, subprocess

OUT=Path(__file__).resolve().parent
OLD=OUT.parent/'892-current-main-context-v1'
E=OUT.parent
V=Path('/home/lee/clifv/.worktrees/stock-extending-production-20261031')
PKG=OUT/'package'

args=argparse.ArgumentParser();args.add_argument('--attempt',required=True);a=args.parse_args()
assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='892-joint-12G'
providers=json.loads((OUT/'providers-state-v1.json').read_text());assert providers['status']=='passed'
binding=json.loads((OUT/'publication-binding-v4.json').read_text());assert binding['status']=='exact_tree_bound'
assert a.attempt.replace('-','').replace('_','').isalnum()
targets=json.loads((OLD/'reconciled-targets.json').read_text())
context=json.loads((OUT/'context.json').read_text());assert binding['source_context_tree']==context['joint_tree']
if binding['candidate_tree']!=context['joint_tree']:
    doc_delta=subprocess.check_output(['git','diff','--name-only',context['joint_tree'],binding['candidate_tree']],cwd='/home/lee/clifv',text=True).splitlines()
    assert doc_delta==['LEARNINGS.md'],('Unreviewed source bridge',doc_delta)

logs=OUT/'runs'/a.attempt;assert not logs.exists();logs.mkdir(parents=True)
lock=(OUT/'focused-owner.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()))
env.pop('FV_LAKE_CACHE',None)
env.update(FV_ROOT=str(PKG),FV_MEMCAP='12G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',CARGO_BUILD_JOBS='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false')
env['LAKE_CACHE_DIR']=str(PKG/'.lake/ci-cache')
env['LEAN_REGALLOC']=str(V/'rust/target/release/lean-regalloc')
lean=context['lean_executable'];leanpath=context['toolchain_library']
env['PATH']=str(Path(lean).parent)+':'+env['PATH']
env['LEAN_PATH']=str(PKG/'.lake/build/lib/lean')+':'+leanpath
env.pop('FV_MEMCAP_OFF',None)
env['PYTHONDONTWRITEBYTECODE']='1'
lib=PKG/'.lake/build/lib/lean'
records=[]
def sha(p):
    result=hashlib.sha256()
    with Path(p).open('rb') as stream:
        for chunk in iter(lambda:stream.read(1024*1024),b''):result.update(chunk)
    return result.hexdigest()

def source_guard():
    for p,h in context['source_hashes'].items():assert sha(PKG/p)==h,('Candidate source changed',p)


def run(label,argv,*,root=PKG,extra=None):
    argv=list(argv)
    if argv and str(argv[0])==lean:argv.insert(1,'-j2')
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
normal_providers=json.loads((OUT/'normal-providers-state-v1.json').read_text());assert normal_providers['status']=='passed'
assert all(p[:-5].replace('/','.') in normal_providers['outputs'] for p in targets['queue892'])
run('892-audits',['python3',OUT/'helpers/axiom-audit.py','--cwd',PKG,'--log-dir',logs/'892-audit',*[PKG/p for p in targets['892_audits']]])
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
    run(label+'-audit',['python3',OUT/'helpers/axiom-audit.py','--cwd',PKG,'--log-dir',logs/(label+'-audit'),audit])
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
result={'status':'passed','baseline':binding['actual_base'],'head892':binding['actual_head892'],'tree892':binding['candidate_tree'],'provider_receipt_sha256':sha(OUT/'providers-state-v1.json'),'892_kernels':12,'892_audit_files':len(targets['892_audits']),'actual_backend_object_comparisons':6,'actual_complete_bundles':6,'actual_additional_typed_compiler_modes':2,'actual_generated_roots':root_count,'generated_sources':generated,'original_inputs_and_allocator_answers':stable_inputs,'records':records,'owned_output_sha256':{p:sha(lib/Path(p).with_suffix('.olean')) for p in targets['queue892']},'normal_key_scope':'Complete current-context direct kernels, AX and actual matrix only. Full normal Lake keys/importers remain mandatory.','full_goal_complete':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(logs/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'passed','892_kernels':12,'actual_bundles':6,'generated_roots':68,'full_goal_complete':False}),flush=True)
