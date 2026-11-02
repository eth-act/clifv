"""Run one source-guarded phase after the coordinator releases the existing view."""
from pathlib import Path
import argparse, datetime, fcntl, hashlib, json, os, re, subprocess
from preflight import OUT, PLAN, check

p=argparse.ArgumentParser()
p.add_argument('--root',required=True)
p.add_argument('--release',required=True)
p.add_argument('--stage',choices=['baseline','combined'],required=True)
p.add_argument('--phase',choices=['normal','audits','tools','crates','e2e','comparison','runtime-encoder','examples','crate-parity','retained-matrices','nonmemory-matrices','configured-tests'],required=True)
p.add_argument('--attempt',required=True)
a=p.parse_args()
assert os.environ.get('WORKER_O_FULL_GATE_GRANTED')=='513-production-shared'
assert a.attempt.replace('-','').replace('_','').isalnum()
context=check(a.root,a.release,a.stage)
root=Path(a.root).resolve()
logs=OUT/'runs'/a.stage/a.phase/a.attempt
assert not logs.exists(), 'Choose a new attempt; preserve old logs'
logs.mkdir(parents=True)
lock=(OUT/'exclusive-shared-gate.lock').open('a+')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
env=dict(os.environ)
env.update(json.loads((OUT.parent/'author-env-v1.json').read_text()))
env.update(FV_ROOT=str(root),FV_MEMCAP='12G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',CARGO_BUILD_JOBS='2')
env.pop('BLESS',None)
# Reuse the one existing artifact cache. Never invent another cache path.
assert env.get('FV_LAKE_CACHE'), 'The coordinator must bind the existing shared cache'
env['PATH']=str(root/'rust/target/release')+':'+env.get('PATH','')
commands=[]
if a.phase=='normal':
    commands=[('normal',['python3','scripts/lake-serial-build.py','--budget','12G','--max-cap','12G','--max-jobs','1','--out',str(logs/'scheduler'),'FV','FVTest','Corpus'],root,[0])]
elif a.phase=='audits':
    commands=[('audits',['python3','scripts/axiom-audit.py','--log-dir',str(logs/'audit')],root,[0])]
elif a.phase=='tools':
    # Sequential targets keep the peak bounded; the preceding normal phase supplies module products.
    commands=[(name,['lake','build',name],root,[0]) for name in PLAN['executables']]
    commands += [('rust-tools',['cargo','build','--release','-p','cargo-fv','-p','clif-data-export','-p','lean-regalloc'],root/'rust',[0]),('prejit-export',['cargo','build','--manifest-path','tools/prejit-export/Cargo.toml'],root,[0])]
elif a.phase=='crates':
    commands=[('crates',['lake','build'],root/'crate-proofs',[0])]
elif a.phase=='e2e':
    commands=[('cleanup',['lake','exe','lean-e2e-check','--identity-report',str(logs/'cleanup-identities.json')],root,[0]),('legacy',['lake','exe','lean-e2e-check','--no-dead-cleanup','--identity-report',str(logs/'legacy-identities.json')],root,[0])]
elif a.phase=='comparison':
    commands=[('lean-backend',['python3','scripts/stock-compiler-compare.py','--jobs','2','--out',str(logs/'lean-backend')],root,[0,10]),('raw-stock',['python3','scripts/stock-compiler-compare.py','--jobs','2','--lean-compiler',str(root/'.lake/build/bin/lean-stock-lowering-compare'),'--out',str(logs/'raw-stock')],root,[0,10])]
elif a.phase=='runtime-encoder':
    commands=[('encoder',['scripts/lean-backend-encode-check.sh'],root,[0]),('filetests',['scripts/lean-backend-filetests.sh'],root,[0]),('arm-fault',['scripts/arm-fault-cosim.sh'],root,[0]),('clif',['scripts/clif-filetests.sh'],root,[0]),('opt',['scripts/opt-difftest.sh'],root,[0])]
    commands += [('float-spec',['scripts/float-spec.sh'],root,[0])]
    commands += [('clif-unwind-native',['scripts/clif-unwind-native.sh'],root,[0])]
elif a.phase=='examples':
    commands=[('rust-tools',['cargo','build','--release','-p','cargo-fv','-p','clif-data-export','-p','lean-regalloc'],root/'rust',[0])]
    commands += [(name,['examples/compare.sh','examples/'+name,'--lean-link','--verified','--keep-temps'],root,[0]) for name in ['fv-demo','survey','deps']]
    commands += [('bigframe-unwind',['examples/compare.sh','examples/bigframe-unwind','--keep-temps'],root,[0])]
elif a.phase=='crate-parity':
    for name in ['fv-demo','survey','deps']:
        dirs=sorted((root/'examples'/name/'target/fv').glob('*/tmp'))
        assert dirs, ('First execute the exact-head example with --keep-temps',name)
        commands.append((name,['python3','scripts/stock-crate-parity.py','--json',str(logs/(name+'-parity.json')),*map(str,dirs)],root,[0]))
elif a.phase=='retained-matrices':
    pairs=json.loads((OUT.parent/'integer-store-native-matrix-source-v1.json').read_text())['pairs']
    assert len(pairs)==13
    for ty in ['i8','i16','i32','i64']:
        for pair in pairs:
            label='mixed-'+ty+'-'+pair['op']+'-'+pair['ty']
            commands.append((label,['python3','scripts/check-stock-memory-store-integration.py','--output',str(logs/label),'--load-type',ty,'--store-type',pair['ty'],'--store-op',pair['op']],root,[0]))
    for cfg in [False,True]:
        for pair in pairs:
            label=('cfg-' if cfg else 'singleton-')+pair['op']+'-'+pair['ty']
            commands.append((label,['python3','scripts/check-stock-memory-store-integration.py','--output',str(logs/label),'--store-type',pair['ty'],'--store-op',pair['op'],*(['--memory-cfg'] if cfg else [])],root,[0]))
    loads=[(ty,['--load-type',ty]) for ty in ['i8','i16','i32','i64']]+[('cfg32',['--memory-cfg'])]
    for op,types in [('uload8',['i16','i32','i64']),('sload8',['i16','i32','i64']),('uload16',['i32','i64']),('sload16',['i32','i64']),('uload32',['i64']),('sload32',['i64'])]:
        loads += [(op+'-'+ty,['--load-op',op,'--load-type',ty]) for ty in types]
    assert len(loads)==17
    for label,options in loads:
        commands.append(('load-'+label,['python3','scripts/check-stock-memory-integration.py','--output',str(logs/('load-'+label)),*options],root,[0]))
    for kind in ['parameter','conditional-forward','conditional','forward','linear','scalar-entry','entry','cfg']:
        commands.append(('retained-'+kind,[str(root/'.lake/build/bin/stock-memory-retained'),kind],root,[0]))
    capture=root/'scripts/testdata/stock-memory-captured-copy-original.clif'
    assert hashlib.sha256(capture.read_bytes()).hexdigest()=='9d39c7307e7fc9b4c3f334692726fae11926683d31f27ea49d032d46e99e70ce'
    commands.append(('original-captured-copy',['python3','scripts/check-stock-memory-store-integration.py','--output',str(logs/'original-captured-copy'),'--captured-copy',str(capture)],root,[0]))
elif a.phase=='nonmemory-matrices':
    native={'popcount','minmax','cmp','highmul','div','mixeddiv','returneddiv','generaldiv','narrow','mask','cfg','cfgentry','cfgscalarentry','cfglinear','cfgforward','cfgconditional','cfgconditionalforward','cfgparameter'}
    kinds=['mixed','logical','scalar','not','mul','shift','cast','bit','popcount','minmax','cmp','highmul','div','mixeddiv','returneddiv','generaldiv','narrow','mask','cfg','cfgentry','cfgscalarentry','cfglinear','cfgforward','cfgconditional','cfgconditionalforward','cfgparameter']
    for kind in kinds:
        commands.append((kind,['python3','scripts/check-stock-mixed-integration.py','--class',kind,'--fixture-mode','native' if kind in native else 'interpreted','--output',str(logs/kind)],root,[0]))
elif a.phase=='configured-tests':
    commands=[('configured-provider',['python3','-m','unittest','discover','-s','scripts','-p','test_stock_configured_provider.py','-v'],root,[0]),('pipeline',['python3','-m','unittest','discover','-s','scripts','-p','test_stock_pipeline.py','-v'],root,[0])]
records=[]
for label,argv,cwd,allowed in commands:
    check(root,a.release,a.stage)
    logfile=logs/(label+'.log')
    with logfile.open('w') as stream:
        result=subprocess.run(['nice','-n','10',str(root/'scripts/memcap.sh'),*argv],cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT)
    record={'id':label,'argv':argv,'cwd':str(cwd),'exit':result.returncode,'accepted_exit_codes':allowed,'log':str(logfile),'log_sha256':hashlib.sha256(logfile.read_bytes()).hexdigest(),'state':'passed' if result.returncode in allowed else 'failed'}
    records.append(record)
    (logs/'progress.json').write_text(json.dumps({'context':context,'commands':records},indent=2)+'\n')
    assert record['state']=='passed', ('Inspect the preserved diagnostic before retrying',label,result.returncode)
    if a.phase=='comparison':
        measurement=json.loads((logs/label/'results.json').read_text())
        assert measurement['progress']=='finished'
        assert not any(t.get('status')=='harness_error' for t in measurement['tests'])
        assert measurement['configuration_overrides']==[] and measurement['binary_normalization'] is False
    check(root,a.release,a.stage)
    print('GATE',label,'passed',flush=True)
if a.phase=='audits':
    roots={}
    for log in (logs/'audit').glob('*.log'):
        text=' '.join(log.read_text().split())
        for name,axes in re.findall(r"'(.+?)' depends on axioms: \[([^]]*)\]",text):
            value=sorted(set(x.strip() for x in axes.split(',') if x.strip()))
            assert name not in roots or roots[name]==value
            roots[name]=value
        for name in re.findall(r"'(.+?)' does not depend on any axioms",text):roots[name]=[]
    assert roots
    (logs/'exact-axiom-sets.json').write_text(json.dumps(roots,indent=2)+'\n')
receipt={'status':'passed','stage':a.stage,'phase':a.phase,'context':context,'commands':records,'tool_hashes':{p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in ['scripts/memcap.sh','scripts/lake-serial-build.py','scripts/axiom-audit.py']},'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'all_tests_passed':False,'full_goal_complete':False,'scope_note':'One phase only. Comparison exit10 records a complete measurement with known gaps, not equivalence. Separate projection/identity/AX and real generated-consumer gates remain required.'}
(logs/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':'passed','phase':a.phase,'stage':a.stage,'full_goal_complete':False}),flush=True)
