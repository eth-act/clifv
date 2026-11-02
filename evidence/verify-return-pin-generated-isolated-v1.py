from pathlib import Path
import datetime,fcntl,hashlib,json,os,subprocess,time
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029';view=b/'.worktrees/stock-extending-production-20261031'
while True:
 try:command=Path('/proc/2048716/cmdline').read_bytes()
 except FileNotFoundError:break
 if b'return-pin-consumer-isolated-v1' not in command:break
 time.sleep(10)
prior=json.loads((e/'return-pin-consumer-isolated-state-v1.json').read_text());assert prior['status']=='passed'
lock=(e/'main870-cache-import.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX)
r=Path(prior['isolated_package']);head=prior['head'];output=r/'.lake/build/lib/lean';packet=e/'return-pin-generated-proof-packet-v1';manifest=json.loads((e/'return-pin-generated-proof-packet-v1.json').read_text());driver=e/manifest['driver'];assert hashlib.sha256(driver.read_bytes()).hexdigest()==manifest['driver_sha256']
logs=e/'return-pin-generated-isolated-kernel-v1';assert not logs.exists();logs.mkdir()
env=dict(os.environ);env.update(json.loads((e/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(view),FV_MEMCAP='3G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false')
env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=view,env=env,text=True).strip()
def kernel(source,root,name,log_path):
 target=output/Path(name).with_suffix('');target.parent.mkdir(parents=True,exist_ok=True)
 with log_path.open('w') as log:
  subprocess.run(['nice','-n','10',str(view/'scripts/memcap.sh'),'lake','env','lean','--root='+str(root),str(source),'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c'],cwd=r,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
owned=[]
generated = logs / 'generated'
assert not generated.exists(), 'Preserve the previous generated proof attempt before retrying'
with (logs / 'generate.log').open('w') as log:
    subprocess.run(['nice', '-n', '10', str(view / 'scripts/memcap.sh'), 'lake', 'env', 'lean', '--run',
                    str(driver), str(generated)],
                   cwd=r, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
cases = json.loads((generated / 'manifest.json').read_text())
assert len(cases) == 12
assert {(c['mixed'], c['cleanup'], c['split'], c['all_stack']) for c in cases} == {
    (mixed, cleanup, split, stack) for mixed in [False, True] for cleanup in [False, True]
    for split in ([False, True] if mixed else [False]) for stack in [False, True]}
proof_hashes = {}
for case in cases:
    label = case['module']
    assert label.startswith('WorkerOReturnPinGenerated')
    for index, name in enumerate(case['files']):
        source = Path(name)
        relative = source.relative_to(generated)
        assert relative.parts[0] == 'Crates'
        assert not (r / relative).exists()
        kernel(source, generated, relative, logs / (label + '-' + str(index) + '.log'))
        proof_hashes[str(relative)] = hashlib.sha256(source.read_bytes()).hexdigest()
        owned.append(str(relative))
    audit = logs / (label + '-audit.lean')
    # Each imported crate is a fixed original input. Generic stack/checker roots have separate standard-only audits.
    audit.write_text('import Crates.' + label + '\n\n' + '\n'.join(
        '#print axioms Crates.' + label + '.' + root + ' -- witness: native_decide'
        for root in ['okB_input', 'link_ok', 'base_closed', 'bin_ok', 'correct_0', 'correct_stack_0']) + '\n')
    with (logs / (label + '-audit-summary.log')).open('w') as log:
        subprocess.run(['nice', '-n', '10', str(view / 'scripts/memcap.sh'), 'python3', str(view/'scripts/axiom-audit.py'), '--cwd', str(r),
                        '--log-dir', str(logs / (label + '-audit')), str(audit)],
                       cwd=r, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    print('GENERATED', label, 'passed', flush=True)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=view,text=True).strip()==head
receipt=dict(status='passed',head=head,cases=12,fixed_generated_roots=72,generated_hashes=proof_hashes,source_packet='return-pin-generated-proof-packet-v1',isolated_package=str(r),requires_current_main_gates=True,full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(e/'return-pin-generated-isolated-state-v1.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(dict(status='passed',cases=12,fixed_generated_roots=72,requires_current_main_gates=True)),flush=True)
