from pathlib import Path
import os,json,subprocess,tempfile,hashlib
b=Path('/home/lee/clifv');r=b/'.worktrees/stock-cfg-source-20261025';e=b/'.git/agent-evidence/stock-memory-20261029';env=dict(os.environ);env.update(json.loads((e/'author-env-v1.json').read_text()));env.update(FV_MEMCAP='1G',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',LEAN_NUM_THREADS='1',LEAN_REGALLOC=str(r/'rust/target/release/lean-regalloc'));env.pop('FV_PIPELINE_T',None)
source="""function %configured_memory(i64) -> i32 {
block0(v0: i64):
    nop
    jump block1
block1:
    nop
    v2 = load.i32 notrap v0
    return v2
}
"""
out=e/'configured-provider-regression-before-v1';out.mkdir(exist_ok=False);src=out/'input.clif';src.write_text(source);request=json.loads((e/'configured-provider-request-fixture.next.json').read_text())['request'];request['input_sha256']=hashlib.sha256(src.read_bytes()).hexdigest();config=out/'request.json';config.write_text(json.dumps(request)+'\n');rows=[]
for cleanup in [False,True]:
 data={}
 for mode in ['default','configured']:
  name=mode+('-cleanup' if cleanup else '-plain');captured=out/(name+'.allocator.json');obj=out/(name+'.o');receipt=out/(name+'.receipt.json');args=[str(r/'scripts/memcap.sh'),str(r/'.lake/build/bin/lean-backend'),str(src),str(obj),'--regalloc','regalloc2',*([] if cleanup else ['--no-dead-cleanup'])]
  if mode=='configured':args+=['--stock-config',str(config),'--config-receipt',str(receipt)]
  with (out/(name+'.log')).open('w') as log:done=subprocess.run(args,cwd=r,env=dict(env,LEAN_REGALLOC_KEEP=str(captured)),stdout=log,stderr=subprocess.STDOUT)
  assert done.returncode==0,(name,done.returncode)
  data[mode]=json.loads(captured.read_text())['functions']
  if mode=='configured':
   checked=json.loads(receipt.read_text());assert checked['configuration_accepted'] and not checked['function_rejections'];assert 'experimental' in checked['proof_scope']
 rows.append(dict(cleanup=cleanup,allocator_inputs_equal=data['default']==data['configured'],default=data['default'],configured=data['configured']))
report=dict(status='passed' if all(x['allocator_inputs_equal'] for x in rows) else 'failed',scope='Regression for configured compiler selecting the same proved provider. Before-fix failure is expected.',rows=rows);(out/'receipt.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='rows'}));raise SystemExit(0 if report['status']=='passed' else 1)
