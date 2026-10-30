from pathlib import Path
import os,json,subprocess,datetime,time,hashlib,psutil
b=Path('/home/lee/clifv');r=b/'.worktrees/stock-cfg-source-20261025';e=b/'.git/agent-evidence/stock-memory-20261029';env=dict(os.environ);env.update(json.loads((e/'author-env-v1.json').read_text()));env.update(FV_ROOT=str(r),FV_MEMCAP='4G',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LEAN_NUM_THREADS='2',CARGO_BUILD_JOBS='2');env.pop('FV_PIPELINE_T',None);state=e/'captured-real-inputs-state-v2.json';records=[]
def save(status,**x):state.write_text(json.dumps(dict(status=status,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),records=records,**x),indent=2)+'\n')
save('waiting',dependency=2051023)
while psutil.pid_exists(2051023):time.sleep(2)
try:
 assert json.loads((e/'captured-current-consumers-state-v2.json').read_text())['status']=='passed'
 out=e/'captured-real-inputs-v2';out.mkdir(exist_ok=False)
 expected=json.loads((e/'memory-captured-inventory-current/receipt.json').read_text())['sources']
 digest=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
 assert all(digest(p)==h for p,h in expected.items())
 save('running',phase='eligibility')
 with (out/'rows.jsonl').open('w') as stdout,(out/'inventory.log').open('w') as stderr:
  done=subprocess.run([str(r/'scripts/memcap.sh'),'lake','env','lean','--run',str(e/'memory-cfg-captured-inventory-v1.lean'),str(e/'memory-captured-inventory-current/sources.txt')],cwd=r,env=env,stdout=stdout,stderr=stderr)
 assert done.returncode==0,('inventory',done.returncode)
 rows=[json.loads(line) for line in (out/'rows.jsonl').read_text().splitlines() if line.startswith('{')];accepted=[x for x in rows if x['checked_stock_memory']]
 assert accepted,'No captured inputs passed'
 for i,row in enumerate(accepted):
  for cleanup in [False,True]:
   label=str(i)+('-cleanup' if cleanup else '-plain');obj=out/(label+'.o');save('running',phase=label)
   args=[str(r/'scripts/memcap.sh'),str(r/'.lake/build/bin/lean-backend'),row['path'],str(obj),'--regalloc','regalloc2',*([] if cleanup else ['--no-dead-cleanup'])]
   with (out/(label+'.log')).open('w') as log:done=subprocess.run(args,cwd=r,env=env,stdout=log,stderr=subprocess.STDOUT)
   text=(out/(label+'.log')).read_text();assert done.returncode==0 and obj.exists() and obj.stat().st_size>0 and 'unsupported:' not in text,(label,text)
   records.append(dict(path=row['path'],function=row['function'],cleanup=cleanup,source_sha256=digest(row['path']),object_sha256=digest(obj)))
 assert len(rows)==len(expected) and all(digest(p)==h for p,h in expected.items())
 save('passed',sources=len(rows),eligible=sum(x['eligible'] for x in rows),source_ok=sum(x['source_ok'] for x in rows),checked=len(accepted),functions=sorted({x['function'] for x in accepted}),source_hashes_exact=True,source_base='current main8a70 plus pending775 b6cdec54; landing remains necessary')
except BaseException as error:save('failed',error=repr(error));raise
