from pathlib import Path
import json,subprocess,time,datetime,os
root=Path('/home/lee/clifv/.worktrees/stock-cfg-source-20261025');os.chdir(root)
head='52b22dc9e1cb4329ec160ade0f2e12a4312f2d51'
progress=Path('/tmp/stock-memory-reconciled-validation-queue-v1.json');records=[]
def save(state):progress.write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),head=head,state=state,records=records),indent=2)+'\n')
def frozen():
 assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()==head
 assert not subprocess.check_output(['git','status','--porcelain'],text=True).strip()
frozen();save('waiting-for-normal-tools-trust')
r=Path('/tmp/stock-memory-reconciled-normal-gates-v1/receipt.json')
while not r.exists():time.sleep(10)
assert json.loads(r.read_text())['state']=='passed','Normal/tools/trust failed; inspect before further gates'
items=[('full','/tmp/stock-memory-production-full-manifest-v1.json'),('memory','/tmp/stock-memory-production-integration-manifest-v3.json')]
items += [(kind,f'/tmp/stock-memory-retained-{kind}-manifest-v2.json') for kind in ['conditional','forward','linear','scalar-entry','entry','cfg']]
for label,old in items:
 frozen();m=json.loads(Path(old).read_text());m['candidate']=head;m['base']='2dafec2e';m['packet']='stock-memory-reconciled-'+label
 m['env']['FV_MEMCAP']='8G'
 if label=='memory':
  for g in m['gates']:g['argv']=[x.replace('/tmp/stock-memory-production-integration-v3','/tmp/stock-memory-reconciled-integration-v1') for x in g['argv']]
 # Inputs are collected after normal build; binaries and their complete current
 # transitive Lean artifacts are hashed in the new run, not reused from3753.
 m['inputs']=[str(p) for p in (root/'.lake/build/lib/lean').rglob('*.olean')]
 manifest=Path(f'/tmp/stock-memory-reconciled-{label}-manifest-v1.json');manifest.write_text(json.dumps(m,indent=2)+'\n')
 out=Path(f'/tmp/stock-memory-reconciled-{label}-gates-v1')
 record=dict(label=label,state='running',started=datetime.datetime.now(datetime.timezone.utc).isoformat());records.append(record);save('running');print('START',label,flush=True)
 with Path(f'/tmp/stock-memory-reconciled-{label}-runner-v1.log').open('w') as log:
  p=subprocess.run(['taskset','-c','0,1','nice','-n','10','python3','scripts/stock-delivery-gates.py','run',str(manifest),'--root',str(root),'--out',str(out)],stdout=log,stderr=subprocess.STDOUT)
 record.update(state='passed' if p.returncode==0 else 'failed',returncode=p.returncode,ended=datetime.datetime.now(datetime.timezone.utc).isoformat());save(record['state']);print('END',label,record['state'],flush=True)
 if p.returncode:raise SystemExit('Gate failed; queue held for inspection')
save('passed');print('ALL_RECONCILED_GATES_PASS',flush=True)
