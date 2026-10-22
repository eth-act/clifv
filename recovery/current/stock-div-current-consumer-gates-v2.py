from pathlib import Path
import json,os,subprocess,re,time,concurrent.futures,datetime
normal=Path('/tmp/stock-div-reconciled-current-normal-author/receipt.json')
while not normal.exists():
 if not Path('/proc/'+str(json.load(open('/tmp/stock-div-current-normal-worker-pid.json'))['pid'])+'/cmdline').exists():raise SystemExit('Current normal worker ended without receipt; inspect current-final-pr-build/normal logs')
 time.sleep(1)
a=json.load(open(normal));assert a['state']=='passed',a['state']
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();assert a['head']==head
E=os.environ.copy();E.update(json.load(open('/tmp/stock-div-release-env.json')));E['FV_MEMCAP']='8G'
# Observe the exact fact in the checked audit. Never admit a fact by broad pattern.
old=json.load(open('/tmp/stock-div-owned/partitions.json'));out=Path('/tmp/stock-div-current-owned');out.mkdir(exist_ok=True)
log=Path('/tmp/stock-div-current-affected-audits/stock-div-production.log').read_text();facts=set(re.findall(r'Link\.LinkSpec\.reachOkMap_duplicates\._native\.native_decide\.ax_[\w]+',log));assert len(facts)==1,facts
core=old['core']+['FV.Link.ReachCheck','FV.Link.ReachCheckEq'];witnesses=old['witnesses']+['FV.Link.ReachCheckWitness'];allowed=sorted(set(old['exact_native_facts'])|facts);part={**old,'base':json.load(open('/tmp/stock-div-current-base.json'))['base'],'candidate':head,'core':core,'witnesses':witnesses,'exact_native_facts':allowed};(out/'partitions.json').write_text(json.dumps(part,indent=2)+'\n')
s=Path('/tmp/stock-div-owned/Owned0.lean').read_text();s=s[s.index('open Lean Elab Command'):];arr=lambda xs:'#['+', '.join(json.dumps(x) for x in xs)+']'
for name,values in [('core',core),('witnesses',witnesses),('fixedFacts',allowed)]:s=re.sub(r'  let '+name+r' := #\[.*\]',lambda _: '  let '+name+' := '+arr(values),s)
(out/'Owned0.lean').write_text(''.join('import '+n+'\n' for n in core+witnesses)+s)
for i in range(1,len(part['executable_owners'])+1):(out/f'Owned{i}.lean').write_text(Path('/tmp/stock-div-owned',f'Owned{i}.lean').read_text())
m=json.load(open('/tmp/stock-div-current-normal-manifest.json'));m['packet']='div-current-owned';m['gates']=[{'id':'owned-'+str(i),'argv':['lake','env','lean',str(out/f'Owned{i}.lean')],'requires':['STOCK_DIV_OWNED'],'complete_inputs':False} for i in range(len(part['executable_owners'])+1)];Path('/tmp/stock-div-current-owned-manifest.json').write_text(json.dumps(m,indent=2)+'\n')
m=json.load(open('/tmp/stock-div-release-native-manifest.json'));m['candidate']=head;m['base']=part['base'];m['env'].update(E);m['packet']='div-current-native';Path('/tmp/stock-div-current-native-manifest.json').write_text(json.dumps(m,indent=2)+'\n')
print('Starting final actual consumer gates on',head,'ownership',len(core),len(witnesses),len(allowed),flush=True)
def chain(names):
 records=[]
 for name in names:
  r=subprocess.run(['python3','/tmp/stock-div-run-gates.py',name],env=E);records.append({'kind':name,'returncode':r.returncode})
  if r.returncode:break
 return records
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 jobs=[pool.submit(chain,['current-full']),pool.submit(chain,['current-native','current-integration','current-highmul-integration','current-retention','current-owned'])];records=[f.result() for f in jobs]
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'head':head,'records':records,'state':'passed' if len(records[0])==1 and len(records[1])==5 and all(x['returncode']==0 for row in records for x in row) else 'failed'};Path('/tmp/stock-div-current-all-gates-status.json').write_text(json.dumps(result,indent=2)+'\n');print(result,flush=True);raise SystemExit(0 if result['state']=='passed' else 1)
