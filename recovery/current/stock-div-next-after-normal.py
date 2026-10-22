from pathlib import Path
import json,os,time,subprocess,hashlib,datetime
receipt=Path('/tmp/stock-div-reconciled-main3-normal-author/receipt.json')
while True:
 if receipt.exists():
  try:ready=json.loads(receipt.read_text()).get('state')=='passed'
  except json.JSONDecodeError:ready=False
  if ready:break
 time.sleep(1)
E=os.environ.copy();E.update(json.load(open('/tmp/stock-div-main3-normal-manifest.json'))['env']);E['FV_MEMCAP']='4G';rows=[]
for name in ['entry-trap','quiet-record','record-uniqueness']:
 src=Path('/tmp/stock-div-next-'+name+'.lean');log=Path('/tmp/stock-div-next-'+name+'-main3-current.log')
 with log.open('w') as f:p=subprocess.run(['scripts/memcap.sh','lake','env','lean',str(src)],env=E,stdout=f,stderr=subprocess.STDOUT)
 rows.append({'name':name,'returncode':p.returncode,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'log':str(log),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()});print(name,p.returncode,flush=True)
Path('/tmp/stock-div-next-after-normal-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'current_normal_head':json.loads(receipt.read_text())['head'],'records':rows},indent=2))
