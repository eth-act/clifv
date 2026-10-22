from pathlib import Path
import os,signal,json,subprocess,shutil,hashlib,datetime
p=479609;cmd=Path(f'/proc/{p}/cmdline').read_bytes().replace(b'\0',b' ').decode();assert 'stock-div-current-final-pr-build' in cmd;os.kill(p,signal.SIGSTOP)
root=Path('/tmp/stock-div-mixed-import-check');root.mkdir(exist_ok=True);shutil.rmtree(root/'FV',ignore_errors=True);staged=Path('/tmp/stock-div-next-staged');parts=json.load(open(staged/'partition.json'))['parts'];E=os.environ.copy();E.update(json.load(open('/tmp/stock-div-release-env.json')));E['FV_MEMCAP']='6G';records=[]
try:
 lp=subprocess.check_output(['scripts/memcap.sh','lake','env','printenv','LEAN_PATH'],env=E,text=True).strip();E['LEAN_PATH']=str(root)+':'+lp
 for x in parts:
  src=staged/x['path'];dest=root/'StockMixedScratch'/src.name;dest.parent.mkdir(parents=True,exist_ok=True);body=src.read_text()
  for part in parts:body=body.replace('import '+part['path'][:-5].replace('/','.'),'import StockMixedScratch.'+Path(part['path']).stem)
  dest.write_text(body);log=root/(dest.stem+'-2.log')
  with log.open('w') as f:r=subprocess.run(['scripts/memcap.sh','lean','--root='+str(root),'-o',str(dest.with_suffix('.olean')),str(dest)],env=E,stdout=f,stderr=subprocess.STDOUT)
  records.append({'module':x['path'],'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'returncode':r.returncode,'log':str(log)});print(dest.stem,r.returncode,flush=True)
  if r.returncode:print(log.read_text()[-2200:]);break
 else:
  src=staged/'scripts/audit/stock-mixed-div-production.lean';body=src.read_text()
  for part in parts:body=body.replace('import '+part['path'][:-5].replace('/','.'),'import StockMixedScratch.'+Path(part['path']).stem)
  src=root/'Review.lean';src.write_text(body);log=root/'all-roots-2.log'
  with log.open('w') as f:r=subprocess.run(['scripts/memcap.sh','lean',str(src)],env=E,stdout=f,stderr=subprocess.STDOUT)
  records.append({'module':'bundled all new roots','returncode':r.returncode,'log':str(log)});print('bundled new roots',r.returncode,flush=True)
finally:
 Path('/tmp/stock-div-next-split-check-2.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'actual_current_head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'scope':'New split proof import validation in separate temporary root, using actual installed import artifacts; production classifier/pipeline witnesses not yet applied or validated. Current main normal-key reconciliation still pending.','records':records},indent=2)+'\n')
 if Path(f'/proc/{p}/cmdline').exists():os.kill(p,signal.SIGCONT)
