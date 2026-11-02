from pathlib import Path
import os,json,subprocess,hashlib,datetime,tarfile,io
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ');out=Path('/tmp/stock-outcome-recovery-'+stamp);out.mkdir();files={}
for directory in ['stock-div-next-staged','stock-outcome-normal','stock-outcome-main-repair','stock-outcome-interface-audits','stock-outcome-independent','stock-outcome-independent-light','stock-outcome-independent-bounded','stock-div-mixed-source-check','stock-div-mixed-import-check-renamed','stock-outcome-value-interface-check','stock-mixed-div-domain-normal','stock-mixed-div-witness-normal','stock-mixed-div-witness-normal-retry1','stock-mixed-div-checks-normal','stock-mixed-div-direct-main-normal']:
 root=Path('/tmp')/directory
 for p in root.rglob('*'):
  if p.is_file():files[directory+'/'+str(p.relative_to(root))]=p
for pattern in ['stock-outcome-*.json','stock-outcome-*.py','stock-outcome-*.md','stock-outcome-*.txt','stock-outcome-*.log','stock-div-next-*.py','stock-div-next-*.json','stock-mixed-div-prepare-owned.py','stock-empty-args-adapter-investigation.md','stock-div-current-status.md','stock-mixed-div-*.json','stock-mixed-div-*.py','stock-mixed-div-*.log','stock-mixed-div-*.md']:
 for p in Path('/tmp').glob(pattern):
  if p.is_file():files['state/'+p.name]=p
manifest={'source_head':head,'utc':stamp,'state':'partial evidence; normal build running, not a completed validation claim','mixed_class':'staged only; full production compile/validation pending','files':{}}
archive=out/'recovery.tar.gz'
with tarfile.open(archive,'w:gz') as tar:
 for name,p in sorted(files.items()):
  b=p.read_bytes();manifest['files'][name]={'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)};info=tarfile.TarInfo(name);info.size=len(b);tar.addfile(info,io.BytesIO(b))
 b=json.dumps(manifest,indent=2).encode();info=tarfile.TarInfo('manifest.json');info.size=len(b);tar.addfile(info,io.BytesIO(b))
E=os.environ.copy();E['GIT_INDEX_FILE']=str(out/'index');subprocess.run(['git','read-tree',head],env=E,check=True);blob=subprocess.check_output(['git','hash-object','-w',str(archive)],text=True).strip();subprocess.run(['git','update-index','--add','--cacheinfo','100644',blob,'evidence/outcome-and-mixed-recovery.tar.gz'],env=E,check=True);tree=subprocess.check_output(['git','write-tree'],env=E,text=True).strip();commit=subprocess.check_output(['git','commit-tree',tree,'-p',head],input=b'Back up outcome-interface partial evidence and complete staged mixed-div source\n').decode().strip();branch='agent/stock-outcome-recovery-'+stamp;subprocess.run(['git','update-ref','refs/heads/'+branch,commit],check=True);subprocess.run(['git','push','origin',commit+':refs/heads/'+branch],check=True);remote=subprocess.check_output(['git','ls-remote','origin','refs/heads/'+branch],text=True).split()[0];assert remote==commit
r={'state':'remote_verified','source_head':head,'backup_commit':commit,'branch':branch,'archive':str(archive),'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'bytes':archive.stat().st_size,'files':len(files),'scope':manifest['state']};Path('/tmp/stock-outcome-recovery-backup.json').write_text(json.dumps(r,indent=2)+'\n');(out/'index').unlink();print(json.dumps(r))
