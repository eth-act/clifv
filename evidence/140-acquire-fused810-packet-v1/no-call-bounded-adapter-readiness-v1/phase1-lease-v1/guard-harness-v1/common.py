from pathlib import Path
import datetime,json,os,psutil,time
D=Path(__file__).resolve().parent
O=D.parent
E=O.parent.parent
F=E/'140-fence-packet-v1/package'
def save(path,value):
 tmp=path.with_name(path.name+'.tmp-'+str(os.getpid()));tmp.write_text(json.dumps(value,indent=2)+'\n');os.replace(tmp,path)
def live(pid,birth):
 try:
  p=psutil.Process(pid);return p.create_time()==birth and p.status()!=psutil.STATUS_ZOMBIE
 except(psutil.NoSuchProcess,psutil.AccessDenied):return False
def busy(state):
 p=D/'consumer-identity.json'
 if p.exists():
  c=json.loads(p.read_text())
  if live(c['pid'],c['birth']):return True
 for path in Path(state['scope_parent']).glob('worker-o-acquire-phase1-v1-*.scope/cgroup.procs'):
  try:
   if path.read_text().strip():return True
  except FileNotFoundError:pass
 for p in psutil.process_iter(['name','status','cmdline']):
  try:
   if p.info['status']!='zombie' and p.info['name'] in ['lean','lake','leantar'] and (p.cwd()==str(F) or any(str(F) in a for a in p.info['cmdline']or[])):return True
  except(psutil.NoSuchProcess,psutil.AccessDenied):pass
 return False
def restore(reason):
 data={'status':'restored','source_GiB':2,'acquire_GiB':1,'reason':reason,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 tmp=D/('shares-restored.tmp-'+str(os.getpid()));tmp.write_text(json.dumps(data,indent=2)+'\n')
 try:os.link(tmp,D/'shares-restored.json')
 except FileExistsError:pass
 finally:tmp.unlink()
