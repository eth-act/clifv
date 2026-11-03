from pathlib import Path
import hashlib,json,os,shutil,tempfile
D=Path(__file__).resolve().parent
R=D.parent/'direct-call-store-live-packet-v1/validation-package-v1'
def restore():
 expected=json.loads((D/'prepared-inputs.json').read_text())['configs'];changed=[]
 for name,h in expected.items():
  original=D/'canonical-configs'/name
  assert hashlib.sha256(original.read_bytes()).hexdigest()==h
  dest=R/name;assert dest.parent.resolve()==R.resolve() and dest.parent.stat().st_uid==os.getuid()
  if dest.read_bytes()!=original.read_bytes():
   fd,tmp=tempfile.mkstemp(prefix='.old23-config-',dir=dest.parent);os.close(fd)
   try:
    shutil.copyfile(original,tmp);os.replace(tmp,dest)
   finally:
    if Path(tmp).exists():Path(tmp).unlink()
   changed.append(name)
  assert dest.read_bytes()==original.read_bytes()
 return {'restored':changed,'all_canonical_bytes_match':True}
