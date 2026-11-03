from pathlib import Path
import hashlib,json,os
def restore_config(D):
 data=json.loads((D/'config-restoration.json').read_text());original=(D/'original-G-lakefile.toml').read_bytes();assert hashlib.sha256(original).hexdigest()==data['original_sha256'];path=Path(data['G'])/'lakefile.toml';current=path.read_bytes();projected=original.replace(b'weakLeanArgs = [',b'weakLeanArgs = ["-j1",',1);assert current in [original,projected],('Unexpected G config; preserve it',str(path))
 if current!=original:
  tmp=path.with_name(path.name+'.IselCtlTryF-restore');tmp.write_bytes(original);os.replace(tmp,path)
 assert path.read_bytes()==original
 return {'original_config_restored':True,'original_sha256':data['original_sha256'],'changed':current!=original}
