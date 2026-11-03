from pathlib import Path
import hashlib,json,tempfile
from preflight import verify_files
with tempfile.TemporaryDirectory()as name:
 root=Path(name);p=root/'A.lean';p.write_text('theorem ok : True := True.intro\n');raw=p.read_bytes();h=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
 verify_files(root,{'A.lean':h},{'A.lean':'100644'},{})
 p.write_text('changed\n')
 try:verify_files(root,{'A.lean':h},{'A.lean':'100644'},{})
 except AssertionError:pass
 else:raise AssertionError('Altered source was accepted')
 p.write_bytes(raw)
 try:verify_files(root,{'A.lean':'0'*40},{'A.lean':'100644'},{})
 except AssertionError:pass
 else:raise AssertionError('Altered manifest was accepted')
print('Original source accepted; source and manifest mutations rejected')
