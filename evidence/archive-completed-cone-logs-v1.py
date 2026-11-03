from pathlib import Path
import os,hashlib,json,gzip,tarfile,datetime
os.nice(10)
E=Path('/home/lee/clifv/.git/agent-evidence/stock-memory-20261029');D=E/'general7-remaining29-conditional-broad-12g-v1'
assert json.loads((D/'state.json').read_text())['same_controller_resumed']
assert json.loads((D/'receipt.json').read_text())['status']=='passed-conditional-cone-and-complete1657'
files=sorted(p for p in D.rglob('*.log') if p.is_file() and not p.is_symlink() and '.lake' not in p.parts)
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as stream:
  for chunk in iter(lambda:stream.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
catalogue={str(p.relative_to(D)):{'sha256':digest(p),'bytes':p.stat().st_size} for p in files}
assert all('author-env' not in n for n in catalogue)
archive=D/'logs-curated-v1.tar.gz';assert not archive.exists();temp=archive.with_suffix('.gz.tmp')
with temp.open('wb') as raw:
 with gzip.GzipFile(filename='',mode='wb',fileobj=raw,compresslevel=1,mtime=0) as compressed:
  with tarfile.open(fileobj=compressed,mode='w|') as tar:
   for p in files:
    name=str(p.relative_to(D));info=tar.gettarinfo(str(p),arcname=name);info.mtime=0;info.uid=info.gid=0;info.uname=info.gname='';info.mode=0o600
    with p.open('rb') as source:tar.addfile(info,source)
seen=set()
with tarfile.open(temp,mode='r|gz') as tar:
 for member in tar:
  assert member.isfile() and member.name in catalogue and member.name not in seen
  data=tar.extractfile(member);assert data is not None;h=hashlib.sha256();count=0
  for chunk in iter(lambda:data.read(1024*1024),b''):h.update(chunk);count+=len(chunk)
  assert {'sha256':h.hexdigest(),'bytes':count}==catalogue[member.name],member.name;seen.add(member.name)
assert seen==set(catalogue)
for p in files:assert digest(p)==catalogue[str(p.relative_to(D))]['sha256']
os.replace(temp,archive)
r={'status':'ALL_DECOMPRESSED_LOG_HASHES_EXACT','archive':str(archive),'archive_sha256':digest(archive),'compressed_bytes':archive.stat().st_size,'raw_bytes':sum(x['bytes'] for x in catalogue.values()),'files':catalogue,'compression':'single-thread gzip level1, nice10, 1GiB cap','no_build_cache_or_credentials':True,'raw_logs_removed':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(D/'logs-archive-v1.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:r[k] for k in ['status','archive_sha256','compressed_bytes','raw_bytes']}),flush=True)
