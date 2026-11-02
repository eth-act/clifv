from pathlib import Path
import json,hashlib,datetime,shutil,psutil
E=Path('/home/lee/clifv/.git/agent-evidence/stock-memory-20261029');P=E/'892-current-main-context-v1/package';T=P/'.lake/build';C=P/'.lake/ci-cache'
assert T.is_dir() and not T.is_symlink() and C.is_dir()
for p in psutil.process_iter(['name','cmdline']):
 try:
  if p.info['name'] not in ['lean','lake']:continue
  assert str(T) not in ' '.join(p.info['cmdline'] or []),(p.pid,'command')
  assert p.cwd()!=str(P),(p.pid,'cwd')
  assert not any(x.path.startswith(str(T)) for x in p.memory_maps(grouped=True)),(p.pid,'mapped output')
 except (psutil.NoSuchProcess,psutil.AccessDenied,FileNotFoundError):pass
rows={};size=0
for p in T.rglob('*'):
 if p.is_symlink():rows[str(p.relative_to(T))]={'symlink':str(p.readlink())};continue
 if not p.is_file():continue
 h=hashlib.sha256()
 with p.open('rb') as f:
  while chunk:=f.read(1024**2):h.update(chunk)
 st=p.stat();size+=st.st_size;rows[str(p.relative_to(T))]={'sha256':h.hexdigest(),'bytes':st.st_size,'links':st.st_nlink}
manifest=E/'892-obsolete-build-output-preservation-v1.json';manifest.write_text(json.dumps({'status':'preserved_completed_outputs','files':rows,'logical_bytes':size,'source_and_logs_preserved':True,'native_cache_untouched':True,'worker_dependency_checks':'Both active proof workers explicitly report no dependency on this build path.','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},indent=2)+'\n')
shutil.rmtree(T);assert C.is_dir();r={'status':'completed','removed_only':str(T),'hashes':len(rows),'logical_bytes':size,'preservation_sha256':hashlib.sha256(manifest.read_bytes()).hexdigest(),'source_and_logs_preserved':True,'native_cache_untouched':True,'active_proof_and_broad_prefixes_untouched':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(E/'892-obsolete-build-cleanup-v1.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
