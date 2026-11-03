from pathlib import Path
import hashlib,json,os,psutil,stat,subprocess
OUT=Path(__file__).resolve().parent;PLAN=json.loads((OUT/'snapshot-plan.json').read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def blob(p):
 p=Path(p);data=os.readlink(p).encode()if p.is_symlink()else p.read_bytes()
 return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
def verify_files(root,blobs,modes,overrides):
 root=Path(root)
 for rel,wanted in blobs.items():
  p=root/rel;assert p.exists()or p.is_symlink(),('Missing canonical source',rel)
  if rel in overrides:
   o=overrides[rel];assert o['canonical_blob']==wanted and sha(p)==o['sha256'],('Operational source changed',rel)
  else:assert blob(p)==wanted,('Source differs from exact target',rel)
  assert p.is_symlink()if modes[rel]=='120000'else bool(p.stat().st_mode&stat.S_IXUSR)==(modes[rel]=='100755'),('Source mode changed',rel)
def check(root,release_path,stage='combined'):
 root=Path(root).resolve();assert root==Path(PLAN['existing_snapshot']).resolve()and stage=='combined'
 r=json.loads(Path(release_path).read_text());assert r['owner']=='worker-O execution coordinator'and r['allow_shared_full_gate']is True
 assert r['revision']==PLAN['target_revision']and r['tree']==PLAN['combined_tree']and r['view']==str(root)
 assert r['resource_budget']=='12G/max2; O aggregate16G'
 q=OUT/'queue-manifest.json';assert sha(q)==r['reviewed_queue_manifest_sha256']
 for rel,h in json.loads(q.read_text())['files'].items():assert sha(OUT/rel)==h,('Reviewed queue changed',rel)
 b=Path(r['backup_receipt']);assert sha(b)==r['backup_receipt_sha256']and json.loads(b.read_text())['remote_verified']
 for owner in r['released_broad_owners']:
  try:p=psutil.Process(owner['pid']);assert p.create_time()!=owner['birth']or p.status()==psutil.STATUS_ZOMBIE,('Old broad owner lives',owner)
  except psutil.NoSuchProcess:pass
 repo=Path(PLAN['source_repository'])
 tree=subprocess.check_output(['git','rev-parse',PLAN['target_revision']+'^{tree}'],cwd=repo,text=True).strip();assert tree==PLAN['combined_tree']
 actual={}
 for row in subprocess.check_output(['git','ls-tree','-rz',tree],cwd=repo).split(b'\0'):
  if row:
   meta,name=row.split(b'\t',1);mode,kind,oid=meta.decode().split()
   if kind=='blob':actual[name.decode()]=oid
 assert actual==PLAN['all_source_blobs'],'Exact repository inventory differs'
 verify_files(root,actual,PLAN['source_modes'],PLAN['operational_source_overrides'])
 for prefix in ['FV','FVTest','Corpus','corpus/dsl','crate-proofs']:
  for p in (root/prefix).rglob('*.lean'):
   if '.lake'not in p.parts:assert str(p.relative_to(root))in actual,('Unreviewed library source',p)
 for x in r['external_sources']:
  path=root/x['relative_path'];assert path.resolve()==Path(x['existing_source']).resolve()
  assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=path,text=True).strip()==x['commit']
 assert os.statvfs(root).f_bavail*os.statvfs(root).f_frsize>=100*1024**3
 return {'root':str(root),'stage':stage,'revision':PLAN['target_revision'],'tree':tree,'head892':PLAN['head892'],'release_sha256':sha(release_path),'queue_manifest_sha256':sha(q),'full_goal_complete':False}
