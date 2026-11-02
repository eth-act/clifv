"""Guard the one existing owned source package. Never mutate it."""
from pathlib import Path
import json,hashlib,os,psutil
OUT=Path(__file__).resolve().parent;PLAN=json.loads((OUT/'snapshot-plan.json').read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def blob(p):
 p=Path(p)
 if p.is_symlink():data=os.readlink(p).encode()
 else:data=p.read_bytes()
 return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
def release_check(root,release_path):
 root=Path(root).resolve();assert root==Path(PLAN['existing_snapshot']).resolve(),'Reuse the same owned package'
 release=json.loads(Path(release_path).read_text());assert release['owner']=='worker-O execution coordinator';assert release['candidate_tree']==PLAN['combined_tree'];assert release['view']==str(root);assert release['allow_shared_full_gate'] is True;assert release['resource_budget']=='12G/max1; O aggregate16G'
 manifest=OUT/'queue-manifest.json';assert release['reviewed_queue_manifest_sha256']==sha(manifest)
 for rel,h in json.loads(manifest.read_text())['files'].items():assert sha(OUT/rel)==h,('Queue changed after review',rel)
 backup=Path(release['backup_receipt']);assert release['remote_backup_verified'] is True and sha(backup)==release['backup_receipt_sha256']
 owner=release['released_provider_owner'];assert owner['pid']==PLAN['active_owner_to_release']
 try:
  p=psutil.Process(owner['pid']);assert p.create_time()!=owner['create_time'] or p.status()==psutil.STATUS_ZOMBIE,'Current normal/consumer owner still runs'
 except psutil.NoSuchProcess:pass
 assert release['normal_and_consumer_receipts_reviewed'] is True
 assert os.statvfs(root).f_bavail*os.statvfs(root).f_frsize>=100*1024**3
 return root,release

def check(root,release_path,stage='combined'):
 assert stage=='combined','This successor validates the current published candidate; old baselines remain separate evidence'
 root,release=release_check(root,release_path)
 for rel,wanted in PLAN['all_source_blobs'].items():
  p=root/rel
  if rel=='lakefile.toml':assert sha(p)==release['operational_lakefile_sha256'];continue
  assert p.exists() or p.is_symlink(),('Missing canonical source',rel)
  assert blob(p)==wanted,('Source differs from exact publication snapshot',rel)
 for prefix in ['FV','FVTest','corpus/dsl','crate-proofs']:
  for p in (root/prefix).rglob('*.lean'):
   if '.lake' in p.parts:continue
   assert str(p.relative_to(root)) in PLAN['all_source_blobs'],('Unreviewed generated source in library',p)
 return {'root':str(root),'stage':'combined','tree':PLAN['combined_tree'],'source_context_tree':PLAN['source_context_tree'],'head892':PLAN['head892'],'release_sha256':sha(release_path),'queue_manifest_sha256':sha(OUT/'queue-manifest.json')}
