"""Guard the one existing owned source package. Never mutate it."""
from pathlib import Path
import json,hashlib,os,psutil,stat
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
 assert release['released_owners']==PLAN['required_release_owners']
 for owner in PLAN['required_release_owners']:
  try:
   proc=psutil.Process(owner['pid']);assert proc.create_time()!=owner['create_time'] or proc.status()==psutil.STATUS_ZOMBIE,('Actual current owner still runs',owner)
  except psutil.NoSuchProcess:pass
 normal_path=Path(release['normal_provider_receipt']);assert sha(normal_path)==release['normal_provider_receipt_sha256']
 normal=json.loads(normal_path.read_text());assert normal['status']=='passed' and normal['joint_tree']==PLAN['source_context_tree'];assert normal['normal_project_targets']==2895 and normal['authoritative_final_no_build_exit']==0
 wrapper_path=Path(release['provider_wrapper_receipt']);assert sha(wrapper_path)==release['provider_wrapper_receipt_sha256']
 wrapper=json.loads(wrapper_path.read_text());assert wrapper['status']=='passed' and wrapper['normal_provider_receipt_sha256']==sha(normal_path)
 consumer_path=Path(release['actual_consumer_receipt']);assert sha(consumer_path)==release['actual_consumer_receipt_sha256']
 consumer=json.loads(consumer_path.read_text());assert consumer['status']=='passed' and consumer['head892']==PLAN['validated_head892'] and consumer['tree892']==PLAN['validated_tree892'];assert consumer['provider_receipt_sha256']==sha(wrapper_path)
 assert consumer['actual_backend_object_comparisons']==6 and consumer['actual_complete_bundles']==6 and consumer['actual_additional_typed_compiler_modes']==2 and consumer['actual_generated_roots']==68
 bridge_path=Path(release['source_projection_bridge_receipt']);assert sha(bridge_path)==release['source_projection_bridge_receipt_sha256']
 bridge=json.loads(bridge_path.read_text());assert bridge['status']=='passed' and bridge['current_tree']==PLAN['combined_tree']
 assert bridge['actual_892_merged_commit']==PLAN['actual_892_merged_commit'] and bridge['actual_892_head']==PLAN['head892']
 assert bridge['validated85_head']==consumer['head892'] and bridge['validated85_tree']==consumer['tree892']
 assert bridge['normal_provider_receipt_sha256']==sha(normal_path) and bridge['all_validated_sources_equal_actual_tree'] is True
 assert bridge['all_normal_source_hashes_checked']==len(normal['source_hashes'])
 release_owner=Path(release['actual_owner_release_receipt']);assert sha(release_owner)==release['actual_owner_release_receipt_sha256']
 released=json.loads(release_owner.read_text());assert released['status']=='released_after_actual_normal_and_consumer_success'
 assert released['scheduler']==326832 and released['observer']==456502
 assert released['normal_receipt_sha256']==sha(normal_path) and released['consumer_receipt_sha256']==sha(consumer_path)
 assert sha(PLAN['source_snapshot_manifest'])==release['source_snapshot_manifest_sha256']

 for rel,h in normal['source_hashes'].items():assert sha(root/rel)==h,('Validated normal source changed',rel)
 assert os.statvfs(root).f_bavail*os.statvfs(root).f_frsize>=100*1024**3
 return root,release

def check(root,release_path,stage='combined'):
 assert stage=='combined','This successor validates the current published candidate; old baselines remain separate evidence'
 root,release=release_check(root,release_path)
 for rel,wanted in PLAN['all_source_blobs'].items():
  p=root/rel
  if rel in PLAN['operational_source_overrides']:
   override=PLAN['operational_source_overrides'][rel];assert override['canonical_blob']==wanted and sha(p)==override['sha256'],('Operational source differs',rel)
  else:
   assert p.exists() or p.is_symlink(),('Missing canonical source',rel)
   assert blob(p)==wanted,('Source differs from exact publication snapshot',rel)
  assert p.is_symlink() if PLAN['source_modes'][rel]=='120000' else bool(p.stat().st_mode&stat.S_IXUSR)==(PLAN['source_modes'][rel]=='100755'),('Source mode differs',rel)
 for prefix in ['FV','FVTest','corpus/dsl','crate-proofs']:
  for p in (root/prefix).rglob('*.lean'):
   if '.lake' in p.parts:continue
   assert str(p.relative_to(root)) in PLAN['all_source_blobs'],('Unreviewed generated source in library',p)
 return {'root':str(root),'stage':'combined','tree':PLAN['combined_tree'],'source_context_tree':PLAN['source_context_tree'],'head892':PLAN['head892'],'release_sha256':sha(release_path),'queue_manifest_sha256':sha(OUT/'queue-manifest.json')}
