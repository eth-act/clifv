"""Fill missing canonical files only after the coordinator releases the existing package."""
from pathlib import Path
import argparse,json,hashlib,subprocess,os
from preflight import OUT,PLAN,release_check,blob,sha
p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--release',required=True);a=p.parse_args();root,release=release_check(a.root,a.release);assert release['allow_materialize_existing_snapshot'] is True
prior=json.loads((OUT.parent/'892-joint-current-context-v2/context.json').read_text());assert all(sha(root/rel)==h for rel,h in prior['source_hashes'].items()),'Preserve the reviewed current source boundary'
allowed={'LEARNINGS.md','scripts/lake-serial-build.py'};written=[]
for rel,wanted in PLAN['all_source_blobs'].items():
 dest=root/rel
 if rel=='lakefile.toml':assert sha(dest)==release['operational_lakefile_sha256'];continue
 if dest.exists() or dest.is_symlink():
  if blob(dest)==wanted:continue
  assert rel in allowed,('Preserve unexpected existing source',rel)
  if rel=='scripts/lake-serial-build.py':assert sha(dest)==release['operational_scheduler_sha256']
  old=OUT/'materialization-preimages'/rel;old.parent.mkdir(parents=True,exist_ok=True);old.write_bytes(dest.read_bytes());dest.unlink()
 data=subprocess.check_output(['git','cat-file','blob',wanted],cwd='/home/lee/clifv');dest.parent.mkdir(parents=True,exist_ok=True)
 if PLAN['source_modes'][rel]=='120000':dest.symlink_to(data.decode())
 else:dest.write_bytes(data);dest.chmod(0o755 if PLAN['source_modes'][rel]=='100755' else 0o644)
 assert blob(dest)==wanted;written.append(rel)
# Reuse the existing pinned upstream checkouts. These are source links, not new worktrees.
for item in release['external_source_links']:
 dest=root/item['relative_path'];target=Path(item['existing_source']).resolve();assert target.exists()
 actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=target,text=True).strip();assert actual==item['commit']
 if dest.exists() or dest.is_symlink():assert dest.resolve()==target
 else:dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(target,target_is_directory=True)
(OUT/'materialization-receipt.json').write_text(json.dumps({'status':'passed','candidate_tree':PLAN['combined_tree'],'written_files':written,'new_view':False,'new_cache':False,'existing_normal_outputs_preserved':True},indent=2)+'\n');print('MATERIALIZED MISSING CANONICAL FILES',len(written))
