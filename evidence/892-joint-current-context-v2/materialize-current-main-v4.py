from pathlib import Path
import json,hashlib,subprocess,psutil,datetime
O=Path(__file__).resolve().parent;M=O/'current-main-migration-v4';C=json.loads((M/'context.json').read_text());OLD=json.loads((M/'old-context.json').read_text());P=Path(C['package']);R=Path('/home/lee/clifv');boundary=json.loads((O/'current-main-migration-boundary-v1.json').read_text());assert boundary['status']=='old_owner_released_pending_current_materialization'
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=R)
for x in psutil.process_iter(['pid','name']):
 if x.info['name'] in ['lean','lake','lake.orig']:
  try:assert Path(x.cwd())!=P.resolve(),('Unexpected active package reader/writer',x.pid)
  except (psutil.NoSuchProcess,psutil.AccessDenied):pass
for rel,h in OLD['source_hashes'].items():assert sha(P/rel)==h,('Old package source changed unexpectedly',rel)
outputs={}
for f in (P/'.lake/build/lib/lean').rglob('*'):
 if f.is_file() and (f.name.endswith('.trace') or f.name.endswith('.olean')):outputs[str(f.relative_to(P))]={'sha256':sha(f),'bytes':f.stat().st_size}
(M/'preserved-old-normal-output-hashes.json').write_text(json.dumps(outputs,indent=2)+'\n')
changes=git('diff','--name-status',OLD['joint_tree'],C['joint_tree']).decode().splitlines();changed=[]
for line in changes:
 status,rel=line.split('\t');assert status in ['A','M'],('Unexpected deletion/rename',line)
 data=git('show',C['joint_tree']+':'+rel);target=P/rel;before=None
 if target.exists():
  before=target.read_bytes();old=git('show',OLD['joint_tree']+':'+rel);assert before==old,('Preserve unknown preexisting source',rel)
  h=M/'source-preimages'/rel;h.parent.mkdir(parents=True,exist_ok=True);h.write_bytes(before)
  target.unlink()
 target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data);newhash=hashlib.sha256(data).hexdigest();C['source_hashes'][rel]=newhash
 changed.append({'status':status,'path':rel,'old_sha256':hashlib.sha256(before).hexdigest() if before is not None else None,'new_sha256':newhash})
configs={}
for name in ['lakefile.toml','lake-manifest.json','lean-toolchain']:
 target=P/name;old=target.read_bytes();canonical=git('show',C['base']+':'+name);operational=canonical
 if name=='lakefile.toml':operational=canonical.replace(b'weakLeanArgs = [',b'weakLeanArgs = ["-j2",',1)
 assert name!='lean-toolchain' or old==canonical,'Pinned Lean changed; stop'
 for label,data in [('old-operational',old),('new-canonical',canonical),('new-operational',operational)]:
  f=M/(label+'-'+name);f.write_bytes(data)
 if old!=operational:target.unlink();target.write_bytes(operational)
 configs[name]={'old_operational_sha256':hashlib.sha256(old).hexdigest(),'new_canonical_sha256':hashlib.sha256(canonical).hexdigest(),'new_operational_sha256':hashlib.sha256(operational).hexdigest()}
C.update(status='materialized_current_main_and_canonical_production',additional_current_A_changes=changed)
(O/'context-before-current-main-migration-v4.json').write_bytes((O/'context.json').read_bytes());(O/'context.json').write_text(json.dumps(C,indent=2)+'\n');(O/'normal-provider-targets-before-migration-v4.txt').write_bytes((O/'normal-provider-targets.txt').read_bytes());(O/'normal-provider-targets.txt').write_bytes((M/'normal-provider-targets.txt').read_bytes())
boundary.update(status='materialized_current_main_and_canonical_production',new_joint_tree=C['joint_tree'],actual_main=C['base'],configs=configs,changed_sources=changed,preserved_normal_artifacts=len(outputs),utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(O/'current-main-migration-boundary-v1.json').write_text(json.dumps(boundary,indent=2)+'\n')
(O/'publication-binding-v4-prospective.json').write_text(json.dumps({'status':'awaiting_coordinator_exact_head','actual_base':C['base'],'candidate_tree':C['joint_tree'],'canonical18_unchanged':True,'full_goal_complete':False},indent=2)+'\n')
print(json.dumps({'status':'materialized','base':C['base'],'tree':C['joint_tree'],'project_target_modules':C['project_modules'],'current_A_changed_paths':len(changed),'normal_artifacts_preserved':len(outputs),'shared_source_changed':[p for p in C['new_source_changes']]}))
