from pathlib import Path
import json,hashlib,subprocess,shutil
O=Path(__file__).resolve().parent;C=json.loads((O/'context.json').read_text());P=Path(C['package']);R=Path('/home/lee/clifv');base='3d8e0c5d25e4f0849f76670b1fd492e8eb2cadae'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
config=P/'lakefile.toml';old=config.read_text();assert 'weakLeanArgs = [' in old
(O/'canonical-lakefile-before-scheduling-j2.toml').write_text(old)
new=old.replace('weakLeanArgs = [','weakLeanArgs = ["-j2",',1);config.write_text(new)
for name in ['memcap.sh','lake-serial-build.py','lake-module-peaks.tsv']:
 path=P/'scripts'/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(subprocess.check_output(['git','show',base+':scripts/'+name],cwd=R))
 if name.endswith(('.sh','.py')):path.chmod(0o755)
modules=[p[:-5].replace('/','.') for p in C['full_project_queue']];(O/'normal-provider-targets.txt').write_text('\n'.join(modules)+'\n')
r={'joint_tree':C['joint_tree'],'head892':'a455465225905aba9f3247e5a565ac90dbdb1a6a','project_sources':C['source_hashes'],'canonical_lakefile_sha256':hashlib.sha256(old.encode()).hexdigest(),'operational_lakefile_sha256':sha(config),'operational_difference':'Append-j2only to weakLeanArgs; Module.presetup adds mod.leanArgs to trace at Module.lean:613, excludes weakLeanArgs; buildLean uses both at984','cache':'Existing package-local CI staging cache only; no global mapping writes or newwarmcache','normal_targets':len(modules),'resource':'12GiB onejob; all Leanexplicit-j2; OMP2','raw_passes_preserved':True,'normal_recompile':'Only actual Lake normal-key requirements determine repeats; no fabricated traces'}
(O/'normal-handoff-source-binding-v1.json').write_text(json.dumps(r,indent=2)+'\n');print('Normal-key source binding prepared',len(modules))
