from pathlib import Path
import json,subprocess,hashlib,shutil,zipfile,datetime,os
O=Path(__file__).resolve().parent;OLD=O.parent/'892-current-main-context-v1';P=OLD/'package';run=41408842551;head='3a6719b44b0e6b38e24cd0de82655f93b78272a9'
group=Path('/proc/self/cgroup').read_text().strip().split('0::')[-1];cg=Path('/sys/fs/cgroup')/group.lstrip('/');assert int((cg/'memory.max').read_text())<=1024**3
os.environ.update(GOMAXPROCS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2')
def api(path):return json.loads(subprocess.check_output(['gh','api',path],text=True))
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
a=api(f'repos/eth-act/clifv/actions/runs/{run}');assert a['head_sha']==head and a['event']=='push'
jobs=api(f'repos/eth-act/clifv/actions/runs/{run}/jobs?per_page=100')['jobs'];arts=api(f'repos/eth-act/clifv/actions/runs/{run}/artifacts?per_page=100')['artifacts'];records=[]
for shard in [2,3,4]:
 name='stage-w1-'+str(shard);producer=[j for j in jobs if j['name']==f'Build wave 1 ({shard}) / shard {shard}'];assert len(producer)==1 and producer[0]['conclusion']=='success'
 matches=[a for a in arts if a['name']==name and not a['expired']];assert len(matches)==1;item=matches[0];assert item['workflow_run']['head_sha']==head and item['size_in_bytes']<=2*1024**3
 assert shutil.disk_usage(P).free>100*1024**3
 stage=P/'.lake/ci-stages'/name;archive=P/'.lake/ci-downloads'/(str(item['id'])+'-late.zip');assert not stage.exists();archive.parent.mkdir(parents=True,exist_ok=True)
 with archive.open('wb') as out:subprocess.run(['gh','api',f'repos/eth-act/clifv/actions/artifacts/{item["id"]}/zip'],stdout=out,check=True)
 digest=sha(archive)
 if item.get('digest','').startswith('sha256:'):assert digest==item['digest'].split(':',1)[1]
 stage.mkdir()
 with zipfile.ZipFile(archive) as bundle:
  assert sum(x.file_size for x in bundle.infolist())<=4*1024**3
  for entry in bundle.infolist():
   dest=stage/entry.filename;assert dest.resolve().is_relative_to(stage.resolve());assert (entry.external_attr>>16)&0o170000!=0o120000
   if entry.is_dir():dest.mkdir(parents=True,exist_ok=True);continue
   dest.parent.mkdir(parents=True,exist_ok=True)
   with bundle.open(entry) as src,dest.open('wb') as out:shutil.copyfileobj(src,out,1048576)
 mappings=list(stage.rglob('outputs.jsonl'));assert mappings
 records.append({'artifact':item,'producer':producer[0],'stage':str(stage),'archive_sha256':digest,'mapping_hashes':{str(m.relative_to(stage)):sha(m) for m in mappings},'unstaged':False,'live_library_writes':False,'live_cache_writes':False})
 archive.unlink();(O/'late-ci-stage-recovery-v1.json').write_text(json.dumps({'status':'recovering','run':run,'head':head,'scope1GiB':str(cg),'records':records,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},indent=2)+'\n');print('PRESERVED',name,flush=True)
(O/'late-ci-stage-recovery-v1.json').write_text(json.dumps({'status':'passed','run':run,'head':head,'scope1GiB':str(cg),'records':records,'no_unstage_or_cache_mapping_mutations':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},indent=2)+'\n')
