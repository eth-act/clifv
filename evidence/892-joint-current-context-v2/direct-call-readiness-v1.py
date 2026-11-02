from pathlib import Path
import json,hashlib,subprocess,re,collections,datetime
R=Path('/home/lee/clifv');E=R/'.git/agent-evidence/stock-memory-20261029';O=Path(__file__).resolve().parent;P=O/'package';base='3d8e0c5d25e4f0849f76670b1fd492e8eb2cadae';packet=E/'direct-call-result-packet-v1';manifest=json.loads((E/'direct-call-result-packet-v1.json').read_text());C=json.loads((O/'context.json').read_text())
def git(*args):return subprocess.check_output(['git',*args],cwd=R)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
blobs={l.split('\t')[1]:l.split()[2] for l in git('ls-tree','-r',base).decode().splitlines()};graph=collections.defaultdict(set)
for line in git('grep','-n','-E',r'^(public |private |meta )*import ',base,'--','*.lean').decode().splitlines():
 _,path,_,text=line.split(':',3);words=re.sub(r'^(?:(?:public|private|meta)\s+)*import\s+','',text).split('--')[0].split()
 graph[path].update(w.replace('.','/')+'.lean' for w in words if w.replace('.','/')+'.lean' in blobs)
for path,h in manifest['files'].items():
 assert sha(packet/path)==h
 for word in re.findall(r'(?m)^import\s+([\w.]+)',(packet/path).read_text()):
  dep=word.replace('.','/')+'.lean';assert dep in blobs or dep in manifest['files'];graph[path].add(dep)
closure=set(manifest['files']);todo=list(closure)
while todo:
 for dep in graph.get(todo.pop(),set())-closure:closure.add(dep);todo.append(dep)
mods=closure-set(manifest['files']);out={};missing=[];mismatch=[];trace_missing=[]
for path in sorted(mods):
 data=git('show',base+':'+path);h=hashlib.sha256(data).hexdigest()
 if path not in C['source_hashes'] or C['source_hashes'][path]!=h:mismatch.append(path)
 stem=P/'.lake/build/lib/lean'/Path(path).with_suffix('');olean=Path(str(stem)+'.olean');trace=Path(str(stem)+'.trace')
 row={'source_sha256':h,'in_joint_sources':path in C['source_hashes'],'source_matches_joint':C['source_hashes'].get(path)==h,'olean_exists':olean.is_file(),'trace_exists':trace.is_file()}
 if not olean.is_file():missing.append(path)
 if not trace.is_file():trace_missing.append(path)
 else:
  try:
   before=trace.stat();t=json.loads(trace.read_text());after=trace.stat()
   assert (before.st_ino,before.st_size,before.st_mtime_ns)==(after.st_ino,after.st_size,after.st_mtime_ns)
   row['normal_saved_depHash']=t.get('depHash');row['normal_saved_outputs']=t.get('outputs');row['trace_sha256']=sha(trace)
  except (json.JSONDecodeError,AssertionError,FileNotFoundError):row['trace_read']='unstable_or_unreadable; not counted valid'
 out[path]=row
report={'status':'read_only_inventory','base':base,'packet_sources':manifest['files'],'project_imports':len(mods),'missing_provider_outputs':missing,'missing_traces':trace_missing,'sources_outside_or_different_from_joint':mismatch,'providers':out,'normal_key_readiness_passed':False,'why_not_current_validity_claim':'Existing saved trace presence cannot establish current dependency/output fingerprints; current normal preflight did not preserve its per-module valid list. No Lake query or live library/cache write ran.','live_normal_owner':141228,'full_goal_complete':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(O/'direct-call-readiness-state-v1.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:report[k] for k in ['project_imports','missing_provider_outputs','missing_traces','sources_outside_or_different_from_joint','normal_key_readiness_passed']}))
