from pathlib import Path
import subprocess,json,hashlib,os,tempfile,re,collections
O=Path(__file__).resolve().parent;M=O/'current-main-migration-v4';M.mkdir();E=O.parent;R=Path('/home/lee/clifv');OLD=json.loads((O/'context.json').read_text());base='2e4c9d1c24ae025617c4aa9360b38d495460a7cd';manifest=json.loads((E/'return-pin-production-delivery-packet-v1.json').read_text())['files']
def git(*args,**kw):return subprocess.check_output(['git',*args],cwd=R,**kw)
def sha(data):return hashlib.sha256(data).hexdigest()
fd,index=tempfile.mkstemp(prefix='migration-index-',dir=M);os.close(fd);os.unlink(index);env=dict(os.environ,GIT_INDEX_FILE=index)
try:
 subprocess.run(['git','read-tree',base],cwd=R,env=env,check=True)
 for rel,h in manifest.items():
  p=E/'return-pin-production-delivery-packet-v1'/rel;assert sha(p.read_bytes())==h
  blob=git('hash-object','-w',str(p)).decode().strip();subprocess.run(['git','update-index','--add','--cacheinfo','100644',blob,rel],cwd=R,env=env,check=True)
 tree=git('write-tree',env=env).decode().strip()
finally:Path(index).unlink(missing_ok=True)
paths={line.split('\t')[1] for line in git('ls-tree','-r',tree).decode().splitlines()};graph=collections.defaultdict(set)
for line in git('grep','-n','-E',r'^(public |private |meta )*import ',tree,'--','*.lean').decode().splitlines():
 _,p,_,text=line.split(':',3);words=re.sub(r'^(?:(?:public|private|meta)\s+)*import\s+','',text).split('--')[0].split();graph[p].update(w.replace('.','/')+'.lean' for w in words if w.replace('.','/')+'.lean' in paths)
roots=set(manifest)|set(OLD['matrix_templates'])
for p,item in OLD['matrix_templates'].items():
 data=Path(item['source']).read_bytes();assert sha(data)==item['sha256'];graph[p]={w.replace('.','/')+'.lean' for w in re.findall(r'(?m)^import\s+([\w.]+)',data.decode()) if w.replace('.','/')+'.lean' in paths}
closure=set(roots);todo=list(roots)
while todo:
 for p in graph.get(todo.pop(),set())-closure:closure.add(p);todo.append(p)
hashes={p:(sha(Path(OLD['matrix_templates'][p]['source']).read_bytes()) if p in OLD['matrix_templates'] else sha(git('show',tree+':'+p))) for p in closure};mods={p for p in closure if p.startswith(('FV/','FVTest/'))};pending=set(mods);queue=[]
while pending:
 ready=sorted(p for p in pending if not graph.get(p,set())&pending);assert ready;queue+=ready;pending-=set(ready)
changed={p for p,h in hashes.items() if OLD['source_hashes'].get(p)!=h};invalid=set(changed)
while True:
 new={p for p in mods if graph.get(p,set())&invalid}-invalid
 if not new:break
 invalid|=new
new=dict(OLD,base=base,joint_tree=tree,source_hashes=hashes,imports={p:sorted(graph[p]) for p in closure},full_project_queue=queue,kernel_queue=[],project_modules=len(mods),status='prepared_migration_pending_old_owner_release',previous_joint_tree=OLD['joint_tree'],historical_reused_before_migration=OLD['reused'],reused={},ci_source_changes=[],ci_transitive_invalidations=[],new_source_changes=sorted(changed),current_migration_invalidations=sorted(invalid),normalkeys='Real Lake will recompute every inputkey after reviewed source migration; old80a receipts remain historical',head513='3d8e0c5d25e4f0849f76670b1fd492e8eb2cadae')
(M/'context.json').write_text(json.dumps(new,indent=2)+'\n');(M/'old-context.json').write_text(json.dumps(OLD,indent=2)+'\n');(M/'normal-provider-targets.txt').write_text('\n'.join(p[:-5].replace('/','.') for p in queue)+'\n')
r={'status':'prepared_only','actual_main':base,'old_joint_tree':OLD['joint_tree'],'new_joint_tree':tree,'production_files':manifest,'source_changes':sorted(changed),'old_source_hashes':{p:OLD['source_hashes'].get(p) for p in changed},'new_source_hashes':{p:hashes[p] for p in changed},'new_project_modules':len(mods),'old_project_modules':OLD['project_modules'],'transitive_invalidations':len(invalid),'source_files_written_to_active_package':False,'no_branch_writes':True};(M/'preparation-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
