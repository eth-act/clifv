from pathlib import Path
import json,hashlib,subprocess,os,re,collections,tempfile
R=Path('/home/lee/clifv');E=R/'.git/agent-evidence/stock-memory-20261029';O=E/'892-joint-current-context-v2';O.mkdir();P=O/'package';P.mkdir();OLD=E/'892-current-main-context-v1';S=E/'513-standalone-current-main-v1';C=json.loads((OLD/'context.json').read_text());SC=json.loads((S/'context-ci-v4.json').read_text());STATE=json.loads((S/'state-ci-v4.json').read_text());assert STATE['status']=='passed'
main='7c979e18457fd49d96b6f88f5f364ef62490f94c';head='0d511cd9';prod=json.loads((E/'return-pin-production-delivery-packet-v1.json').read_text())['files']
def git(*args,**kw):return subprocess.check_output(['git',*args],cwd=R,**kw)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
head=git('rev-parse',head).decode().strip();oldtree=git('rev-parse',head+'^{tree}').decode().strip()
fd,index=tempfile.mkstemp(prefix='joint892-index-',dir=O);os.close(fd);os.unlink(index);env=dict(os.environ,GIT_INDEX_FILE=index)
try:
 subprocess.run(['git','read-tree',oldtree],cwd=R,env=env,check=True)
 for rel,h in prod.items():
  src=E/'return-pin-production-delivery-packet-v1'/rel;assert sha(src)==h
  blob=git('hash-object','-w',str(src)).decode().strip();subprocess.run(['git','update-index','--add','--cacheinfo','100644',blob,rel],cwd=R,env=env,check=True)
 tree=git('write-tree',env=env).decode().strip()
finally:Path(index).unlink(missing_ok=True)
blobs={l.split('\t')[1]:l.split()[2] for l in git('ls-tree','-r',tree).decode().splitlines()}; graph=collections.defaultdict(set)
for line in git('grep','-n','-E',r'^(public |private |meta )*import ',tree,'--','*.lean').decode().splitlines():
 _,p,_,text=line.split(':',3);imports=re.sub(r'^(?:(?:public|private|meta)\s+)*import\s+','',text).split('--')[0]
 graph[p].update(m.replace('.','/')+'.lean' for m in imports.split() if m.replace('.','/')+'.lean' in blobs)
templates=C['matrix_templates'];roots=set(prod)|set(templates)
for p,x in templates.items():
 assert sha(x['source'])==x['sha256'];graph[p]={m.replace('.','/')+'.lean' for m in re.findall(r'(?m)^import\s+([\w.]+)',Path(x['source']).read_text()) if m.replace('.','/')+'.lean' in blobs}
closure=set(roots);todo=list(roots)
while todo:
 for p in graph.get(todo.pop(),set())-closure:closure.add(p);todo.append(p)
hashes={}
for p in closure:
 data=Path(templates[p]['source']).read_bytes() if p in templates else git('show',tree+':'+p)
 dest=P/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data);hashes[p]=hashlib.sha256(data).hexdigest()
modules={p for p in closure if p.startswith(('FV/','FVTest/'))};queue=[];pending=set(modules)
while pending:
 ready=sorted(p for p in pending if not graph.get(p,set())&pending);assert ready;queue+=ready;pending-=set(ready)
# Actualcurrentmain additions preserve this source boundary, except explicit513+892 changes.
cihash={p:hashlib.sha256(git('show','3a6719b44b0e6b38e24cd0de82655f93b78272a9:'+p)).hexdigest() for p in modules if p in C['source_hashes'] and p not in prod}
ci_sources_changed={p for p in modules if cihash.get(p)!=hashes[p]};invalid=set(ci_sources_changed)
while True:
 new={p for p in modules if graph.get(p,set())&invalid}-invalid
 if not new:break
 invalid|=new
suf=['.olean','.olean.private','.olean.server','.ilean','.ir','.trace','.c'];linked={};ci=OLD/'package'
def link(rel,root,kind):
 stem=root/'.lake/build/lib/lean'/Path(rel).with_suffix('');out={}
 if not Path(str(stem)+'.olean').exists():return False
 for suffix in suf:
  src=Path(str(stem)+suffix)
  if src.exists():
   dst=P/src.relative_to(root);dst.parent.mkdir(parents=True,exist_ok=True);os.link(src,dst);out[suffix]={'sha256':sha(src),'bytes':src.stat().st_size}
 linked[rel]={'kind':kind,'source_package':str(root),'outputs':out};return True
for rel in queue:
 if rel not in invalid:link(rel,ci,'exactCI-source-and-full-dependency-closure')
# Reuse fresh513 commands only with exact current source AND actual imported output hashes.
fresh={x['source']:x for x in STATE['command_records'] if x['source']!='Types.lean'}
for rel in queue:
 if rel in linked or rel not in fresh:continue
 rec=fresh[rel];stage=rec['stage'];pkg=Path(SC['stages'][stage]['package'])
 if sha(pkg/rel)!=hashes[rel]:continue
 deps=graph.get(rel,set())&modules
 if not all(d in linked and sha(pkg/'.lake/build/lib/lean'/Path(d).with_suffix('.olean'))==linked[d]['outputs']['.olean']['sha256'] for d in deps):continue
 link(rel,pkg,'fresh513-command-with-exact-direct-import-output-fingerprints')
missing=[p for p in queue if p not in linked]
for name in ['lakefile.toml','lake-manifest.json','lean-toolchain']:(P/name).write_bytes(git('show',main+':'+name))
(P/'.lake/packages').symlink_to(OLD/'package/.lake/packages',target_is_directory=True)
context={'status':'prepared','base':main,'head513':head,'joint_tree':tree,'package':str(P),'source_hashes':hashes,'imports':{p:sorted(graph[p]) for p in closure},'full_project_queue':queue,'kernel_queue':missing,'reused':linked,'project_modules':len(modules),'ci_source_changes':sorted(ci_sources_changed),'ci_transitive_invalidations':sorted(invalid),'892_targets':json.loads((OLD/'reconciled-targets.json').read_text())['queue892'],'audits':C['audits'],'matrix_templates':templates,'lean_executable':SC['lean_executable'],'toolchain_library':SC['toolchain_library'],'proofslot':'12GiB explicit-j2 onejob','noVwrites':True,'no_branch_writes':True,'normalkeys':'CI reused only with exact full transitive source closure; raw kernel outputs remain separate from full normal-key gate'}
(O/'context.json').write_text(json.dumps(context,indent=2)+'\n')
print(json.dumps({'joint_tree':tree,'modules':len(modules),'ci_source_changes':len(ci_sources_changed),'ci_transitive_invalidations':len(invalid),'reused':len(linked),'fresh513_reused':sum(x['kind'].startswith('fresh513') for x in linked.values()),'missing':len(missing),'first_missing':missing[:8]}))
