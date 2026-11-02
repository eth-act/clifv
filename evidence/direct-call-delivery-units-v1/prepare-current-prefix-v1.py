from pathlib import Path
import hashlib,json,os,shutil,subprocess,datetime
D=Path(__file__).resolve().parent;E=D.parent;B=Path('/home/lee/clifv');LIVE=E/'892-joint-current-context-v2/package';P=D/'current-foundation-package-v1';S=json.loads((D/'class-foundation-prepared-v1.json').read_text());assert not P.exists();P.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for rel in ['lakefile.toml','lake-manifest.json','lean-toolchain']:
 data=subprocess.check_output(['git','show',S['base']+':'+rel],cwd=B);assert data==(LIVE/rel).read_bytes(),rel
 (P/rel).write_bytes(data)
for rel in S['import_closure']:
 d=P/rel;d.parent.mkdir(parents=True,exist_ok=True)
 data=(D/'class-foundation-sources'/rel).read_bytes() if rel in S['source_hashes'] else subprocess.check_output(['git','show',S['base']+':'+rel],cwd=B)
 d.write_bytes(data)
(P/'.lake').mkdir();(P/'.lake/packages').symlink_to((LIVE/'.lake/packages').resolve(),target_is_directory=True)
# Scripts execute only in this isolated package. They never write the normal package.
for rel in subprocess.check_output(['git','ls-tree','-r','--name-only',S['base'],'scripts'],cwd=B,text=True).splitlines():
 d=P/rel;d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(subprocess.check_output(['git','show',S['base']+':'+rel],cwd=B))
 mode=subprocess.check_output(['git','ls-tree',S['base'],rel],cwd=B,text=True).split()[0]
 if mode=='100755':d.chmod(0o755)
borrowed={};missing=[]
for rel in S['import_closure']:
 if rel in S['source_hashes'] or not (LIVE/rel).exists():continue
 assert (P/rel).read_bytes()==(LIVE/rel).read_bytes(),rel
 stem=Path(rel).with_suffix('')
 if not (LIVE/'.lake/build/lib/lean'/Path(str(stem)+'.olean')).exists():missing.append(rel);continue
 for area in ['lib/lean','ir']:
  path=LIVE/'.lake/build'/area/stem
  for source in path.parent.glob(path.name+'.*'):
   if not source.is_file():continue
   target=P/source.relative_to(LIVE);target.parent.mkdir(parents=True,exist_ok=True)
   # Copy mutable metadata; link immutable compiler products, then forbid later writes to them.
   if source.suffix in ['.trace','.hash','.json']:shutil.copyfile(source,target)
   else:os.link(source,target)
   borrowed[str(target.relative_to(P))]=sha(target)
external=[n for n in S['import_closure'] if n not in S['source_hashes']]
context={'status':'snapshot_prepared_not_validated','base':S['base'],'tree':S['tree'],'package':str(P),'sources':{n:sha(P/n) for n in S['import_closure']},'borrowed_artifacts':borrowed,'missing_providers':missing,'outside_providers':[n for n in external if not (LIVE/n).exists()],'normal_check_roots':[n[:-5].replace('/','.') for n in external if (LIVE/n).exists()],'no_live_package_writes':True,'effective_lean_jobs':1,'cap':'1G','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(D/'current-foundation-snapshot-v1.json').write_text(json.dumps(context,indent=2)+'\n');print('Snapshot',len(context['sources']),'sources;',len(borrowed),'artifact hashes;',len(missing),'missing normal providers')
