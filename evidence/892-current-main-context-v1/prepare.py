"""Prepare current-main isolated source and import snapshots; never run Lean."""
from pathlib import Path
import collections, fcntl, hashlib, json, os, re, subprocess

ROOT=Path('/home/lee/clifv')
OUT=Path(__file__).resolve().parent
E=OUT.parent
V=ROOT/'.worktrees/stock-extending-production-20261031'
BASE='3a6719b44b0e6b38e24cd0de82655f93b78272a9'
FROZEN='a4c0726d46c5908b4ac06cf797ee939af8644703'
PROD='90c51c880b9d614f7c5f9730b8363a6321c840de'
PKG=OUT/'package'
assert not PKG.exists(), 'Preserve earlier diagnostics; select a new packet version'

def git(*args):
    return subprocess.check_output(['git',*args],cwd=ROOT)
def save(name,data):
    p=OUT/name;p.parent.mkdir(parents=True,exist_ok=True)
    p.write_bytes(data if isinstance(data,bytes) else (json.dumps(data,indent=2)+'\n').encode())
def digest(data):return hashlib.sha256(data).hexdigest()

assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=V,text=True).strip()==FROZEN
assert not subprocess.check_output(['git','status','--porcelain'],cwd=V,text=True).strip()
assert git('rev-parse','origin/main').decode().strip()==BASE
assert subprocess.check_output(['gh','api','repos/eth-act/clifv/commits/main','--jq','.sha'],text=True).strip()==BASE
tree=git('merge-tree','--write-tree',BASE,PROD).decode().strip()
manifest=json.loads((E/'return-pin-production-delivery-packet-v1.json').read_text())
for p,h in manifest['files'].items():assert digest(git('show',tree+':'+p))==h,p
assert len(manifest['files'])==18

def blobs(ref):return {l.split('\t')[1]:l.split()[2] for l in git('ls-tree','-r',ref).decode().splitlines()}
current,frozen=blobs(tree),blobs(FROZEN)
graph=collections.defaultdict(set)
for line in git('grep','-n','-E',r'^(public |private |meta )*import ',tree,'--','*.lean').decode().splitlines():
    _,p,_,text=line.split(':',3)
    imports=re.sub(r'^(?:(?:public|private|meta)\s+)*import\s+','',text).split('--')[0]
    graph[p].update(m.replace('.','/')+'.lean' for m in imports.split() if m.replace('.','/')+'.lean' in current)
templates={
 'matrix/PrepareActualBundles.lean':E/'return-pin-production-activation-packet-v1/PrepareActualBundlesV6.lean',
 'matrix/PrepareTypedBundles.lean':E/'return-pin-typed-proof-packet-v1/PrepareTypedBundlesV1.lean',
 'matrix/ReflowActualBundle.lean':E/'return-pin-production-activation-packet-v1/ReflowActualBundleV1.lean',
 'matrix/ReflowTypedBundle.lean':E/'return-pin-typed-proof-packet-v1/ReflowTypedBundleV1.lean',
 'matrix/BackendEntrySmoke.lean':E/'return-pin-production-activation-packet-v1/BackendEntrySmokeV3.lean',
}
for p,source in templates.items():
    data=source.read_text()
    graph[p]={m.replace('.','/')+'.lean' for m in re.findall(r'(?m)^import\s+([\w.]+)',data) if m.replace('.','/')+'.lean' in current}
roots=set(manifest['files'])|set(templates)
closure=set(roots);todo=list(roots)
while todo:
    for p in graph.get(todo.pop(),set())-closure:closure.add(p);todo.append(p)
module_paths={p for p in closure if p.startswith(('FV/','FVTest/'))}
direct={p for p in module_paths if current[p]!=frozen.get(p)}
missing={p for p in module_paths if not (V/'.lake/build/lib/lean'/Path(p).with_suffix('.olean')).exists()}
affected=set(direct)|missing
while True:
    delta={p for p in module_paths if graph.get(p,set())&affected}-affected
    if not delta:break
    affected|=delta
queue=[];pending=set(affected)
while pending:
    ready=sorted(p for p in pending if not graph.get(p,set())&pending)
    assert ready,('Dependency cycle',sorted(pending)[:20])
    queue+=ready;pending-=set(ready)
profiles={}
for source in [V/'scripts/lake-module-peaks.tsv',V/'.lake/lake-module-peaks.tsv']:
    if not source.exists():continue
    for line in source.read_text().splitlines():
        fields=line.split('\t')
        if line.startswith('#') or len(fields)<2:continue
        try:mb=float(fields[1])
        except ValueError:continue
        name=fields[0].replace('.','/')+'.lean'
        prior=profiles.get(name,{'peak_rss_mb':0})
        if mb>prior['peak_rss_mb']:profiles[name]={'peak_rss_mb':mb,'profile':str(source)}
over3={p:profiles[p] for p in affected if profiles.get(p,{}).get('peak_rss_mb',0)>3072}
save('preparation-inventory.json',{'base':BASE,'candidate_tree':tree,'frozen_source':FROZEN,'production_files':manifest['files'],'module_closure':len(module_paths),'direct_changed_sources':sorted(direct),'missing_artifacts':sorted(missing),'minimal_rebuild_queue':queue,'rebuild_count':len(queue),'historical_over3GiB':over3,'all_profiles_for_queued_modules':{p:profiles[p] for p in queue if p in profiles},'no_builds':True})
print(json.dumps({'module_closure':len(module_paths),'direct_changed_sources':len(direct),'missing_artifacts':len(missing),'minimal_rebuild_queue':len(queue),'historical_over3GiB':over3,'no_builds':True}),flush=True)

PKG.mkdir()
(PKG/'lakefile.toml').write_text('name = "production892currentcontext"\nversion = "0.1.0"\n\n[[lean_lib]]\nname = "FV"\n\n[[lean_lib]]\nname = "FVTest"\n')
(PKG/'lean-toolchain').write_bytes(git('show',BASE+':lean-toolchain'))
source_hashes={}
for p in sorted(closure):
    data=templates[p].read_bytes() if p in templates else git('show',tree+':'+p)
    target=PKG/p;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data);source_hashes[p]=digest(data)
context_sources={}
for root in sorted(roots):
    found={root};todo=[root]
    while todo:
        for p in graph.get(todo.pop(),set())-found:found.add(p);todo.append(p)
    context_sources[root]={'source_paths':{p:{'sha256':source_hashes[p],'blob':current.get(p),'frozen_blob':frozen.get(p),'owned_rebuild':p in affected} for p in sorted(found)}}
linked=[]
with (E/'main870-cache-import.lock').open('a+') as lock:
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    for p in sorted(module_paths-affected):
        assert current[p]==frozen[p]
        stem=V/'.lake/build/lib/lean'/Path(p).with_suffix('')
        for suffix in ['.olean','.ilean','.olean.private','.olean.server']:
            source=Path(str(stem)+suffix)
            if not source.exists():continue
            target=Path(str(PKG/'.lake/build/lib/lean'/Path(p).with_suffix(''))+suffix)
            target.parent.mkdir(parents=True,exist_ok=True)
            h=digest(source.read_bytes());os.link(source,target)
            assert digest(target.read_bytes())==h
            linked.append({'path':str(target.relative_to(PKG)),'sha256':h,'inode':target.stat().st_ino,'source':str(source)})
context={'base':BASE,'candidate_tree':tree,'frozen_source':FROZEN,'package':str(PKG),'source_hashes':source_hashes,'per_target':context_sources,'queue':queue,'audits':sorted(p for p in roots if p.startswith('scripts/audit/')),'matrix_templates':{p:{'source':str(s),'sha256':source_hashes[p]} for p,s in templates.items()},'historical_over3GiB':over3,'historical_profile_not_a_guarantee':True,'hardlinked_import_count':len(linked),'direct_kernel_scope':'Current-context proper Lean kernels and unchanged AX audits. Not normal Lake keys, full reverse importers, full libraries or runtime suite.','no_builds':True,'proofslot':'not granted'}
save('context.json',context)
save('ownership.json',{'owner':'worker-O / investigate_513 delegate','purpose':'Current #892 proof context after #894; active isolated snapshot, not a warm cache','package':str(PKG),'hardlinked_imports':linked,'owned_output_modules':queue,'write_rule':'Unlink every owned output before any compiler writes. Never write/chmod hardlinked imports.','cleanup':'After preserving sources/logs/generated sources/receipts and output hashes, remove package/.lake only. Never alter frozen V or shared cache mappings.','worktrees_created':[],'caches_created':[],'proofslot':'not granted; do not launch','no_builds':True})
print(json.dumps({'prepared_package':str(PKG),'queued_kernels':len(queue),'read_only_import_outputs':len(linked),'historical_over3GiB_count':len(over3),'no_builds':True}),flush=True)
