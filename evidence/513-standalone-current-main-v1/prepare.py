"""Prepare a standalone513 context. Never load frozen project outputs or publish."""
from pathlib import Path
import collections, hashlib, json, re, subprocess

ROOT=Path('/home/lee/clifv')
OUT=Path(__file__).resolve().parent
E=OUT.parent
BASE='3b586e45bb65855c9e6c0640f3e9f5f75abd4446'
OLD='5aae55c32030e3e9f15ab6515a2cccf268751646'
LEAN=Path('/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean')
LIB=LEAN.parent.parent/'lib/lean'
git=lambda *a:subprocess.check_output(['git',*a],cwd=ROOT)
sha=lambda b:hashlib.sha256(b).hexdigest()
assert not (OUT/'context.json').exists(), 'Preserve prior preparation'
assert subprocess.check_output(['gh','api','repos/eth-act/clifv/commits/main','--jq','.sha'],text=True).strip()==BASE
TREE=git('merge-tree','--write-tree',BASE,OLD).decode().strip()
old_hashes=json.loads((E/'513-recovery-packet-v1/recovery-receipt.json').read_text())['source_sha256']
changed=git('diff','--name-only',BASE,TREE).decode().splitlines()
assert set(changed)==set(old_hashes) and len(changed)==207
for p,h in old_hashes.items():assert sha(git('show',TREE+':'+p))==h,p
roots=['FV/Backend/Proof/'+n+'.lean' for n in ['LowerOutcomes','LowerValueRelations','LowerSim','PrepareSound']]
roots+=['FV/E2E/'+n+'.lean' for n in ['Statement','Main','ABIReadOnlyRealize']]
records={}
external={}
for stage,tree in [('baseline',BASE),('candidate',TREE)]:
    pkg=OUT/stage;assert not pkg.exists();pkg.mkdir()
    files=set(git('ls-tree','-r','--name-only',tree).decode().splitlines())
    sources={};imports={};todo=[p for p in roots if p in files]
    while todo:
        p=todo.pop()
        if p in sources:continue
        data=git('show',tree+':'+p);sources[p]=data
        tokens=[]
        for line in data.decode().splitlines():
            m=re.match(r'^(?:(?:public|private|meta)\s+)*import\s+(.+)',line)
            if m:tokens+=m.group(1).split('--')[0].split()
        deps=set()
        for name in tokens:
            local=name.replace('.','/')+'.lean'
            if local in files:
                assert local.startswith(('FV/','FVTest/')),('Unexpected project root; classify before running',local)
                deps.add(local)
            else:
                artifact=LIB/(name.replace('.','/')+'.olean')
                assert artifact.is_file() and artifact.resolve().is_relative_to(LIB.resolve()),('Unpinned external import',name)
                external[name]={'path':str(artifact),'sha256':sha(artifact.read_bytes())}
        imports[p]=deps;todo+=list(deps-sources.keys())
    ordered=[];pending=set(sources)
    while pending:
        ready=sorted(p for p in pending if not imports[p]&pending);assert ready
        ordered+=ready;pending-=set(ready)
    hashes={}
    for p,data in sources.items():
        dest=pkg/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data);hashes[p]=sha(data)
    (pkg/'lean-toolchain').write_bytes(git('show',BASE+':lean-toolchain'))
    (pkg/'.lake/build/lib/lean').mkdir(parents=True)
    records[stage]={'source_ref':tree,'package':str(pkg),'source_hashes':hashes,'full_topological_queue':ordered,'project_source_count':len(sources),'imports':{p:sorted(d) for p,d in imports.items()}}
candidate_targets=[p for p in records['candidate']['full_topological_queue'] if p in roots]
assert len(candidate_targets)==7
newpaths=set(records['candidate']['source_hashes'])-set(records['baseline']['source_hashes'])
assert newpaths=={'FV/Backend/Proof/LowerOutcomes.lean','FV/Backend/Proof/LowerValueRelations.lean'}
for p,h in records['candidate']['source_hashes'].items():
    if p not in roots:assert records['baseline']['source_hashes'][p]==h,('Intermediate differs; rebuild separately',p)
names=['VTrapFrom','VRetFrom','VTrapFrom.prefix','VRetFrom.prefix','ArgsAtEntry','Reach','dfgCons_congr','loadVal_congr']
checks='set_option pp.universes true\nset_option pp.explicit true\nset_option pp.fullNames true\n'+'\n'.join('#check @Backend.Proof.Driver.'+n+'\n#print axioms Backend.Proof.Driver.'+n for n in names)+'\n'
(OUT/'baseline/Types.lean').write_text('import FV.Backend.Proof.LowerSim\n'+checks)
(OUT/'candidate/Types.lean').write_text('import FV.Backend.Proof.LowerValueRelations\n'+checks)
context={'base':BASE,'candidate_tree':TREE,'production892_included':False,'extraction_files':old_hashes,'old_headers_exact':372,'consumer_bodies_exact':203,'moved_declarations_exact':8,'stages':records,'candidate_targets':candidate_targets,'external_imports':external,'lean_executable':str(LEAN),'lean_executable_sha256':sha(LEAN.read_bytes()),'toolchain_library':str(LIB),'allowed_lean_paths':'Only the owned stage library and pinned toolchain library. No frozen or global project artifact fallback.','baseline_policy':'Compile every project module fresh. Candidate reuses only this newly compiled baseline for byte-identical project sources; all seven changed providers compile fresh.','resource_cap':'2G,one command at a time,LEAN/OMP threads2; stop on first failure/OOM without retry','no_builds_yet':True,'no_cache_or_worktree':True,'no_branch_writes':True,'normal_full_affected_gates':'Still pending and separate'}
(OUT/'context.json').write_text(json.dumps(context,indent=2)+'\n')
print(json.dumps({'base':BASE,'tree':TREE,'baseline_project_modules':records['baseline']['project_source_count'],'candidate_project_sources':records['candidate']['project_source_count'],'candidate_targets':7,'external_modules':len(external),'production892_included':False,'no_builds_yet':True}))
