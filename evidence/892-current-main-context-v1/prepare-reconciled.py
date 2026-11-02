"""Pin the reconciled892/513 trees and prepare the second-stage source only."""
from pathlib import Path
import collections, hashlib, json, re, subprocess

OUT=Path(__file__).resolve().parent
E=OUT.parent
ROOT=Path('/home/lee/clifv')
HEAD892='36dd36a6c1746acb1741dd5c984b0ead1b8a2d18'
HEAD513='328541fa3402deac8d4df8ff7f790e95196c37a3'
TREE892='7dbf27cb7545c4a9d137719c8f59d7b05d91c074'
TREE513='a4dcc3fa905fad9d6c0c7f2a49fcd335b5989f84'
git=lambda *a:subprocess.check_output(['git',*a],cwd=ROOT)
ctx=json.loads((OUT/'context.json').read_text())
assert ctx['candidate_tree']==TREE892
assert git('rev-parse',HEAD892+'^{tree}').decode().strip()==TREE892
assert git('rev-parse',HEAD513+'^{tree}').decode().strip()==TREE513
manifest=json.loads((E/'return-pin-production-delivery-packet-v1.json').read_text())
for p,h in manifest['files'].items():assert hashlib.sha256(git('show',HEAD892+':'+p)).hexdigest()==h
roots892={p for p in manifest['files'] if p.startswith(('FV/','FVTest/'))}
pending=set(roots892);queue892=[]
while pending:
    ready=[]
    for p in pending:
        text=(OUT/'package'/p).read_text()
        deps={m.replace('.','/')+'.lean' for m in re.findall(r'(?m)^import\s+([\w.]+)',text)}
        if not deps&pending:ready.append(p)
    assert ready
    queue892+=sorted(ready);pending-=set(ready)
pkg=OUT/'package-513';assert not pkg.exists();pkg.mkdir()
source892={p:git('show',HEAD892+':'+p) for p in roots892}
paths=set(git('ls-tree','-r','--name-only',HEAD513).decode().splitlines())
graph=collections.defaultdict(set)
for line in git('grep','-n','-E',r'^(public |private |meta )*import ',HEAD513,'--','*.lean').decode().splitlines():
    _,p,_,text=line.split(':',3)
    graph[p].update(m.replace('.','/')+'.lean' for m in re.sub(r'^(?:(?:public|private|meta)\s+)*import\s+','',text).split('--')[0].split() if m.replace('.','/')+'.lean' in paths)
roots513={'FV/Backend/Proof/'+n+'.lean' for n in ['LowerOutcomes','LowerValueRelations','LowerSim','PrepareSound']}|{'FV/E2E/'+n+'.lean' for n in ['Statement','Main','ABIReadOnlyRealize']}
closure=set(roots513);todo=list(closure)
while todo:
    for p in graph[todo.pop()]-closure:closure.add(p);todo.append(p)
sourcehash={}
for p in closure:
    data=git('show',HEAD513+':'+p);dest=pkg/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data);sourcehash[p]=hashlib.sha256(data).hexdigest()
for name in ['lakefile.toml','lake-manifest.json','lean-toolchain']:(pkg/name).write_bytes(git('show',HEAD513+':'+name))
queue513=[];pending=set(roots513)
while pending:
    ready=sorted(p for p in pending if not graph[p]&pending);assert ready
    queue513+=ready;pending-=set(ready)
names=['VTrapFrom','VRetFrom','VTrapFrom.prefix','VRetFrom.prefix','ArgsAtEntry','Reach','dfgCons_congr','loadVal_congr']
checks='set_option pp.universes true\nset_option pp.explicit true\nset_option pp.fullNames true\n'+'\n'.join('#check @Backend.Proof.Driver.'+n+'\n#print axioms Backend.Proof.Driver.'+n for n in names)+'\n'
(OUT/'package/Baseline513Types.lean').write_text('import FV.Backend.Proof.LowerSim\n'+checks)
(pkg/'Candidate513Types.lean').write_text('import FV.Backend.Proof.LowerValueRelations\n'+checks)
out={'head892':HEAD892,'tree892':TREE892,'head513':HEAD513,'tree513':TREE513,'queue892':queue892,'queue513':queue513,'513_sources':sourcehash,'513_context_count':len(closure),'513_exact_type_axiom_roots':['Backend.Proof.Driver.'+n for n in names],'892_audits':ctx['audits'],'coherent_current_baseline_required':True,'no_builds':True,'no_ref_writes':True}
(OUT/'reconciled-targets.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'head892':HEAD892,'892_kernels':len(queue892),'892_audits':len(ctx['audits']),'head513':HEAD513,'513_kernels':len(queue513),'513_context_sources':len(closure),'types_and_axiom_roots':8,'no_builds':True}))
