"""Snapshot immutable current imports; never build or write the live package."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess
E=Path(__file__).resolve().parent.parent
OUT=Path(__file__).resolve().parent
LIVE=E/'892-joint-current-context-v2/package'
P=OUT/'package'
roots=['FV.Backend.Proof.StockProtectedSinkDriver','FV.Backend.Proof.StockMemoryHelperProjection',
       'FV.Backend.Proof.IselAtomic','FV.Backend.Proof.StockSelectionReceipts',
       'FV.Backend.Proof.StockMemorySourceExecution','FV.Backend.Proof.StockScanTrapSemantics']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
seen={};external=set()
def visit(mod):
    if mod in seen:return
    rel=Path(mod.replace('.','/')+'.lean');src=LIVE/rel
    if not src.exists():external.add(mod);return
    seen[mod]={'source':str(rel),'sha256':sha(src)}
    for row in src.read_text().splitlines():
        if row.startswith('import '):
            for imp in row.removeprefix('import ').split():
                if re.fullmatch(r'[A-Za-z0-9_.]+',imp):visit(imp)
for mod in roots:visit(mod)
assert not P.exists(),'Preserve old snapshot; use a new attempt'
P.mkdir()
for name in ['lakefile.toml','lake-manifest.json','lean-toolchain']:
    shutil.copyfile(LIVE/name,P/name)
artifacts={}
for mod,row in seen.items():
    rel=Path(row['source']);(P/rel).parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(LIVE/rel,P/rel)
    stem=LIVE/'.lake/build/lib/lean'/rel.with_suffix('')
    files=list(stem.parent.glob(stem.name+'.*'))
    assert stem.with_suffix('.olean').exists(),('Missing current provider',mod)
    for src in files:
        dest=P/src.relative_to(LIVE);dest.parent.mkdir(parents=True,exist_ok=True)
        os.link(src,dest)
        artifacts[str(dest.relative_to(P))]=sha(dest)
    # Normal-key evidence includes the generated C artifact and its hash.
    ir=LIVE/'.lake/build/ir'/rel.with_suffix('')
    for src in ir.parent.glob(ir.name+'.*'):
        if src.is_file():
            dest=P/src.relative_to(LIVE);dest.parent.mkdir(parents=True,exist_ok=True)
            os.link(src,dest);artifacts[str(dest.relative_to(P))]=sha(dest)
assert external<= {'Std','Lean'},external
context=json.loads((E/'892-joint-current-context-v2/context.json').read_text())
state={'status':'snapshot_prepared_not_yet_normal_checked','roots':roots,'modules':seen,
       'external':sorted(external),'artifacts':artifacts,
       'source_context_tree':context['joint_tree'],
       'lean_executable':context['lean_executable'],'toolchain_library':context['toolchain_library'],
       'config_hashes':{n:sha(P/n) for n in ['lakefile.toml','lake-manifest.json','lean-toolchain']},
       'cache_access':'disabled','project_library_fallback':'none','budget':'1G','threads':1}
(OUT/'import-snapshot-v1.json').write_text(json.dumps(state,indent=2)+'\n')
print(json.dumps({'status':state['status'],'project_imports':len(seen),'borrowed_files':len(artifacts)}))
