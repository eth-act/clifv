from pathlib import Path
import json,re,hashlib,shutil,os
F=Path(__file__).resolve().parent;E=F.parent;L=E/'892-joint-current-context-v2/package';P=F/'package';S=json.loads((F/'import-snapshot-v12.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
roots=['FV.Backend.Proof.PrepareSound','FV.Backend.Proof.DeadCleanupPrepare'];seen={}
def visit(m):
 if m in seen:return
 rel=Path(m.replace('.','/')+'.lean');p=L/rel
 if not p.exists():assert m.split('.')[0] in {'Lean','Std'};return
 seen[m]={'source':str(rel),'sha256':sha(p)}
 for row in p.read_text().splitlines():
  if row.startswith('import '):
   for i in row[7:].split():
    if re.fullmatch(r'[A-Za-z0-9_.]+',i):visit(i)
for m in roots:visit(m)
for m,row in seen.items():
 if m in S['modules']:assert S['modules'][m]==row;continue
 assert (L/'.lake/build/lib/lean'/Path(row['source']).with_suffix('.olean')).exists(),m
assert not (F/'import-snapshot-v13.json').exists()
added=[]
for m,row in seen.items():
 if m in S['modules']:continue
 rel=Path(row['source']);(P/rel).parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(L/rel,P/rel)
 assert sha(P/rel)==row['sha256']
 for directory in [L/'.lake/build/lib/lean'/rel.with_suffix(''),L/'.lake/build/ir'/rel.with_suffix('')]:
  for src in directory.parent.glob(directory.name+'.*'):
   if not src.is_file():continue
   dest=P/src.relative_to(L);dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists(),str(dest)
   if src.suffix in {'.hash','.json','.trace'}:shutil.copyfile(src,dest)
   else:os.link(src,dest)
   h=sha(src);assert sha(dest)==h;S['artifacts'][str(dest.relative_to(P))]=h
 S['modules'][m]=row;added.append(m)
S['roots']=sorted(set(S['roots']+roots));S['status']='requires_normal_check';S['new_modules']=added
(F/'import-snapshot-v13.json').write_text(json.dumps(S,indent=2)+'\n')
v=(F/'verify-access-v12.py').read_text().replace('import-snapshot-v12.json','import-snapshot-v13.json').replace('import-normal-check-v12.json','import-normal-check-v13.json');(F/'verify-access-v13.py').write_text(v)
print('Prepared',len(S['modules']),'modules;',len(added),'new completed providers')
