from pathlib import Path
import json,re,hashlib,shutil,os,subprocess
F=Path(__file__).resolve().parent;E=F.parent;L=E/'892-joint-current-context-v2/package';V=Path('/home/lee/clifv/.worktrees/stock-extending-production-20261031');P=F/'package';S=json.loads((F/'import-snapshot-v21.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();roots=['FV.Opt.Legalize128Pre'];seen={};owners={};provenance={}
def visit(m):
 if m in seen:return
 rel=Path(m.replace('.','/')+'.lean');owner=L if (L/rel).exists() else V;p=owner/rel
 if not p.exists():assert m.split('.')[0] in {'Lean','Std'};return
 raw=subprocess.check_output(['git','show',S['source_context_tree']+':'+str(rel)]);assert hashlib.sha256(raw).hexdigest()==sha(p),m
 seen[m]={'source':str(rel),'sha256':sha(p)};owners[m]=owner
 for row in p.read_text().splitlines():
  if row.startswith('import '):
   for i in row[7:].split():
    if re.fullmatch(r'[A-Za-z0-9_.]+',i):visit(i)
for m in roots:visit(m)
for m,row in seen.items():
 if m in S['modules']:assert S['modules'][m]==row;continue
 assert (owners[m]/'.lake/build/lib/lean'/Path(row['source']).with_suffix('.olean')).exists(),m
assert not (F/'import-snapshot-v22.json').exists();added=[]
for m,row in seen.items():
 if m in S['modules']:continue
 owner=owners[m];rel=Path(row['source']);(P/rel).parent.mkdir(parents=True,exist_ok=True);assert not (P/rel).exists();shutil.copyfile(owner/rel,P/rel)
 for directory in [owner/'.lake/build/lib/lean'/rel.with_suffix(''),owner/'.lake/build/ir'/rel.with_suffix('')]:
  for src in directory.parent.glob(directory.name+'.*'):
   if not src.is_file():continue
   dest=P/src.relative_to(owner);dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists(),str(dest)
   if src.suffix in {'.hash','.json','.trace'}:shutil.copyfile(src,dest)
   else:os.link(src,dest)
   h=sha(src);assert sha(dest)==h;S['artifacts'][str(dest.relative_to(P))]=h
 S['modules'][m]=row;added.append(m);provenance[m]=str(owner)
S['roots']=sorted(set(S['roots']+roots));S['status']='requires_normal_check';S['new_modules']=added;S['allocated_match_provider_provenance']=provenance
(F/'import-snapshot-v22.json').write_text(json.dumps(S,indent=2)+'\n');v=(F/'verify-access-v21.py').read_text().replace('import-snapshot-v21.json','import-snapshot-v22.json').replace('import-normal-check-v21.json','import-normal-check-v22.json');(F/'verify-access-v22.py').write_text(v);print('Prepared',len(S['modules']),'modules;',len(added),'new completed providers')
