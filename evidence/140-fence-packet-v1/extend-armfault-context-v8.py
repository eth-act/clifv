from pathlib import Path
import subprocess,re,json,hashlib,shutil,os
F=Path(__file__).resolve().parent;E=F.parent;P=F/'package';V=Path('/home/lee/clifv/.worktrees/stock-extending-production-20261031');S=json.loads((F/'import-snapshot-v7.json').read_text());tree=S['source_context_tree'];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();seen={};raws={}
def visit(m):
 if m in seen:return
 rel=Path(m.replace('.','/')+'.lean');raw=subprocess.run(['git','show',tree+':'+str(rel)],capture_output=True)
 if raw.returncode:assert m.split('.')[0] in {'Lean','Std'};return
 h=hashlib.sha256(raw.stdout).hexdigest();assert sha(V/rel)==h,('Historical source differs',m)
 seen[m]={'source':str(rel),'sha256':h};raws[m]=raw.stdout
 for line in raw.stdout.decode().splitlines():
  if line.startswith('import '):
   for i in line[7:].split():
    if re.fullmatch(r'[A-Za-z0-9_.]+',i):visit(i)
visit('FV.ArmFault.Step')
for m,row in seen.items():
 if m in S['modules']:assert row==S['modules'][m]
 else:assert (V/'.lake/build/lib/lean'/Path(row['source']).with_suffix('.olean')).exists()
assert not (F/'import-snapshot-v8.json').exists();added=[]
for m,row in seen.items():
 if m in S['modules']:continue
 rel=Path(row['source']);src=P/rel;src.parent.mkdir(parents=True,exist_ok=True);assert not src.exists();src.write_bytes(raws[m]);assert sha(src)==row['sha256']
 for directory in [V/'.lake/build/lib/lean'/rel.with_suffix(''),V/'.lake/build/ir'/rel.with_suffix('')]:
  for borrowed in directory.parent.glob(directory.name+'.*'):
   if not borrowed.is_file():continue
   dest=P/borrowed.relative_to(V);dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists(),str(dest)
   if borrowed.suffix in {'.trace','.json','.hash'}:shutil.copyfile(borrowed,dest)
   else:os.link(borrowed,dest)
   h=sha(borrowed);assert sha(dest)==h;S['artifacts'][str(dest.relative_to(P))]=h
 S['modules'][m]=row;added.append(m)
S['roots']=sorted(set(S['roots']+['FV.ArmFault.Step']));S['status']='requires_normal_check';S['armfault_reuse']={'baseline_tree':tree,'complete_source_closure':sorted(seen),'new_modules':added,'historical_output_owner':str(V),'reuse_validated':False,'project_fallback':False}
(F/'import-snapshot-v8.json').write_text(json.dumps(S,indent=2)+'\n')
v=(F/'verify-access-v7.py').read_text().replace('import-snapshot-v7.json','import-snapshot-v8.json').replace('import-normal-check-v7.json','import-normal-check-v8.json');(F/'verify-access-v8.py').write_text(v)
print('Prepared',len(S['modules']),'modules;',len(added),'ArmFault providers; normal-check still required')
