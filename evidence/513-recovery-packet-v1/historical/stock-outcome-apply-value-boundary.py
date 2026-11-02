from pathlib import Path
import json,re,hashlib,subprocess,datetime
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],text=True)
proof=json.load(open('/tmp/stock-outcome-value-boundary-check.json'));assert proof['state']=='passed';root=Path.cwd();old=Path('FV/Backend/Proof/LowerSim.lean').read_text();blocks={}
for name in ['dfgCons_congr','loadVal_congr']:
 match=re.search(r'(?m)^theorem '+name+r'\b[\s\S]*?(?=\n\n)',old);assert match;block=match.group()
 if name=='dfgCons_congr':block=old[old.rfind('/-- DFG consistency',0,match.start()):match.end()]
 assert hashlib.sha256(block.encode()).hexdigest()==proof['unchanged_helper_body_sha256'][name];blocks[name]=block
review=json.load(open('/tmp/stock-outcome-witness-import-review.json'));paths=review['candidate_paths']+[p for p,names in review['conservatively_kept'] if names==['dfgCons_congr']];kept=[];edits={}
for name in paths:
 p=Path(name);s=p.read_text();assert s.count('import FV.Backend.Proof.LowerSim\n')==1
 if re.search(r'\bsnoc\b',s):kept.append(name);continue
 edits[name]=s.replace('import FV.Backend.Proof.LowerSim\n','import FV.Backend.Proof.LowerValueRelations\n')
p='FV/E2E/ABIReadOnlyRealize.lean';s=Path(p).read_text();assert 'import FV.Backend.Proof.LowerValueRelations' not in s;edits[p]='import FV.Backend.Proof.LowerValueRelations\n'+s
new=old.replace('import FV.Backend.Proof.LowerOutcomes','import FV.Backend.Proof.LowerValueRelations')
for block in blocks.values():assert new.count(block)==1;new=new.replace(block+'\n\n','')
helper=Path('/tmp/stock-outcome-value-relations-staged.lean').read_text();dest=Path('FV/Backend/Proof/LowerValueRelations.lean');assert not dest.exists()
for block in blocks.values():assert block in helper
strip=lambda s:'\n'.join(x for x in s.splitlines() if not x.startswith('import '));parity={}
for name,after in edits.items():
 before=Path(name).read_text();assert strip(before)==strip(after),name;parity[name]=hashlib.sha256(strip(before).encode()).hexdigest()
for name,text in edits.items():Path(name).write_text(text)
Path('FV/Backend/Proof/LowerSim.lean').write_text(new);dest.write_text(helper)
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'base_head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'unchanged_body_sha256':parity,'unchanged_moved_helper_sha256':proof['unchanged_helper_body_sha256'],'import_only_witness_files':len(edits)-1,'conservatively_left_with_snoc':kept,'lower_outcomes_unchanged':True,'all_other_lower_sim_source_exact':True,'scope':'Only two exact-body lemma moves and import providers; no existing theorem/proof/definition body changes. Full current normal/trust gates pending.'};Path('/tmp/stock-outcome-value-boundary-applied.json').write_text(json.dumps(r,indent=2)+'\n');print('Import-only witness files',r['import_only_witness_files'],'conservatively kept',len(kept));subprocess.run(['git','diff','--check'],check=True)
