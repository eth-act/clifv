from pathlib import Path
import re,json,os,subprocess,hashlib,datetime
root=Path('/tmp/stock-outcome-value-interface-check');pkg=root/'ValueInterfaceScratch';pkg.mkdir(parents=True,exist_ok=True);old=Path('FV/Backend/Proof/LowerSim.lean').read_text();blocks={}
for name in ['dfgCons_congr','loadVal_congr']:
 match=re.search(r'(?m)^theorem '+name+r'\b[\s\S]*?(?=\n\n)',old);assert match;blocks[name]=match.group()
 if name=='dfgCons_congr':
  start=old.rfind('/-- DFG consistency',0,match.start());assert start>=0;blocks[name]=old[start:match.end()]
helper='import FV.Backend.Proof.LowerOutcomes\nnamespace Backend.Proof.Driver\nopen Backend Backend.Proof\nvariable {ctx : Ctx}\n\n'+'\n\n'.join(blocks.values())+'\nend Backend.Proof.Driver\n';(pkg/'LowerValueRelations.lean').write_text(helper)
copy=old.replace('import FV.Backend.Proof.LowerOutcomes','import ValueInterfaceScratch.LowerValueRelations')
for block in blocks.values():assert copy.count(block)==1;copy=copy.replace(block+'\n\n','')
(pkg/'LowerSim.lean').write_text(copy);Path('/tmp/stock-outcome-value-relations-staged.lean').write_text(helper)
E=os.environ.copy();E.update(json.load(open('/tmp/stock-div-release-env.json')));E['FV_MEMCAP']='3G';lp=subprocess.check_output(['scripts/memcap.sh','lake','env','printenv','LEAN_PATH'],env=E,text=True).strip();E['LEAN_PATH']=str(root)+':'+lp;records=[]
for src in [pkg/'LowerValueRelations.lean',pkg/'LowerSim.lean']:
 log=root/(src.stem+'.log')
 with log.open('w') as f:r=subprocess.run(['scripts/memcap.sh','lean','--root='+str(root),'-o',str(src.with_suffix('.olean')),str(src)],env=E,stdout=f,stderr=subprocess.STDOUT)
 records.append({'source':str(src),'returncode':r.returncode,'log':str(log)});print(src.stem,r.returncode,flush=True)
 if r.returncode:print(log.read_text()[-1600:]);break
else:
 checks='set_option pp.universes true\nset_option pp.explicit true\nset_option pp.fullNames true\n#check @Backend.Proof.Driver.dfgCons_congr\n#check @Backend.Proof.Driver.loadVal_congr\n#print axioms Backend.Proof.Driver.dfgCons_congr\n#print axioms Backend.Proof.Driver.loadVal_congr\n';outputs=[]
 for tag,imp in [('old','FV.Backend.Proof.LowerSim'),('new','ValueInterfaceScratch.LowerValueRelations')]:
  src=root/(tag+'-types.lean');src.write_text('import '+imp+'\n'+checks);log=root/(tag+'-types.log')
  with log.open('w') as f:r=subprocess.run(['scripts/memcap.sh','lean',str(src)],env=E,stdout=f,stderr=subprocess.STDOUT)
  records.append({'source':str(src),'returncode':r.returncode,'log':str(log)});outputs.append(log.read_text());print(tag,'types/axioms',r.returncode,flush=True)
 equal=outputs[0]==outputs[1];print('exact elaborated type/axiom output',equal,flush=True)
state='passed' if len(records)==4 and not any(x['returncode'] for x in records) and equal else 'failed';result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'state':state,'scope':'Isolated unchanged two-lemma stable provider and complete LowerSim copy. Elaborated types/required axioms exactly compared. No tracked shared-file edits yet.','unchanged_helper_body_sha256':{n:hashlib.sha256(s.encode()).hexdigest() for n,s in blocks.items()},'records':records};Path('/tmp/stock-outcome-value-boundary-check.json').write_text(json.dumps(result,indent=2)+'\n');raise SystemExit(0 if state=='passed' else 1)
