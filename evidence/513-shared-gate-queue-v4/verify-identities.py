"""Preserve original inputs, stage identities and successful outcomes in both measurements."""
from pathlib import Path
import argparse,json,hashlib
from identity_checks import require_production_compiled
from stream_comparison import read_comparison
O=Path(__file__).resolve().parent;E=O.parent;p=argparse.ArgumentParser();p.add_argument('--production',type=Path,required=True);p.add_argument('--raw-stock',type=Path,required=True);p.add_argument('--cleanup-e2e',type=Path,required=True);p.add_argument('--legacy-e2e',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();assert not a.out.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
refs=json.loads((O/'accepted-identity-references.json').read_text());oldpath=E/'captured-copy-production-official-vectors-v1/results.json';oldstate=json.loads((E/'captured-copy-production-official-state-v1.json').read_text());assert sha(oldpath)==oldstate['report_sha256'];prior_inputs,prior_stage,_=read_comparison(oldpath)
assert len(prior_inputs)==1302 and len(prior_stage)==4501
accepted={tuple(x) for x in refs['official_reference']['accepted_identities']};assert len(accepted)==1633
records=[]
for mode,path in [('production',a.production),('raw-stock',a.raw_stock)]:
 inputs,stages,now=read_comparison(path);assert now['progress']=='finished';assert now['configuration_overrides']==[] and now['binary_normalization'] is False;assert inputs==prior_inputs,'Original file inputs changed';assert set(stages)==set(prior_stage),'Original stage identities changed'
 retained={k for k in accepted if stages[k].get('exact_code_artifact') is True};lost=sorted(accepted-retained)
 compiled_stage=None
 if mode=='production':
  assert not lost,('Accepted production identities regressed',lost)
  compiled_stage=require_production_compiled(prior_stage,stages)
  assert compiled_stage['prior_compiled_identities']==1997

 records.append({'mode':mode,'input_hashes_exact':1302,'stage_identities_exact':4501,'accepted_reference':1633,'accepted_retained':len(retained),'lost':lost,'compiled_stage_preservation':compiled_stage,'raw_accepted_floor_is_not_invented':mode=='raw-stock','measurement_is_not_equivalence':True,'source_report_sha256':sha(path)})
e2e=[]
for name,current in [('e2e-identities.json',a.cleanup_e2e),('legacy-e2e-identities.json',a.legacy_e2e)]:
 ref=refs['e2e_references'][name];path=Path(ref['path']);assert sha(path)==ref['sha256']
 def indexed(p):
  d=json.loads(p.read_text());assert d['schema']==1;out={(r['file'],r['index'],r['function']):r['stages'] for r in d['functions']};assert len(out)==len(d['functions']);return out
 baseline=indexed(path);actual=indexed(current);assert len(baseline)==1159;assert all(actual.get(k)==v for k,v in baseline.items()),('Successful E2E identity/stage regressed',name)
 e2e.append({'mode':name,'retained':1159,'prior_stages_exact':True,'actual':len(actual),'current_sha256':sha(current)})
a.out.write_text(json.dumps({'status':'passed','comparisons':records,'e2e':e2e,'full_goal_complete':False},indent=2)+'\n')
