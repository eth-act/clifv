from pathlib import Path
import json,hashlib,resource,datetime,gc
from identity_checks import require_production_compiled
O=Path(__file__).resolve().parent;reference=O.parent/'captured-copy-production-official-vectors-v1/results.json';from stream_comparison import read_comparison
_,rows,_=read_comparison(reference);assert len(rows)==4501
unchanged=require_production_compiled(rows,rows);assert unchanged['prior_compiled_identities']==1997
key=next(key for key,row in rows.items() if row['status']=='different_code_artifact');mutated=dict(rows);mutated[key]={'status':'lean_unsupported'};assert set(mutated)==set(rows)
try:require_production_compiled(rows,mutated)
except AssertionError as error:rejected=str(error)
else:raise AssertionError('The compiled-to-unsupported mutation must fail')
result={'status':'passed','unchanged_reference':unchanged,'prior_different_outputs':sum(r['status']=='different_code_artifact' for r in rows.values()),'mutation_identity':list(key),'mutated_status':'lean_unsupported','stage_tuple_identity_preserved':True,'mutation_rejected':True,'diagnostic':rejected,'reference_sha256':hashlib.sha256(reference.read_bytes()).hexdigest(),'max_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'no_Lean_build':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(O/'compiled-preservation-harness-receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['status','unchanged_reference','prior_different_outputs','stage_tuple_identity_preserved','mutation_rejected','max_rss_kib']}))
