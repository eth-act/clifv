"""Execute the unchanged original object and settings contracts against current tools."""
from pathlib import Path
import argparse,os,json,hashlib,subprocess,sys,importlib.util
O=Path(__file__).resolve().parent;E=O.parent;p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();root=a.root.resolve();out=a.output;out.mkdir();env=dict(os.environ,FV_ROOT=str(root),PYTHONDONTWRITEBYTECODE='1');env.pop('BLESS',None);env.pop('FV_PIPELINE_T',None)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
sources=json.loads((E/'memory-captured-inventory-current/receipt.json').read_text())['sources'];assert len(sources)==4543 and all(sha(p)==h for p,h in sources.items())
reference=json.loads((E/'captured-object-reference-v1/receipt.json').read_text());previous=json.loads((E/'captured-real-inputs-state-v5.json').read_text());expected={(x['function'],x['cleanup']):x for x in reference['rows']};assert len(previous['records'])==len(expected)==8
sys.path.insert(0,str(root/'scripts'));from byte_compare import ELF
from stock_common import comparison
spec=importlib.util.spec_from_file_location('current_comparison',root/'scripts/stock-compiler-compare.py');compare=importlib.util.module_from_spec(spec);spec.loader.exec_module(compare)
records=[]
def run(label,args,extra=None,expected_exit=0):
 with (out/(label+'.log')).open('w') as log:rc=subprocess.call(list(map(str,args)),cwd=root,env=dict(env,**(extra or {})),stdout=log,stderr=subprocess.STDOUT)
 records.append({'id':label,'argv':list(map(str,args)),'exit':rc,'expected_exit':expected_exit});(out/'progress.json').write_text(json.dumps(records,indent=2)+'\n');assert rc==expected_exit,(label,rc)
for index,row in enumerate(previous['records']):
 source=Path(row['path']);assert sha(source)==row['source_sha256'];obj=out/f'{index}.o';allocation=out/f'{index}.allocation.json';trace=out/f'{index}.trace.json';cleanup=[] if row['cleanup'] else ['--no-dead-cleanup']
 run('capture-'+str(index),[root/'.lake/build/bin/lean-backend',source,obj,'--regalloc','regalloc2',*cleanup],{'LEAN_REGALLOC_KEEP':str(allocation)})
 run('trace-'+str(index),[root/'.lake/build/bin/lean-backend-lowering-trace',source,trace,'--stock-schedule',*cleanup])
 actual=json.loads(allocation.read_text())['functions'];reported=json.loads(trace.read_text())['functions'];assert len(actual)==len(reported)==1 and reported[0]['status']=='lowered';lowered=reported[0]['lowering'];assert lowered['allocator_input']==actual[0]
 if not row['cleanup']:assert lowered['allocation_selected']==lowered['stock_schedule']['selected']
 elf=ELF(obj);symbol,code=elf.function(row['function']);relocs=elf.function_relocations(symbol,{});prior=expected[(row['function'],row['cleanup'])];result=comparison(bytes.fromhex(prior['stock_bytes']),code,prior['stock_metadata']['relocations'],relocs);assert result['exact_code_and_relocations'],result
variants={}
for manifest in (E/'captured-object-reference-v1').glob('*/first/manifest.json'):
 for variant in json.loads(manifest.read_text())['variants']:
  for name in variant['functions']:variants[name.removeprefix('%')]=variant
for i,row in enumerate(reference['rows']):
 source=Path(row['original_path']);assert sha(source)==row['original_sha256'];request=compare.request_for(variants[row['function']],source.read_bytes());requested=out/f'{i}.request.json';requested.write_text(json.dumps(request,indent=2)+'\n');receipt=out/f'{i}.rejected.receipt.json';obj=out/f'{i}.rejected.o';allocation=out/f'{i}.rejected.allocator.json'
 run('original-rejection-'+str(i),[root/'.lake/build/bin/lean-backend',source,obj,'--regalloc','regalloc2','--stock-config',requested,'--config-receipt',receipt,*([] if row['cleanup'] else ['--no-dead-cleanup'])],{'LEAN_REGALLOC_KEEP':str(allocation)},3)
 actual=json.loads(receipt.read_text());old=json.loads((E/f'configured-original-captures-v1/{i}-native-baseline.receipt.json').read_text());assert actual==old and actual['request']==request and actual['configuration_accepted'] is False;assert not obj.exists() and not allocation.exists()
assert all(sha(p)==h for p,h in sources.items())
(out/'receipt.json').write_text(json.dumps({'status':'passed','source_hashes_exact':4543,'original_objects_exact':8,'settings_rejections_exact':8,'required_rejection_exit':3,'no_rejected_object_or_allocation':True,'commands':records,'full_goal_complete':False},indent=2)+'\n')
