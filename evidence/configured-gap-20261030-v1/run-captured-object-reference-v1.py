from pathlib import Path
import os,json,subprocess,hashlib,datetime,sys,importlib.util
b=Path('/home/lee/clifv');r=b/'.worktrees/stock-cfg-source-20261025';e=b/'.git/agent-evidence/stock-memory-20261029';out=e/'captured-object-reference-v1';out.mkdir(exist_ok=False);env=dict(os.environ);env.update(json.loads((e/'author-env-v1.json').read_text()));env.update(FV_MEMCAP='1G',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',LEAN_NUM_THREADS='1',RAYON_NUM_THREADS='1');env.pop('BLESS',None);env.pop('RUST_LOG',None)
sys.path.insert(0,str(r/'scripts'));from byte_compare import ELF;from stock_common import comparison
spec=importlib.util.spec_from_file_location('stock_compare',r/'scripts/stock-compiler-compare.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();binary=r/'rust/target/debug/prejit-export';actual=sha(binary);known={json.loads((e/'delivery-reference-preparation-v1.json').read_text())['exporter_sha256'],json.loads((e/'delivery-official-vectors-v1/results.json').read_text())['binary_hashes']['tools/prejit-export/target/debug/prejit-export']};assert actual in known,('Unverified exporter',actual)
inputs=json.loads((e/'captured-real-inputs-state-v1.json').read_text());rows=[]
try:
 for i,record in enumerate(inputs['records'][::2]):
  original=Path(record['path']);assert sha(original)==record['source_sha256'];directory=out/str(i);directory.mkdir();wrapper=directory/'compile.clif';wrapper.write_bytes(b'test compile\n'+original.read_bytes())
  for label in ['first','repeat']:
   with (directory/(label+'.log')).open('w') as log:done=subprocess.run(['nice','-n','15',str(r/'scripts/memcap.sh'),str(binary),str(wrapper),str(directory/label),'aarch64-unknown-linux-gnu','--all-stages'],cwd=r,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=60)
   assert done.returncode==0,(label,done.returncode)
  manifest=json.loads((directory/'first/manifest.json').read_text());variant=manifest['variants'][0];stockdir=directory/'first'/('variant-'+str(variant['index']));repeatdir=directory/'repeat'/('variant-'+str(variant['index']));assert module.repeat_check(stockdir,repeatdir,variant)
  artifacts=module.artifacts(stockdir,variant);assert len(artifacts)==1;path,metadata=next(iter(artifacts.values()));reference=path.with_suffix('.bin').read_bytes()
  for cleanup in [False,True]:
   obj=e/'captured-real-inputs-v1'/(str(i)+('-cleanup' if cleanup else '-plain')+'.o');elf=ELF(obj);symbol,code=elf.function(record['function']);relocs=elf.function_relocations(symbol,{});assert not metadata['relocations'] and not relocs
   compared=comparison(reference,code,metadata['relocations'],relocs);rows.append(dict(function=record['function'],cleanup=cleanup,original_path=str(original),original_sha256=sha(original),wrapper_sha256=sha(wrapper),stock_bytes=reference.hex(),lean_bytes=code.hex(),comparison=compared,stock_metadata=metadata,stock_repeatable=True,settings_contract_verified=False,compiler_source='preserved6e4 plus2dbedd3b; existing default compiler objects'))
  assert sha(original)==record['source_sha256']
 report=dict(status='passed',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),rows=rows,code_and_relocations_exact=sum(x['comparison']['exact_code_and_relocations'] for x in rows),cases=len(rows),exporter_sha256=actual,input_adaptation='A separate wrapper adds only test compile; original source and all original flags stay unchanged.',scope='Raw default-production function bytes and relocations against original-settings Cranelift exports. Settings contract and full artifact equivalence are NOT established. No official-suite gain is claimed.')
except BaseException as error:
 report=dict(status='failed',error=repr(error),rows=rows);raise
finally:(out/'receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='rows'}))
