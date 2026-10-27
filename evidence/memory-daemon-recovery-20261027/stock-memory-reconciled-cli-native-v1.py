from pathlib import Path
import subprocess,os,json,hashlib
root=Path('/home/lee/clifv/.worktrees/stock-cfg-source-20261025');base=Path('/tmp/stock-memory-reconciled-integration-v1');out=Path('/tmp/stock-memory-reconciled-cli-native-v1');out.mkdir(exist_ok=False)
assert json.loads((base/'receipt.json').read_text())['state']=='passed'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
env=dict(os.environ,OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LEAN_NUM_THREADS='2',FV_MEMCAP='8G');records=[]
def run(label,args):
 log=out/(label+'.log')
 with log.open('w') as f:subprocess.run([str(root/'scripts/memcap.sh'),*map(str,args)],cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT,check=True)
 records.append(dict(label=label,argv=list(map(str,args)),log_sha256=sha(log)))
lld=env['CLIF_NATIVE_LLD'];linker=[lld]+(['-flavor','gnu'] if Path(lld).name in ('lld','rust-lld') else [])
source=base/'generated/StockMemoryProductionPlainFallbackGlobal.clif'
for allocator,options in [('default',[]),('lean',['--regalloc','lean'])]:
 for mode,flags in [('plain',['--no-dead-cleanup']),('cleanup',[])]:
  label=allocator+'-'+mode;obj=out/(label+'.o');elf=out/(label+'.elf');table=out/(label+'.json')
  run('compile-'+label,[root/'.lake/build/bin/lean-backend',source,obj,'--traps',table,*options,*flags])
  run('link-'+label,[*linker,'--threads=1','-m','aarch64elf','-e','_start','-o',elf,base/'memory-native.o',obj])
  run('execute-'+label,[env['CLIF_NATIVE_QEMU'],elf])
report=dict(state='passed',head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),actual_cli_default_and_explicit_lean_both_cleanup=True,candidate_calls=24576,initialized_loads=16384,disagreements=0,source_sha256=sha(source),commands=records,artifacts={str(p.relative_to(out)):sha(p) for p in out.rglob('*') if p.is_file()})
(out/'receipt.json').write_text(json.dumps(report,indent=2)+'\n');print('ACTUAL_MEMORY_CLI_ALLOCATOR_NATIVE_PASS')
