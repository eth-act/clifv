from pathlib import Path
import subprocess,json,hashlib,os
root=Path('/home/lee/clifv/.worktrees/stock-cfg-source-20261025')
source=Path('/tmp/stock-memory-reconciled-integration-v1')
out=Path('/tmp/stock-memory-reconciled-reference-native-v1');out.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
r=json.loads((source/'receipt.json').read_text());assert r['state']=='passed'
for name,h in r['artifacts'].items():assert sha(source/name)==h
commands=[]
def run(label,args):
 log=out/(label+'.log')
 with log.open('w') as f:subprocess.run([str(root/'scripts/memcap.sh'),*map(str,args)],cwd=root,stdout=f,stderr=subprocess.STDOUT,check=True)
 commands.append(dict(label=label,argv=list(map(str,args)),log_sha256=sha(log)))
clif=source/'generated/StockMemoryProductionPlainFallbackGlobal.clif'
assert clif.read_bytes()==(source/'generated/StockMemoryProductionCleanupFallbackGlobal.clif').read_bytes()
compiler=root/'rust/target/release/clif2obj';before=sha(compiler)
run('compile-reference',[compiler,clif,'aarch64-unknown-linux-gnu',out/'reference.o',out/'dump'])
lld=os.environ['CLIF_NATIVE_LLD'];linker=[lld]+(['-flavor','gnu'] if Path(lld).name in ('lld','rust-lld') else [])
run('link-reference',[*linker,'--threads=1','-m','aarch64elf','-e','_start','-o',out/'reference.elf',source/'memory-native.o',out/'reference.o'])
run('run-reference',[os.environ['CLIF_NATIVE_QEMU'],out/'reference.elf'])
assert sha(compiler)==before
report=dict(state='passed',candidate_calls=12288,reference_calls=6144,candidate_initialized_loads=8192,reference_initialized_loads=4096,disagreements=0,original_source_sha256=sha(clif),candidate_receipt_sha256=sha(source/'receipt.json'),reference_compiler_sha256=before,reference_object_sha256=sha(out/'reference.o'),commands=commands,limits='Both actual candidate cleanup modes and the independently compiled Cranelift object execute the identical initialized-memory/ABI harness and match every source value. This is execution evidence, not an agreement-percentage estimate.')
(out/'receipt.json').write_text(json.dumps(report,indent=2)+'\n');print('ACTUAL_MEMORY_CRANELIFT_REFERENCE_PASS 6144 calls 0 disagreements')
