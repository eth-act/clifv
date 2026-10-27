from pathlib import Path
import json,hashlib,re,sys,subprocess,struct
root=Path('/home/lee/clifv/.worktrees/stock-cfg-source-20261025');sys.path.insert(0,str(root/'scripts'))
from byte_compare import ELF
base=Path('/tmp/stock-memory-reconciled-integration-v1');generated=base/'generated'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
r=json.loads((base/'receipt.json').read_text());assert r['state']=='passed'
for path,digest in r['artifacts'].items():assert sha(base/path)==digest,path
bindings=[];functions=[]
for proof in (generated/'Crates').glob('*.lean'):
 if proof.stem.startswith('StockMemoryProduction'):file=generated/(proof.stem+'.elf')
 elif proof.stem.startswith('MemoryCLI'):
  mode='Cleanup' if 'Cleanup' in proof.stem else 'Plain';file=generated/f'StockMemoryProduction{mode}FallbackGlobal.elf'
 else:continue
 data=file.read_bytes();chunks=re.findall(r'\((\d+),\s*Elf\.ofHex\s*"([0-9a-fA-F]*)"\)',proof.read_text());assert chunks,proof
 for offset,hexdata in chunks:
  chunk=bytes.fromhex(hexdata);offset=int(offset);assert data[offset:offset+len(chunk)]==chunk,(proof,offset)
 bindings.append(dict(proof=str(proof),proof_sha256=sha(proof),file=str(file),file_sha256=sha(file),excerpt_chunks=len(chunks)))
for mode,title in [('plain','Plain'),('cleanup','Cleanup')]:
 obj=ELF(generated/f'memory-{mode}.o');image=(generated/f'StockMemoryProduction{title}FallbackGlobal.elf').read_bytes()
 bundle=json.loads((generated/f'StockMemoryProduction{title}FallbackGlobal-bundle/bundle.json').read_text());addresses=dict(bundle['symbols'])
 h=struct.unpack_from('<16sHHIQQQIHHHHHH',image,0)
 segments=[struct.unpack_from('<IIQQQQQQ',image,h[5]+i*h[9]) for i in range(h[10])]
 for name in ['memory_load0','memory_load1','memory_retained']:
  symbol,ob=obj.function(name);address=addresses[name]
  matches=[seg for seg in segments if seg[0]==1 and seg[3]<=address and address+len(ob)<=seg[3]+seg[5]];assert len(matches)==1
  seg=matches[0];offset=seg[2]+address-seg[3];assert image[offset:offset+len(ob)]==ob,(mode,name)
  assert not obj.function_relocations(symbol,{}),(mode,name,'unexpected relocation')
  functions.append(dict(mode=mode,name=name,address=address,file_offset=offset,bytes_sha256=hashlib.sha256(ob).hexdigest()))
assert len(bindings)==10 and len(functions)==6
report=dict(state='passed',head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),compiled_proof_actual_elf_bindings=bindings,native_object_verified_elf_functions=functions,compiler_binary_sha256={name:sha(root/'.lake/build/bin'/name) for name in ['lean-backend','lean-link','link-check','stock-memory-linked']},source_tree_sha256=subprocess.check_output(['git','rev-parse','HEAD^{tree}'],cwd=root,text=True).strip())
Path('/tmp/stock-memory-reconciled-fixture-byte-binding-v1.json').write_text(json.dumps(report,indent=2)+'\n');print('ACTUAL_MEMORY_PROOF_ELF_NATIVE_BYTES_BOUND',len(bindings),len(functions))
