from pathlib import Path
import json,hashlib,subprocess,re
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';P=E/'direct-call-production-class-packet-v1';V=B/'.worktrees/stock-extending-production-20261031';ref='90c51c880b9d614f7c5f9730b8363a6321c840de'
raw=subprocess.check_output(['git','ls-tree','-r',ref],cwd=B,text=True);tree={line.split('\t',1)[1]:line.split()[2] for line in raw.splitlines()}
owned={str(f.relative_to(P)):f.read_bytes() for prefix in ['FV','FVTest'] for f in (P/prefix).rglob('*.lean')};accepted=E/'direct-call-result-packet-v1';extra={str(f.relative_to(accepted)):f.read_bytes() for f in (accepted/'FV').rglob('*.lean')};overlays=extra|owned
sources={};imports={};todo=list(owned)+["FV/E2E/ProductionBoundaryWitness.lean"];origins={};missing=[];changed=[]
def blob(data):return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
while todo:
 name=todo.pop()
 if name in sources:continue
 if name in overlays:data=overlays[name];origins[name]='owned' if name in owned else 'accepted_binding'
 else:
  assert name in tree,('missing from immutable production',name)
  existing=V/name
  if existing.exists() and blob(existing.read_bytes())==tree[name]:data=existing.read_bytes();origins[name]='carrier_source_exact'
  else:
   data=subprocess.check_output(['git','cat-file','blob',tree[name]],cwd=B);assert blob(data)==tree[name];origins[name]='immutable_production_blob'
   (changed if existing.exists() else missing).append(name)
 sources[name]=data;deps={m.replace('.','/')+'.lean' for m in re.findall(r'^import\s+([\w.]+)',data.decode(),re.M) if m.startswith(('FV.','FVTest.'))};imports[name]=deps;todo.extend(deps-sources.keys())
configs={}
for name in ['lakefile.toml','lakefile.lean','lake-manifest.json','lean-toolchain']:
 if name in tree:
  data=subprocess.check_output(['git','cat-file','blob',tree[name]],cwd=B);assert blob((V/name).read_bytes())==tree[name];configs[name]=tree[name]
assert len(configs)==3
receipt=dict(status='source_inventory_declared_not_compiled',immutable_production=ref,carrier_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=V,text=True).strip(),project_source_count=len(sources),configs=configs,missing_in_carrier=sorted(missing),changed_in_carrier=sorted(changed),origins=origins,source_hashes={n:hashlib.sha256(d).hexdigest() for n,d in sources.items()},git_blobs={n:tree[n] for n in sources if n not in overlays},current_main_validation=False)
(P/'production-context-inventory-v20.json').write_text(json.dumps(receipt,indent=2)+'\n');print('Project sources',len(sources),'missing',len(missing),'changed',len(changed))
