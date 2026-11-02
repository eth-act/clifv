from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,datetime
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';Q=E/'direct-call-arithmetic-live-packet-v1';P=E/'direct-call-production-class-packet-v1';R=Q/'validation-package-v1';J=E/'892-joint-current-context-v2/package';base=(Q/'production-actual-main-base-v1.txt').read_text().strip();prior='90c51c880b9d614f7c5f9730b8363a6321c840de';L=Q/'live-production-context-v1';L.mkdir();assert not (R/'.lake/build').exists()
pm=json.loads((P/'reviewed-production-complete-v1/manifest.json').read_text());shared=json.loads((Q/'live-shared-inventory-v1.json').read_text());freeze=['FV/E2E/CompiledSemanticABI.lean','FV/E2E/CompiledSemanticReturnPins.lean','FV/E2E/CompiledProgramReturnPins.lean']
for n in freeze:assert hashlib.sha256((Q/n).read_bytes()).hexdigest()==shared[n]['candidate_sha256'],('frozen constructor changed',n)
sources={};dag={};origins={};todo=['FVTest/Backend/Main.lean','FVTest/Link/LeanLinkMain.lean','FVTest/E2E/LinkCheckMain.lean','FV/E2E/LiveCallProductionExec.lean','FV/E2E/LiveCallProductionSelection.lean']
while todo:
 n=todo.pop()
 if n in sources:continue
 if (Q/n).exists():data=(Q/n).read_bytes();origin='owned live candidate'
 elif (P/n).exists():
  data=(P/n).read_bytes();origin='immutable prior49-source packet';assert hashlib.sha256(data).hexdigest()==pm[n],n
 else:
  found=subprocess.run(['git','rev-parse','--verify',base+':'+n],cwd=B,text=True,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
  if found.returncode==0:blob=found.stdout.strip();origin='actual main '+base
  else:blob=subprocess.check_output(['git','rev-parse',prior+':'+n],cwd=B,text=True).strip();origin='canonical892 provider from immutable production '+prior
  data=subprocess.check_output(['git','cat-file','blob',blob],cwd=B)
 sources[n]=data;origins[n]=origin;dag[n]=[x.replace('.','/')+'.lean' for x in re.findall(r'^import\s+([\w.]+)',data.decode(),re.M) if x.startswith(('FV.','FVTest.'))];todo.extend(dag[n])
configs={};original={}
for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']:
 data=subprocess.check_output(['git','show',base+':'+n],cwd=B);original[n]=hashlib.sha256(data).hexdigest()
 if n=='lakefile.toml':
  assert b'weakLeanArgs = [' in data;data=data.replace(b'weakLeanArgs = [',b'weakLeanArgs = ["-j1",',1)
 (R/n).write_bytes(data);configs[n]=hashlib.sha256(data).hexdigest();(L/n).write_bytes(data)
# Copy every candidate source into its immutable evidence context before any kernel work.
for n,data in sources.items():
 d=R/n;d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(data)
 if origins[n]=='owned live candidate' or origins[n]=='immutable prior49-source packet':
  d=L/'sources'/n;d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(data)
for p in Q.glob('scripts/audit/stock-live-call-*.lean'):
 d=R/p.relative_to(Q);d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(p.read_bytes())
keys={}
def key(n):
 if n not in keys:keys[n]=hashlib.sha256(json.dumps([configs,hashlib.sha256(sources[n]).hexdigest(),[(d,key(d)) for d in sorted(dag[n])]],sort_keys=True).encode()).hexdigest()
 return keys[n]
for n in sources:key(n)
jc=json.loads((E/'892-joint-current-context-v2/context.json').read_text());same={}
def equal(n):
 if n not in same:same[n]=(jc['source_hashes'].get(n)==hashlib.sha256(sources[n]).hexdigest() and all(equal(d) for d in dag[n]))
 return same[n]
# Only weak build job arguments differ; the accepted foundation already checked their native-key compatibility.
for n in ['lean-toolchain','lake-manifest.json']:assert (J/n).read_bytes()==(R/n).read_bytes(),n
assert (J/'lakefile.toml').read_bytes().replace(b'"-j2",',b'')==(R/'lakefile.toml').read_bytes().replace(b'"-j1",',b'')
borrowed={};affected=[];absent=[]
for n in sources:
 if not equal(n):affected.append(n);continue
 stem=Path(n).with_suffix('');o=J/'.lake/build/lib/lean'/Path(str(stem)+'.olean')
 if not o.exists():absent.append(n);continue
 for area in ['lib/lean','ir']:
  p=J/'.lake/build'/area/stem
  for src in p.parent.glob(p.name+'.*'):
   if not src.is_file():continue
   dest=R/src.relative_to(J);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest);borrowed[str(dest.relative_to(R))]=hashlib.sha256(dest.read_bytes()).hexdigest()
state=dict(status='materialized_staged_integration_context',base=base,source_context='actual main plus canonical892, immutable P49, and live candidate overlays; constructor boundary unresolved; NOT publication validation',source_hashes={n:hashlib.sha256(d).hexdigest() for n,d in sources.items()},imports=dag,origins=origins,dependency_keys=keys,original_configs=original,effective_configs=configs,borrowed_artifacts=borrowed,affected=sorted(affected),unchanged_missing_outputs=absent,frozen_constructor_hashes={n:hashlib.sha256(sources[n]).hexdigest() for n in freeze},proofslot_grant='live-production-2G',native_cache=str(E/'892-current-main-context-v1/package/.lake/ci-cache'),no_live_package_writes=True,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(L/'context.json').write_text(json.dumps(state,indent=2)+'\n');print('context',len(sources),'sources;',len(affected),'affected;',len(absent),'unchanged missing;',len(borrowed),'copied artifacts',flush=True)
