from pathlib import Path
import json,re,subprocess,hashlib
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';Q=E/'direct-call-arithmetic-live-packet-v1';P=E/'direct-call-production-class-packet-v1';R=Q/'validation-package-v1';s=json.loads((Q/'standalone-class-source-v1/manifest.json').read_text());base=s['base'];prior='90c51c880b9d614f7c5f9730b8363a6321c840de';todo=['FVTest/Backend/Main.lean','FVTest/Link/LeanLinkMain.lean','FVTest/E2E/LinkCheckMain.lean','FV/E2E/LiveCallProductionExec.lean','FV/E2E/LiveCallProductionSelection.lean'];sources={};imports={};origins={};blobs={}
while todo:
 n=todo.pop()
 if n in sources:continue
 if (Q/n).exists():data=(Q/n).read_bytes();origin='live candidate'
 elif (P/n).exists():data=(P/n).read_bytes();origin='complete previous49-source packet'
 else:
  found=subprocess.run(['git','rev-parse','--verify',base+':'+n],cwd=B,text=True,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
  if found.returncode==0:blob=found.stdout.strip();origin='current main'
  else:blob=subprocess.check_output(['git','rev-parse',prior+':'+n],cwd=B,text=True).strip();origin='missing canonical892 provider from immutable prior production90c51c88'
  data=subprocess.check_output(['git','cat-file','blob',blob],cwd=B);blobs[n]=blob
 sources[n]=hashlib.sha256(data).hexdigest();origins[n]=origin;imports[n]=[x.replace('.','/')+'.lean' for x in re.findall(r'^import\s+([\w.]+)',data.decode(),re.M) if x.startswith(('FV.','FVTest.'))];todo.extend(imports[n])
changed={n for n,h in sources.items() if not (R/n).exists() or hashlib.sha256((R/n).read_bytes()).hexdigest()!=h};closure=set(changed)
while True:
 extra={n for n,deps in imports.items() if set(deps)&closure}-closure
 if not extra:break
 closure|=extra
missing=[n for n in sources if not (R/'.lake/build/lib/lean'/Path(n).with_suffix('.olean')).exists()]
state=dict(status='source_inventory_only_no_build',base=base,prior_production=prior,git_blobs=blobs,source_hashes=sources,origins=origins,imports=imports,changed_against_current_standalone=sorted(changed),reverse_importers_to_rebuild=sorted(closure),missing_outputs=missing,source_context='actual main84b with immutable prior49-source, declared missing canonical892 providers, and owned live candidate overlays; not publication validation')
(Q/'live-production-source-inventory-v2.json').write_text(json.dumps(state,indent=2)+'\n');print('complete production closure',len(sources),'sources;',len(changed),'changed/new;',len(closure),'affected;',len(missing),'missing outputs');print('missing canonical providers',sum('canonical892' in o for o in origins.values()))
