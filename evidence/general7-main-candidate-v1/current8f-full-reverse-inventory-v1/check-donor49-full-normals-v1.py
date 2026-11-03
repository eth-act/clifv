from pathlib import Path
import json,subprocess,os,hashlib
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';D=E/'general7-main-candidate-v1/current8f-full-reverse-inventory-v1'
roots={'P':E/'892-joint-current-context-v2/package','R':E/'direct-call-store-live-packet-v1/validation-package-v1'}
d=json.loads((D/'donor49-source-closure-classification-v1.json').read_text());groups={'P':[],'R':[]}
for row in d['rows']:
 valid=[x for x in row['closure_checks'] if x['source_closure_matches']]
 if valid: groups[valid[0]['owner']].append(row['target'])
results=[]
for owner,targets in groups.items():
 if not targets:continue
 f=D/('donor49-'+owner+'-full-normal-v1.log')
 with f.open('w') as out:r=subprocess.run(['/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake','build','--no-build',*targets],cwd=roots[owner],env=dict(os.environ,LAKE_RESTORE_ARTIFACTS='false'),stdout=out,stderr=subprocess.STDOUT)
 results.append({'owner':owner,'targets':targets,'exit':r.returncode,'log_sha256':hashlib.sha256(f.read_bytes()).hexdigest()});print(owner,len(targets),'normal exit',r.returncode,flush=True)
(D/'donor49-full-normal-results-v1.json').write_text(json.dumps({'scope':'full source match, actual native keys and group normals; no reuse or acceptance yet','records':results},indent=2)+'\n')
raise SystemExit(0 if all(x['exit']==0 for x in results) else 3)
