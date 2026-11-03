from pathlib import Path
import os,subprocess,json,hashlib
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';D=E/'general7-main-candidate-v1/current8f-full-reverse-inventory-v1';P=E/'892-joint-current-context-v2/package';tool='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake';target='FV.Backend.Proof.IselCtlTryF';records=[]
for label,args in [('current-key',['--json','query','--no-build','+'+target+':depHash']),('full-normal',['build','--no-build',target])]:
 r=subprocess.run([tool,*args],cwd=P,env=dict(os.environ,LAKE_RESTORE_ARTIFACTS='false'),capture_output=True,text=True);f=D/('IselCtlTryF-P-'+label+'-v1.log');f.write_text(r.stdout+'\nSTDERR\n'+r.stderr);records.append({'label':label,'exit':r.returncode,'stdout':r.stdout if label=='current-key' else None,'log_sha256':hashlib.sha256(f.read_bytes()).hexdigest()});print(label,r.returncode,flush=True)
(D/'IselCtlTryF-P-diagnostic-v1.json').write_text(json.dumps({'scope':'read-only diagnosis; no reuse','records':records},indent=2)+'\n')
