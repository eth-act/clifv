from pathlib import Path
import json,os,subprocess,importlib.util,math
sp=importlib.util.spec_from_file_location('b','scripts/lake-serial-build.py');b=importlib.util.module_from_spec(sp);sp.loader.exec_module(b);_,mods,deps=b.load_modules(Path.cwd());prof=b.load_profile([Path('scripts/lake-module-peaks.tsv'),Path('.lake/lake-module-peaks.tsv')]);heavy={n for n,(peak,_) in prof.items() if math.ceil((peak*1.2+2**29)/2**30)>13};cold=set(json.load(open('/tmp/stock-outcome-witness-heavy-cold.json')));blocked=heavy&cold
while True:
 n=blocked|{m for m,ds in deps.items() if set(ds)&blocked}
 if n==blocked:break
 blocked=n
applied=json.load(open('/tmp/stock-outcome-value-boundary-applied.json'));allroots={p[:-5].replace('/','.') for p in applied['unchanged_body_sha256'] if p.startswith('FV/Backend/Proof/Stock')};roots=sorted(allroots-blocked);assert roots
closure=set(roots)
while True:
 n=closure|{x for m in closure for x in deps.get(m,[])}
 if n==closure:break
 closure=n
assert not closure & (heavy&cold)
assert not any(x.startswith('FV.Opt.Proof.Rule') for x in closure)
Path('/tmp/stock-outcome-witness-chunk-plan.json').write_text(json.dumps({'roots':roots,'deferred_larger_roots':sorted(allroots-set(roots)),'closed_imports':len(closure),'source_head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'budget':'13GiB/max1 alongside3GiB fixed check module; every required import fits13; old optimizer worker exited'},indent=2)+'\n');print('Witness targets',len(roots),'deferred',len(allroots-set(roots)),flush=True)
E=os.environ.copy();E.update(json.load(open('/tmp/stock-div-release-env.json')));E['FV_MEMCAP']='6G'
with open('/tmp/stock-outcome-witness-chunk-runner.log','w') as f:r=subprocess.run(['python3','scripts/lake-serial-build.py','--budget','13G','--max-jobs','1','--default-cap','6G','--max-cap','16G','--out','/tmp/stock-outcome-witness-chunk',*roots],env=E,stdout=f,stderr=subprocess.STDOUT)
Path('/tmp/stock-outcome-witness-chunk-check.json').write_text(json.dumps({'head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'exit':r.returncode,'target_count':len(roots),'scope':'Actual import-only legacy Stock witness normal build and complete required imports; deferred larger targets remain for final affected pass.'},indent=2)+'\n');print(r.returncode)
