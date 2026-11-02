from pathlib import Path
import importlib.util,json,os,subprocess,hashlib
sp=importlib.util.spec_from_file_location('b','/tmp/stock-outcome-upstream-lake-serial-build.py');b=importlib.util.module_from_spec(sp);sp.loader.exec_module(b);_,mods,deps=b.load_modules(Path.cwd());plan=json.load(open('/tmp/stock-outcome-plan.json'));prof=b.load_profile([Path('scripts/lake-module-peaks.tsv'),Path('.lake/lake-module-peaks.tsv')]); known_heavy={n for n,v in prof.items() if ((int(v[0]*1.2)+(1<<29)+(1<<30)-1)//(1<<30))>10}; blocked={'FV.Backend.Proof.DefGenTab'}|known_heavy
while True:
 n=blocked|{m for m,d in deps.items() if set(d)&blocked}
 if n==blocked:break
 blocked=n
roots=sorted(set(plan['affected'])-blocked);closure=set(roots)
while True:
 n=closure|{d for m in closure for d in deps.get(m,[])}
 if n==closure:break
 closure=n
assert not closure & ({'FV.Backend.Proof.DefGenTab'}|known_heavy),sorted(closure & ({'FV.Backend.Proof.DefGenTab'}|known_heavy))
out=Path('/tmp/stock-outcome-independent-light');out.mkdir(exist_ok=True);only=out/'targets.txt';only.write_text('\n'.join(roots)+'\n');print('Independent affected targets',len(roots),'remaining blocked',len(set(plan['affected'])&blocked),flush=True);e=os.environ.copy();e.update(json.load(open('/tmp/stock-div-release-env.json')));e['FV_MEMCAP']='6G'
with open('/tmp/stock-outcome-independent-light-runner.log','w') as f:r=subprocess.run(['python3','/tmp/stock-outcome-upstream-lake-serial-build.py','--root',str(Path.cwd()),'--budget','10G','--max-jobs','1','--default-cap','6G','--max-cap','16G','--out',str(out),'--only',str(only),*roots],env=e,stdout=f,stderr=subprocess.STDOUT)
Path('/tmp/stock-outcome-independent-light-check.json').write_text(json.dumps({'head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'exit':r.returncode,'target_count':len(roots),'excluded_active_module_and_dependents':sorted(set(plan['affected'])&blocked),'scheduler_source':'Unmodified516 ef499aca batch helper with actual9f16 memory wrapper','scope':'Independent affected normal keys; excludes active DefGenTab and every dependent before any probe/restore. Combined caps15GiB/max2.'},indent=2)+'\n');print(r.returncode)
