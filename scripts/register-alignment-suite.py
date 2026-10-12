#!/usr/bin/env python3
"""Paired numbering-only check against complete archived stock artifacts."""
import argparse,concurrent.futures,importlib.util,json,os,pathlib,shlex,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
spec=importlib.util.spec_from_file_location('comparison',ROOT/'scripts/stock-compiler-compare.py');stock=importlib.util.module_from_spec(spec);spec.loader.exec_module(stock)
def main():
 p=argparse.ArgumentParser();p.add_argument('comparison',type=pathlib.Path);p.add_argument('output',type=pathlib.Path);p.add_argument('--backend',required=True);p.add_argument('--oracle',required=True);p.add_argument('--mode',choices=['reverse_temps','schedule','wrapper'],default='reverse_temps');p.add_argument('--tracer');p.add_argument('--aligned-backend');a=p.parse_args();a.output=a.output.resolve();a.output.mkdir(parents=True,exist_ok=True)
 wrapper=a.output/'oracle';wrapper.write_text('#!/bin/sh\nexec '+shlex.quote(sys.executable)+' '+shlex.quote(str(ROOT/'scripts/register-alignment-probe.py'))+' --oracle "$@"\n');wrapper.chmod(0o755)
 report=json.loads((a.comparison/'results.json').read_text());tasks=[]
 for c in report['tests']:
  for v in c['variants']:
   directory=a.comparison/'files'/c['test'].removesuffix('.clif')
   for j,contract in enumerate(v['lean_compilations']):
    if not contract['contract_verified']:continue
    rows=[r for r in v['functions_compared'] if r.get('index') in contract['function_indices'] and r['status'] in ['different_code_artifact','identical_code_artifact']]
    if rows:tasks.append((c,v,j,directory,rows))
 def one(task):
  c,v,j,directory,rows=task
  assert stock.repeat_check(directory/'stock'/f"variant-{v['index']}",directory/'stock-repeat'/f"variant-{v['index']}",v)
  source=directory/f"variant-{v['index']}"/f'compilation-{j}';dest=a.output/c['test'].removesuffix('.clif')/f"{v['index']}-{j}";dest.mkdir(parents=True,exist_ok=True);out=[]
  for mode in ['baseline',a.mode]:
   d=dest/mode;env={**os.environ,'LEAN_REGALLOC':a.oracle if mode in ['baseline','wrapper'] else str(wrapper)}
   if mode not in ['baseline','wrapper']:
    env.update(ALIGNMENT_MODE=mode,ALIGNMENT_ORACLE=a.oracle)
    if mode=='schedule':
     trace=dest/'trace.json'
     try:
      subprocess.run([a.tracer,str(source/'input.clif'),str(trace),'--stock-schedule'],check=True,capture_output=True,timeout=60)
     except (subprocess.CalledProcessError,subprocess.TimeoutExpired):trace.write_text('{"functions":[]}')
     env['ALIGNMENT_TRACE_JSON']=str(trace)
   backend=a.aligned_backend if mode=='wrapper' else a.backend
   cmd=[backend,str(source/'input.clif'),str(d/'program.o'),'--stock-config',str(source/'stock-config.json'),'--config-receipt',str(dest/(mode+'-receipt.json')),'--dump',str(d/'dump')]
   d.mkdir(exist_ok=True);proc=subprocess.run(cmd,env=env,capture_output=True,text=True);(dest/(mode+'.stderr')).write_text(proc.stderr)
   assert stock.verify_receipt(json.loads((source/'stock-config.json').read_text()),json.loads((dest/(mode+'-receipt.json')).read_text()),(source/'input.clif').read_bytes()) is None
   for r in rows:
    meta_path=directory/'stock'/f"variant-{v['index']}"/f"{r['index']}.json";meta=json.loads(meta_path.read_text())
    actual=stock.compare_function(r['name'],(meta_path,meta),d,True,True);actual=stock.check_signing(actual,v,meta_path.with_suffix('.bin').read_bytes());actual['index']=r['index']
    out.append({'identity':[c['test'],v['index'],r['index'],r['name']],'mode':mode,'row':actual,'expected':r['status'],'exit':proc.returncode})
  return out
 results=[]
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
  for n,result in enumerate(pool.map(one,tasks),1):
   results.extend(result)
   if n%25==0:print('groups',n,'/',len(tasks),flush=True)
 baseline={tuple(r['identity']):r for r in results if r['mode']=='baseline'};candidate={tuple(r['identity']):r for r in results if r['mode']==a.mode}
 gains=[];lost=[];rejects=[];baseline_drift=[]
 for key,b in baseline.items():
  if b['row']['status']!=b['expected']:baseline_drift.append(list(key))
  new=candidate[key]['row']['status']
  if b['row']['status']!='identical_code_artifact' and new=='identical_code_artifact':gains.append(list(key))
  if b['row']['status']=='identical_code_artifact' and new!='identical_code_artifact':lost.append(list(key))
  if new not in ['identical_code_artifact','different_code_artifact']:rejects.append(list(key))
 summary={'schema':1,'archived_commit':'bc3a34c','mode':a.mode,'groups':len(tasks),'compared':len(baseline),'baseline_exact':sum(x['row']['status']=='identical_code_artifact' for x in baseline.values()),'candidate_exact':sum(x['row']['status']=='identical_code_artifact' for x in candidate.values()),'gained':gains,'lost':lost,'new_rejections':rejects,'baseline_status_drift':baseline_drift,'rows':results}
 (a.output/'results.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:(len(v) if isinstance(v,list) else v) for k,v in summary.items() if k!='rows'}),flush=True)
if __name__=='__main__':main()
