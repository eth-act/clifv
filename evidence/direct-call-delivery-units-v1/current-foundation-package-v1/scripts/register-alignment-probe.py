#!/usr/bin/env python3
"""Opt-in allocator-numbering experiment; never changes compiler defaults.

The saved Stock schedule is a candidate model, not a captured stock allocator.
Physical allocations returned by the oracle remain checked by the original Lean pipeline.
"""
import argparse,copy,hashlib,json,os,pathlib,re,shlex,subprocess,sys

def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def reg(s):return int(re.search(r'vreg (\d+)',s)[1])
def write(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')
def remap(f,m):
 n=len(f['vregs']);assert set(m)==set(range(n));assert len(set(m.values()))==n and all(type(x)==int and x>=0 for x in m.values())
 g=copy.deepcopy(f);classes=['i']*(max(m.values(),default=-1)+1)
 for old,new in m.items():classes[new]=f['vregs'][old]
 g['vregs']=''.join(classes)
 for b in g['blocks']:b['params']=[m[v] for v in b['params']]
 for i in g['insts']:
  for o in i['ops']:o['v']=m[o['v']]
  if 'args' in i:i['args']=[[m[v] for v in args] for args in i['args']]
 return g

def shape_map(old,new):
 mapping={};inverse={}
 def bind(a,b):
  if old['vregs'][a]!=new['vregs'][b] or mapping.get(a,b)!=b or inverse.get(b,a)!=a:raise ValueError('alias/class relation differs')
  mapping[a]=b;inverse[b]=a
 def visit(a,b):
  if isinstance(a,dict):
   if set(a)!=set(b):raise ValueError('allocator fields differ')
   for k in a:
    if k=='v':bind(a[k],b[k])
    elif k in ('params','args'):
     def refs(x,y):
      if len(x)!=len(y):raise ValueError('argument counts differ')
      for i,j in zip(x,y):
       if isinstance(i,list):refs(i,j)
       else:bind(i,j)
     refs(a[k],b[k])
    elif k!='vregs':visit(a[k],b[k])
  elif isinstance(a,list):
   if len(a)!=len(b):raise ValueError('instruction/operand counts differ')
   for x,y in zip(a,b):visit(x,y)
  elif a!=b:raise ValueError('instruction order/constraints/preferences differ')
 visit(old,new)
 nxt=len(new['vregs'])
 for v in range(len(old['vregs'])):
  if v not in mapping:mapping[v]=nxt;nxt+=1
 return mapping

def dense_map(old,trace):
 mapping={reg(x['reg']):reg(next(y['reg'] for y in trace['stock_schedule']['value_regs'] if y['value']==x['value'])) for x in trace['value_regs']}
 boundary=trace['initial_next_vreg'];base=trace['stock_schedule']['initial_next_vreg']
 for v in range(boundary,len(old['vregs'])):mapping[v]=base+v-boundary
 nxt=max(mapping.values(),default=191)+1
 for v in range(len(old['vregs'])):
  if v not in mapping:mapping[v]=nxt;nxt+=1
 return mapping

def reverse_map(f):
 source=set(v for b in f['blocks'] for v in b['params'])
 source.update(o['v'] for o in f['insts'][0]['ops'] if o['k']=='def')
 defs=[o['v'] for i in f['insts'] for o in i['ops'] if o['k']=='def' and o['v'] not in source]
 boundary=min(defs,default=len(f['vregs']))
 return {v:(v if v<boundary else boundary+len(f['vregs'])-1-v) for v in range(len(f['vregs']))}

def oracle():
 p=pathlib.Path(sys.argv[2]);request=json.loads(p.read_text());maps=json.loads(pathlib.Path(os.environ['ALIGNMENT_MAP']).read_text()) if os.environ.get('ALIGNMENT_MAP') else {}
 traces={}
 if os.environ.get('ALIGNMENT_TRACE_JSON'):
  traces={x['name'].lstrip('%'):x['lowering'] for x in json.loads(pathlib.Path(os.environ['ALIGNMENT_TRACE_JSON']).read_text()).get('functions',[]) if x.get('status')=='lowered'}
 for f in request['functions']:
  entry=maps.get(f['name'])
  if os.environ.get('ALIGNMENT_MODE')=='reverse_temps':entry={'input_sha256':digest(f),'mapping':reverse_map(f)}
  if os.environ.get('ALIGNMENT_MODE')=='schedule':
   try:entry={'input_sha256':digest(f),'mapping':shape_map(f,traces[f['name']]['stock_schedule']['allocator_input'])}
   except (KeyError,ValueError,IndexError,AssertionError):entry=None
  if entry:
   assert digest(f)==entry['input_sha256'],'request differs from measured baseline'
   f.update(remap(f,{int(k):v for k,v in entry['mapping'].items()}))
 out=subprocess.run([os.environ['ALIGNMENT_ORACLE']],input=json.dumps(request),text=True,capture_output=True)
 sys.stdout.write(out.stdout);sys.stderr.write(out.stderr);return out.returncode

def main():
 a=argparse.ArgumentParser();a.add_argument('--evidence',type=pathlib.Path,required=True);a.add_argument('--comparison',type=pathlib.Path,required=True);a.add_argument('--backend',type=pathlib.Path,required=True);a.add_argument('--tracer',type=pathlib.Path,required=True);a.add_argument('--oracle',type=pathlib.Path,required=True);a.add_argument('--output',type=pathlib.Path,required=True);args=a.parse_args();args.output=args.output.resolve()
 classified=json.loads((args.evidence/'classification.json').read_text());manifest=json.loads((args.evidence/'manifest.json').read_text());numbers={x['number'] for x in classified['cases'] if x['primary']=='register_assignment'};rows=[]
 wrapper=args.output/'oracle';wrapper.parent.mkdir(parents=True,exist_ok=True);wrapper.write_text('#!/bin/sh\nexec '+shlex.quote(sys.executable)+' '+shlex.quote(str(pathlib.Path(__file__).resolve()))+' --oracle "$@"\n');wrapper.chmod(0o755)
 for e in manifest['selected']:
  if e['number'] not in numbers:continue
  data=json.loads((args.evidence/e['evidence']).read_text());folder=args.output/f"{e['number']:02}";folder.mkdir(exist_ok=True);group=(args.comparison/data['artifact_paths']['lean']).parent.parent.parent
  for fn in ['input.clif','stock-config.json']:(folder/fn).write_bytes((group/fn).read_bytes())
  def compile(mode,oracle_bin,extra={}):
   env={**os.environ,'LEAN_REGALLOC':str(oracle_bin),'LEAN_REGALLOC_KEEP':str(folder/(mode+'-request.json')),**extra}
   proc=subprocess.run([str(args.backend),str(folder/'input.clif'),str(folder/(mode+'.o')),'--stock-config',str(folder/'stock-config.json'),'--config-receipt',str(folder/(mode+'-receipt.json')),'--dump',str(folder/mode)],env=env,capture_output=True,text=True)
   (folder/(mode+'.stderr')).write_text(proc.stderr);p=folder/mode/(e['function'].lstrip('%')+'.bin');return {'exit':proc.returncode,'produced':p.exists(),'code_exact':p.exists() and p.read_bytes().hex()==data['stock_code_hex'],'baseline_equal':p.exists() and p.read_bytes().hex()==data['lean_code_hex']}
  row={'number':e['number'],'test':e['test'],'function':e['function'],'baseline':compile('baseline',args.oracle),'variants':{}}
  assert row['baseline']['exit']==0 and row['baseline']['baseline_equal'],row
  subprocess.run([str(args.tracer),str(folder/'input.clif'),str(folder/'trace.json'),'--stock-schedule'],check=True,capture_output=True)
  traced=json.loads((folder/'trace.json').read_text());traces={x['name'].lstrip('%'):x['lowering'] for x in traced['functions'] if x['status']=='lowered'};request=json.loads((folder/'baseline-request.json').read_text())
  for mode,make in [('dense',lambda f,t:dense_map(f,t)),('schedule',lambda f,t:shape_map(f,t['stock_schedule']['allocator_input'])),('reverse_temps',lambda f,t:reverse_map(f))]:
   maps={};errors={}
   for f in request['functions']:
    try:
     t=traces[f['name']];m=make(f,t);remap(f,m);maps[f['name']]={'input_sha256':digest(f),'mapping':m}
    except (ValueError,KeyError,StopIteration,AssertionError,IndexError) as exc:errors[f['name']]=str(exc) or type(exc).__name__
   write(folder/(mode+'-maps.json'),maps)
   row['variants'][mode]={**compile(mode,wrapper,{'ALIGNMENT_MAP':str(folder/(mode+'-maps.json')),'ALIGNMENT_ORACLE':str(args.oracle)}),'mapping_applied':e['function'].lstrip('%') in maps,'mapping_errors':errors}
  rows.append(row);print(e['number'],{k:v['code_exact'] for k,v in row['variants'].items()},flush=True);write(args.output/'results.json',{'schema':1,'scope':'numbering-only; original compiler/checkers; stock schedule is candidate model','rows':rows})
 if len(rows)!=33:raise RuntimeError('expected33 focused cases')
 print('SUMMARY',json.dumps({mode:sum(r['variants'][mode]['code_exact'] for r in rows) for mode in ['dense','schedule','reverse_temps']}))
if __name__=='__main__':sys.exit(oracle() if len(sys.argv)>1 and sys.argv[1]=='--oracle' else main())
