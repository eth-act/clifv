from pathlib import Path
import importlib.util,json,hashlib
root=Path('/tmp/stock-div-next-staged');old=Path('scripts/check-stock-mixed-native.py').read_text();s=old.replace('def run_commands(bits, kind="mixed"):', 'def run_commands(bits, kind="mixed", vectors=None):')
a=s.index('    vectors = [');b=s.index('    cases = []',a);s=s[:a]+'    if vectors is None:\n'+''.join('    '+line if line.strip() else line for line in s[a:b].splitlines(True))+s[b:]
new='''    if kind == "mixeddiv":
        cases = run_commands(bits, "div")
        low, high = -(1 << (bits - 1)), (1 << (bits - 1)) - 1
        # Keep every old case; add live-prefix outcomes, zero divisors, signed
        # boundaries, and the original constant-2 source cases for safe roots.
        vectors = [
            [0,5,2,11,22,33,44,55,7], [1,5,2,11,22,33,44,55,7],
            [-1,-1,1,11,22,33,44,55,1], [0,low,1,11,22,33,44,55,-1],
            [1,high,-1,11,22,33,44,55,1], [2,0,high,11,22,33,44,55,low],
            [1,low,low,11,22,33,44,55,low], [1,1,0,11,22,33,44,55,7],
            [0,0,0,0,0,0,0,0,0], [1,7,-2,11,22,33,44,55,0],
            [1,-7,2,11,22,33,44,55,-2],
        ]
        values = [(args,value) for name,args,value in run_commands(bits,"highmul",vectors)
                  if name == "stock_highmul_ni"]
        assert len(values) == len(vectors)
        mask = (1 << bits) - 1
        for safe in (False,True):
            for op in ("sdiv","udiv","srem","urem"):
                for args,a in values:
                    b = 2 if safe else args[8]
                    if b == 0:
                        result = "int_divz"
                    elif op == "sdiv" and a == low and b == -1:
                        result = "int_ovf"
                    else:
                        x,y = (a & mask,b & mask) if op[0] == "u" else (a,b)
                        q = abs(x) // abs(y)
                        if (x < 0) != (y < 0):q = -q
                        result = signed(q if op.endswith("div") else x-q*y,bits)
                    cases.append(("stock_mixed_div_"+op+("_two" if safe else ""),args,result))
        return cases
'''
s=s.replace('    if kind == "div":',new+'    if kind == "div":',1)
s=s.replace('"highmul", "div"], default=', '"highmul", "div", "mixeddiv"], default=')
s=s.replace('if options.kind in ("highmul", "div"):', 'if options.kind in ("highmul", "div", "mixeddiv"):')
s=s.replace('        if options.kind == "div":','        if options.kind in ("div", "mixeddiv"):')
s=s.replace('        assert names == wanted, names','        if options.kind == "mixeddiv":\n            wanted |= {"stock_mixed_div_"+op+suffix for op in ("sdiv","udiv","srem","urem") for suffix in ("","_two")}\n        assert names == wanted, names')
p=root/'scripts/check-stock-mixed-native.py';p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s);compile(s,str(p),'exec')
def load(path,name):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
before=load(Path('scripts/check-stock-mixed-native.py'),'old');after=load(p,'new');kinds=['mixed','logical','scalar','not','mul','shift','cast','bit','popcount','minmax','cmp','highmul','div'];results={}
for bits in (32,64):
 for kind in kinds:assert before.run_commands(bits,kind)==after.run_commands(bits,kind),(bits,kind)
 new=after.run_commands(bits,'mixeddiv');prior=before.run_commands(bits,'div');assert new[:len(prior)]==prior;results[bits]={'all13prior_grids_exact':True,'prior_cases':len(prior),'current_cases':len(new),'new_cases':len(new)-len(prior),'new_coded_traps':sum(isinstance(v,str) for _,_,v in new[len(prior):])}
(root/'native-grid-preparation.json').write_text(json.dumps({'state':'Python grid generation/retention checks pass; actual Lean objects/native execution pending activation','results':results,'source_sha256':hashlib.sha256(s.encode()).hexdigest()},indent=2)+'\n');print(results)
