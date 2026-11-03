from pathlib import Path
import subprocess,re,json,hashlib,sys,datetime
O=Path(__file__).resolve().parent;ref='8f073980e9630c8d3cd9d6f6f77ab462474c7bcb';base=Path('/home/lee/clifv');sha=lambda b:hashlib.sha256(b).hexdigest()
paths=[p for p in subprocess.check_output(['git','ls-tree','-r','--name-only',ref],cwd=base,text=True).splitlines() if p.endswith('.lean')]
requests=''.join(ref+':'+p+'\n' for p in paths).encode();raw=subprocess.run(['git','cat-file','--batch'],cwd=base,input=requests,stdout=subprocess.PIPE,check=True).stdout
sources={};pos=0
for p in paths:
 end=raw.index(b'\n',pos);header=raw[pos:end].decode().split();assert header[1]=='blob',header;size=int(header[2]);start=end+1;sources[p]=raw[start:start+size];assert raw[start+size:start+size+1]==b'\n';pos=start+size+1
assert pos==len(raw)
def clean(text):
 out=[];i=0;depth=0;quoted=False
 while i<len(text):
  pair=text[i:i+2];c=text[i]
  if depth:
   if pair=='/-':depth+=1;i+=2;continue
   if pair=='-/':depth-=1;i+=2;continue
   out.append('\n' if c=='\n' else ' ');i+=1;continue
  if quoted:
   if c=='\\':out.extend('  ');i+=2;continue
   if c=='"':quoted=False
   out.append('\n' if c=='\n' else ' ');i+=1;continue
  if pair=='/-':depth=1;i+=2;continue
  if pair=='--':
   end=text.find('\n',i);i=len(text) if end<0 else end;continue
  if c=='"':quoted=True;out.append(' ');i+=1;continue
  out.append(c);i+=1
 return ''.join(out)
def imports(data):return [m for line in re.findall(r'(?m)^\s*(?:public\s+)?import[ \t]+([^\n]+)',clean(data.decode())) for m in line.split()]
def graph(src):return {p[:-5].replace('/','.'):imports(b) for p,b in src.items()}
def cycle_check(g):
 sys.setrecursionlimit(10000);color={};cycles=[];stack=[]
 def visit(n):
  if color.get(n)==2:return
  if color.get(n)==1:cycles.append(stack[stack.index(n):]+[n]);return
  color[n]=1;stack.append(n)
  for dep in g[n]:
   if dep in g:visit(dep)
  stack.pop();color[n]=2
 for n in g:visit(n)
 return cycles
oldPath='FV/E2E/DeadCleanupExecGot.lean';newPath='FV/E2E/OutsideAvoids.lean';assert newPath not in sources
old=(O/'old-source'/oldPath).read_bytes();assert sources[oldPath]==old
new=(O/'new-source'/oldPath).read_bytes();decl=(O/'declaration.lean').read_bytes();assert old.count(decl)==1;assert new==b'import FV.E2E.OutsideAvoids\n'+old.replace(decl,b'',1)
newModule=(O/'new-source'/newPath).read_bytes();assert newModule.count(decl)==1
before=graph(sources);candidate=dict(sources);candidate[oldPath]=new;candidate[newPath]=newModule;after=graph(candidate)
oldCycles=cycle_check(before);newCycles=cycle_check(after);assert not oldCycles,oldCycles;assert not newCycles,newCycles
closure=set();todo=['FV.E2E.RegLevelSim']
while todo:
 m=todo.pop()
 if m in closure:continue
 closure.add(m);todo.extend(n for n in after.get(m,[]) if n in after)
assert 'FV.E2E.DeadCleanupExecGot' not in closure
namespace='E2E.DeadCleanupExecBytes.'
names=re.findall(r'(?m)^(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|structure|inductive|abbrev)\s+([^\s{(:]+)',old.decode())
roots=[namespace+n for n in names];generated=[namespace+'OutsideAvoids.'+n for n in ['mk','stack','args','valid']]
for mode in ['baseline','candidate']:
 p=O/'gates'/mode;p.mkdir(parents=True,exist_ok=True)
 (p/'headers.lean').write_text('import FV.E2E.DeadCleanupExecGot\n\n'+''.join('#check @'+n+'\n' for n in roots+generated))
 (p/'axioms.lean').write_text('import FV.E2E.DeadCleanupExecGot\n\n'+''.join('#print axioms '+n+'\n' for n in roots+generated))
broad=base/'.git/agent-evidence/stock-memory-20261029/892-joint-current-context-v2/package'
d={'status':'source_only_proposal_complete_import_cycle_check_passed','origin_ref':ref,'origin_is_origin_main':subprocess.check_output(['git','rev-parse','origin/main'],cwd=base,text=True).strip()==ref,'old_file':oldPath,'new_file':newPath,'old_source_sha256':sha(old),'candidate_old_file_sha256':sha(new),'new_file_sha256':sha(newModule),'exact_declaration_sha256':sha(decl),'declaration_name':namespace+'OutsideAvoids','exact_declaration_bytes_preserved':True,'old_file_only_import_added_and_exact_declaration_removed':True,'broad_P_source_sha256':sha((broad/oldPath).read_bytes()) if (broad/oldPath).exists() else None,'all_current8f_lean_sources':{p:sha(b) for p,b in sources.items()},'complete_graph_module_count':len(before),'candidate_graph_module_count':len(after),'original_import_cycles':oldCycles,'candidate_import_cycles':newCycles,'new_module_imports':imports(newModule),'new_module_dependency_hashes':{m:sha(candidate[m.replace('.','/')+'.lean']) for m in sorted(closure)},'new_dependency_closure_count':len(closure),'old_declaration_headers_to_compare':roots+generated,'old_axiom_roots_to_compare_exactly':roots+generated,'old_header_gate_run':False,'old_axiom_gate_run':False,'normal_key_gate_run':False,'Lean_compilers_started':0,'shared_files_changed':0,'shared_P_changed':False,'approval_to_apply':False,'validation_still_required':['Establish coherent actual-current8f normal dependency contexts before baseline or candidate kernels','Run baseline and candidate header gates with identical pinned configuration; compare exact outputs','Run focused new-module kernel before old importer and refresh only required actual normal keys','Run the unchanged real repository auditor for both old and candidate root lists; compare every old AX set including empty sets','Complete physical and atomic/provider gates under separately approved measured resource caps','Complete actual-results executable, production, linker, generated and current-main gates'],'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(O/'manifest.json').write_text(json.dumps(d,indent=2)+'\n');print('complete graph',len(before),'new closure',len(closure),'old declarations/generation',len(roots+generated));print('manifest',sha((O/'manifest.json').read_bytes()))
