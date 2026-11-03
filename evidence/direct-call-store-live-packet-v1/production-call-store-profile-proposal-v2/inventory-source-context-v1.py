from pathlib import Path
import json,hashlib,subprocess,re
D=Path(__file__).resolve().parent;Q=D.parent;E=Q.parent;L=D/'source-context-v1';L.mkdir();main='2c6008540ece15aa8e2ae2813322247f0d67e48b';gitFiles=subprocess.check_output(['git','ls-tree','-r','--name-only',main],text=True).splitlines();lean=[p for p in gitFiles if p.endswith('.lean') and p.startswith(('FV/','FVTest/'))];proc=subprocess.run(['git','cat-file','--batch'],input=''.join(main+':'+p+'\n' for p in lean).encode(),stdout=subprocess.PIPE,check=True);data=proc.stdout;offset=0;base={};blob={}
for rel in lean:
 end=data.index(b'\n',offset);header=data[offset:end].decode().split();size=int(header[2]);offset=end+1;base[rel]=data[offset:offset+size];blob[rel]=header[0];offset+=size+1
priority=[D/'source',Q/'production-call-store-constructor-proposal-v1/source',Q/'production-head-binding-v1/source',Q/'production-parameterized-factories-v1/source',E/'general7-main-candidate-v1/publication-source-packet-v2/source',Q/'production-current-adapter-prep-v2/preserved-support',E/'direct-call-production-class-packet-v1/reviewed-production-complete-v1'];graph={};records={};stack=[];done=set()
def source(n):
 rel=n.replace('.','/')+'.lean'
 for root in priority:
  p=root/rel
  if p.exists():return p.read_bytes(),{'path':str(p),'origin_kind':'explicit staged source overlay'}
 assert rel in base,('Missing source',n)
 return base[rel],{'git_commit':main,'git_blob':blob[rel],'origin_kind':'exact actual-main Git blob'}
def visit(n):
 assert n not in stack,('Import cycle',stack+[n])
 if n in done:return
 stack.append(n);s,origin=source(n);records[n]={'sha256':hashlib.sha256(s).hexdigest(),**origin};deps=[]
 for line in s.decode().splitlines():
  if line.startswith('import '):deps.extend(d for d in line.split()[1:] if d.startswith(('FV.','FVTest.')))
 graph[n]=deps
 for dep in deps:visit(dep)
 stack.pop();done.add(n)
roots=sorted(p.relative_to(D/'source').as_posix()[:-5].replace('/','.') for p in (D/'source').rglob('*.lean'))
for n in roots:visit(n)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();j={'status':'STAGED_SOURCE_CLOSURE_ONLY;NOT_KERNEL_OR_NATIVE_READINESS','actual_main':main,'profile_manifest_sha256':sha(D/'manifest.json'),'roots11':roots,'source_origins':records,'graph':graph,'import_cycles':[],'overlay_priority':[str(p) for p in priority],'new_root_count':len(roots),'closure_count':len(graph),'current_native_gates':'Required after current source and config keys pass; no artifact reuse or readiness is claimed','complete_old_file_action_retained':True};(L/'manifest.json').write_text(json.dumps(j,indent=2)+'\n');print(sha(L/'manifest.json'),len(graph))
