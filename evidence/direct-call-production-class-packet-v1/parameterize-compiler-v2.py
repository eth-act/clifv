from pathlib import Path
import re,json,subprocess
B=Path('/home/lee/clifv');P=B/'.git/agent-evidence/stock-memory-20261029/direct-call-production-class-packet-v1';ref='90c51c880b9d614f7c5f9730b8363a6321c840de'
(P/'FV/Link').mkdir(parents=True,exist_ok=True)
# Reuse the exact old scope, checker branch, writer, and diagnostic in one factory.
name='FV/Link/ReturnPinCompileDefs.lean';original=subprocess.check_output(['git','show',ref+':'+name],cwd=B,text=True);old=P/'shared-baseline-v1'/name;old.parent.mkdir(parents=True,exist_ok=True);old.write_text(original)
a=original.index('def attempt ');b=original.index('\nend Link.ReturnPinCompilerWith',a);definition=original[a:b]
factory=definition.replace('def attempt (lower :','def attemptWith (checked : (Clif.Function → VCode → VCode) → LinkInput → Res → Bool) (lower :').replace('if okRReturnPinCalls (productionStage cleanup)','if checked (productionStage cleanup)')
(P/'FV/Link/ReturnPinAttemptKernel.lean').write_text('import FV.Link.SemanticCompileDefs\nimport FV.E2E.ReturnPinAdmission\n\nnamespace Link.ReturnPinAttemptKernel\nopen Backend E2E E2E.LinkCheck\nset_option autoImplicit false\nset_option Elab.async false\n\n'+factory+'\n\nend Link.ReturnPinAttemptKernel\n')
olddef=definition.split(':=',1)[0]+':=\n  ReturnPinAttemptKernel.attemptWith okRReturnPinCalls lower S file0 cleanup\n'
facade=original[:a]+olddef+original[b:];facade='import FV.Link.ReturnPinAttemptKernel\n'+facade;(P/name).write_text(facade)
# Move executable compiler correctness once; keep the old compatibility theorem in its facade.
name='FV/Link/ReturnPinExeWith.lean';original=subprocess.check_output(['git','show',ref+':'+name],cwd=B,text=True);old=P/'shared-baseline-v1'/name;old.parent.mkdir(parents=True,exist_ok=True);old.write_text(original)
commands=list(re.finditer(r'(?m)^(?:theorem|def|structure|abbrev|namespace|end|set_option|variable|/[-!]).*',original));entries=[];namespace=''
for i,m in enumerate(commands):
 line=m.group(0)
 if line.startswith('namespace '):namespace=line.split()[1]
 if not line.startswith('theorem '):continue
 end=commands[i+1].start() if i+1<len(commands) else len(original);segment=original[m.start():end];at=min(v for v in [segment.find(':='),segment.find(' where\n')] if v>=0);short=re.match(r'theorem\s+([^\s{:(]+)',segment).group(1);entries.append(dict(start=m.start(),end=end,namespace=namespace,short=short,header=segment[:at]))
generic=original
for e in reversed(entries):
 if e['short']=='accepts_previous':generic=generic[:e['start']]+generic[e['end']:]
generic='\n'.join(line for line in generic.splitlines() if not line.startswith('import '))+'\n';generic=generic.replace('namespace Link.ReturnPinCompilerWith\n','namespace Link.ReturnPinCompilerFor\nvariable {admission : E2E.LinkCheck.ReturnPinAdmission}\n').replace('end Link.ReturnPinCompilerWith','end Link.ReturnPinCompilerFor');a=generic.index('abbrev input ')
generic=generic[:a]+"""abbrev attemptFor (admission : E2E.LinkCheck.ReturnPinAdmission) :=
  ReturnPinAttemptKernel.attemptWith (E2E.LinkCheck.okRReturnPinFor admission)
local notation "attempt" => attemptFor admission

"""+generic[a:]
generic=generic.replace('ReturnPinBinary.okB (','ReturnPinBinaryFor.okBFor admission (').replace('E2E.ReturnPinExecBytes.','E2E.ReturnPinExecBytesFor.').replace('simp [attempt]','simp [attemptFor,ReturnPinAttemptKernel.attemptWith]')
(P/'FV/Link/ReturnPinCompilerKernel.lean').write_text('import FV.Link.Exe\nimport FV.Link.ReturnPinAttemptKernel\nimport FV.Link.ProductionImageWithProof\nimport FV.E2E.ReturnPinExecutableKernel\n\n'+generic)
def names_in_prefix(header):
 depth=0
 for end,c in enumerate(header):
  if c in '({[':depth+=1
  elif c in ')}]':depth-=1
  elif c==':' and depth==0:break
 prefix=header[:end];names=[];i=0
 while i<len(prefix):
  if prefix[i] not in '({':i+=1;continue
  start=i;stack=[prefix[i]];i+=1
  while stack:
   c=prefix[i]
   if c in '({[':stack.append(c)
   elif c in ')}]':stack.pop()
   i+=1
  inside=prefix[start+1:i-1]
  if ':' in inside:names += [n for n in inside.split(':',1)[0].split() if n!='_']
 return names
facade=original
for e in reversed(entries):
 if e['short']=='accepts_previous':continue
 target='Link.ReturnPinCompilerFor.'+e['short'];args=[]
 if 'attempt lower' in e['header']:args.append('(admission := E2E.LinkCheck.ReturnPinAdmission.previous)')
 args += ['('+n+' := '+n+')' for n in names_in_prefix(e['header'])]
 body='by\n  exact '+target+'\n'+'\n'.join('    '+' '.join(args[i:i+3]) for i in range(0,len(args),3))+'\n\n';facade=facade[:e['start']]+e['header']+':= '+body+facade[e['end']:]
facade=facade.replace('simp [attempt,SemanticCompilerWith.attempt]','simp [attempt,ReturnPinAttemptKernel.attemptWith,SemanticCompilerWith.attempt]');(P/name).write_text('import FV.Link.ReturnPinCompilerKernel\n'+facade)
(P/'compiler-kernel-move-v1.json').write_text(json.dumps(dict(old_roots=[e['namespace']+'.'+e['short'] for e in entries],old_headers={e['namespace']+'.'+e['short']:e['header'] for e in entries},generic_roots=['Link.ReturnPinCompilerFor.'+e['short'] for e in entries if e['short']!='accepts_previous']),indent=2)+'\n');print('Moved eight compiler proof bodies; retained nine old headers and compatibility.')
