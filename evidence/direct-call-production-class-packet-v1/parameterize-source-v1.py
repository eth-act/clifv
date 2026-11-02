from pathlib import Path
import subprocess,re,json
B=Path('/home/lee/clifv');P=B/'.git/agent-evidence/stock-memory-20261029/direct-call-production-class-packet-v1';name='FV/Link/ReturnPinExeSourceWith.lean';original=subprocess.check_output(['git','show','90c51c880b9d614f7c5f9730b8363a6321c840de:'+name],cwd=B,text=True);old=P/'shared-baseline-v1'/name;old.parent.mkdir(parents=True,exist_ok=True);old.write_text(original)
generic=original.replace('import FV.Link.ReturnPinExeWith','import FV.Link.ReturnPinCompilerKernel').replace('namespace Link.ReturnPinCompilerWith\n','namespace Link.ReturnPinCompilerFor\nvariable {admission : E2E.LinkCheck.ReturnPinAdmission}\nlocal notation "attempt" => attemptFor admission\n').replace('end Link.ReturnPinCompilerWith','end Link.ReturnPinCompilerFor').replace('ReturnPinBinary.','ReturnPinBinaryFor.');(P/'FV/Link/ReturnPinCompilerSourceKernel.lean').write_text(generic)
commands=list(re.finditer(r'(?m)^(?:theorem|def|structure|abbrev|namespace|end|set_option|variable|/[-!]).*',original));entries=[]
for i,m in enumerate(commands):
 if not m.group(0).startswith('theorem '):continue
 end=commands[i+1].start() if i+1<len(commands) else len(original);segment=original[m.start():end];at=segment.index(':=');short=re.match(r'theorem\s+([^\s{:(]+)',segment).group(1);entries.append((m.start(),end,short,segment[:at]))
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
for start,end,short,header in reversed(entries):
 args=['(admission := E2E.LinkCheck.ReturnPinAdmission.previous)']+['('+n+' := '+n+')' for n in names_in_prefix(header)];body='by\n  exact Link.ReturnPinCompilerFor.'+short+'\n'+'\n'.join('    '+' '.join(args[i:i+3]) for i in range(0,len(args),3))+'\n\n';facade=facade[:start]+header+':= '+body+facade[end:]
(P/name).write_text('import FV.Link.ReturnPinCompilerSourceKernel\n'+facade);(P/'source-kernel-move-v1.json').write_text(json.dumps(dict(old_headers={'Link.ReturnPinCompilerWith.'+s:h for _,_,s,h in entries},old_roots=['Link.ReturnPinCompilerWith.'+s for _,_,s,_ in entries],generic_roots=['Link.ReturnPinCompilerFor.'+s for _,_,s,_ in entries]),indent=2)+'\n');print('Moved two guarded original-source proofs without changing their premises.')
