from pathlib import Path
import re,json
P=Path('/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-production-class-packet-v1')
files=['FV/E2E/ReturnPinExecStatic.lean','FV/E2E/ReturnPinExecGot.lean','FV/E2E/ReturnPinExecProven.lean'];headers={}
def names_in_prefix(header):
 depth=0;end=None
 for i,c in enumerate(header):
  if c in '({[':depth+=1
  elif c in ')}]':depth-=1
  elif c==':' and depth==0:end=i;break
 assert end is not None
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
  if ':' in inside:
   for name in inside.split(':',1)[0].split():
    if name!='_':names.append(name)
 return names
for name in files:
 original=(P/'shared-baseline-v1'/name).read_text();commands=list(re.finditer(r'(?m)^(?:theorem|def|structure|abbrev|namespace|end|set_option|variable|/[-!]).*',original));entries=[];namespace=''
 for i,m in enumerate(commands):
  line=m.group(0)
  if line.startswith('namespace '):namespace=line.split()[1]
  if not line.startswith('theorem '):continue
  end=commands[i+1].start() if i+1<len(commands) else len(original);segment=original[m.start():end];markers=[v for v in [segment.find(':='),segment.find(' where\n')] if v>=0];at=min(markers);header=segment[:at];short=re.match(r'theorem\s+([^\s{:(]+)',segment).group(1);entries.append((m.start(),end,namespace,short,header));headers[namespace+'.'+short]=header
 facade=original
 for start,end,namespace,short,header in reversed(entries):
  pure=namespace=='E2E.LinkSys' or short=='destsInt_of_ok';target=(namespace+'.'+short).replace('ReturnPinExecBytes.','ReturnPinExecBytesFor.').replace('OkReturnPins.extImgProduction','OkReturnPins.extImgProductionFor');args=[]
  if not pure:args.append('(admission := E2E.LinkCheck.ReturnPinAdmission.previous)')
  args += ['('+n+' := '+n+')' for n in names_in_prefix(header)]
  body='by\n  exact '+target+'\n'+'\n'.join('    '+' '.join(args[i:i+3]) for i in range(0,len(args),3))+'\n\n';facade=facade[:start]+header+':= '+body+facade[end:]
 (P/name).write_text('import FV.E2E.ReturnPinExecutableKernel\n'+facade)
(P/'executable-old-headers-v2.json').write_text(json.dumps(dict(status='typed_headers_exact',headers=headers),indent=2)+'\n')
