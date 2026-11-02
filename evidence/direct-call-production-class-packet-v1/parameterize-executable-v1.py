from pathlib import Path
import re,subprocess,json,hashlib
B=Path('/home/lee/clifv');P=B/'.git/agent-evidence/stock-memory-20261029/direct-call-production-class-packet-v1';ref='90c51c880b9d614f7c5f9730b8363a6321c840de'
files=['FV/E2E/ReturnPinExecStatic.lean','FV/E2E/ReturnPinExecGot.lean','FV/E2E/ReturnPinExecProven.lean'];allentries=[];genericparts=[]
for name in files:
 original=subprocess.check_output(['git','show',ref+':'+name],cwd=B,text=True);old=P/'shared-baseline-v1'/name;old.parent.mkdir(parents=True,exist_ok=True);old.write_text(original)
 commands=list(re.finditer(r'(?m)^(?:theorem|def|structure|abbrev|namespace|end|set_option|variable|/[-!]).*',original));namespace='';entries=[]
 for i,m in enumerate(commands):
  line=m.group(0)
  if line.startswith('namespace '):namespace=line.split()[1]
  if not line.startswith('theorem '):continue
  end=commands[i+1].start() if i+1<len(commands) else len(original);segment=original[m.start():end];at=segment.index(':=');header=segment[:at];short=re.match(r'theorem\s+([^\s{:(]+)',segment).group(1);entries.append(dict(start=m.start(),end=end,namespace=namespace,short=short,header=header,file=name))
 generic='\n'.join(line for line in original.splitlines() if not line.startswith('import '))+'\n'
 generic=generic.replace('namespace E2E.ReturnPinExecBytes\n','namespace E2E.ReturnPinExecBytesFor\nvariable {admission : E2E.LinkCheck.ReturnPinAdmission}\n').replace('end E2E.ReturnPinExecBytes','end E2E.ReturnPinExecBytesFor')
 generic=generic.replace('ReturnPinStackBound.okB I','ReturnPinBinaryFor.okBFor admission I').replace('ReturnPinStackBound.','ReturnPinStackBoundFor.').replace('ReturnPinBinary.','ReturnPinBinaryFor.').replace('ReturnPinExecBytes.','ReturnPinExecBytesFor.').replace('returnPinCallsExtra','admission.extra').replace('OkReturnPins.extImgProduction','OkReturnPins.extImgProductionFor')
 genericparts.append(generic)
 facade=original
 for e in reversed(entries):
  pure=(e['namespace']=='E2E.LinkSys' or e['short']=='destsInt_of_ok')
  target=(e['namespace']+'.'+e['short']).replace('ReturnPinExecBytes.','ReturnPinExecBytesFor.').replace('OkReturnPins.extImgProduction','OkReturnPins.extImgProductionFor')
  supplied='' if pure else ' (admission := E2E.LinkCheck.ReturnPinAdmission.previous)'
  body='by\n  apply '+target+supplied+' <;> assumption\n\n';facade=facade[:e['start']]+e['header']+':= '+body+facade[e['end']:]
 facade='import FV.E2E.ReturnPinExecutableKernel\n'+facade;(P/name).write_text(facade);allentries+=entries
imports='import FV.E2E.ReturnPinBinaryKernel\nimport FV.E2E.SemanticExecGoodReads\nimport FV.E2E.SemanticExecGot\n'
(P/'FV/E2E/ReturnPinExecutableKernel.lean').write_text(imports+'\n'.join(genericparts))
(P/'executable-kernel-move-v1.json').write_text(json.dumps(dict(old_files=files,old_headers={e['namespace']+'.'+e['short']:e['header'] for e in allentries},old_roots=[e['namespace']+'.'+e['short'] for e in allentries],generic_roots=[(e['namespace']+'.'+e['short']).replace('ReturnPinExecBytes.','ReturnPinExecBytesFor.').replace('OkReturnPins.extImgProduction','OkReturnPins.extImgProductionFor') for e in allentries]),indent=2)+'\n');print('Moved',len(allentries),'executable proof bodies into one kernel.')
