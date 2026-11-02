from pathlib import Path
import re,subprocess,json,hashlib
B=Path('/home/lee/clifv');P=B/'.git/agent-evidence/stock-memory-20261029/direct-call-production-class-packet-v1'
name='FV/E2E/ReturnPinBinary.lean';original=subprocess.check_output(['git','show','90c51c880b9d614f7c5f9730b8363a6321c840de:'+name],cwd=B,text=True)
old=P/'shared-baseline-v1'/name;old.parent.mkdir(parents=True,exist_ok=True);old.write_text(original)
# Top-level commands delimit proof bodies. Every tactic in this file is indented.
commands=list(re.finditer(r'(?m)^(?:theorem|def|structure|abbrev|namespace|end|set_option|variable|/[-!]).*',original))
entries=[];namespace=''
for i,m in enumerate(commands):
 line=m.group(0)
 if line.startswith('namespace '):namespace=line.split()[1]
 if not line.startswith('theorem '):continue
 end=commands[i+1].start() if i+1<len(commands) else len(original)
 segment=original[m.start():end];at=segment.index(':=');header=segment[:at];short=re.match(r'theorem\s+([^\s{:(]+)',segment).group(1)
 entries.append(dict(start=m.start(),end=end,namespace=namespace,short=short,header=header,body=segment[at+2:]))
keep={'E2E.ReturnPinBinary.okB_previous','E2E.ReturnPinBinary.BinFacts.previous'}
# One generic proof implementation. The two compatibility conversions stay in the old facade.
generic=original
for e in reversed(entries):
 if e['namespace']+'.'+e['short'] in keep:generic=generic[:e['start']]+generic[e['end']:]
generic=generic.replace('import FV.E2E.PreparedReturnPinCalls','import FV.E2E.ReturnPinAdmission')
generic=generic.replace('E2E.ReturnPinBinary','E2E.ReturnPinBinaryFor').replace('E2E.ReturnPinStackBound','E2E.ReturnPinStackBoundFor').replace('ReturnPinStackBound.','ReturnPinStackBoundFor.').replace('ReturnPinBinary.','ReturnPinBinaryFor.')
generic=generic.replace('namespace E2E.ReturnPinBinaryFor\n','namespace E2E.ReturnPinBinaryFor\nvariable {admission : E2E.LinkCheck.ReturnPinAdmission}\n').replace('namespace E2E.ReturnPinStackBoundFor\n','namespace E2E.ReturnPinStackBoundFor\nvariable {admission : E2E.LinkCheck.ReturnPinAdmission}\n')
generic=generic.replace('def okB (I : SemanticStackBound.CompilerInput) : Bool :=\n  okRReturnPinCalls I.stage I.toLinkInput I.results','def okBFor (admission : ReturnPinAdmission) (I : SemanticStackBound.CompilerInput) : Bool :=\n  okRReturnPinFor admission I.stage I.toLinkInput I.results\n\nlocal notation "okB" => okBFor admission')
generic=generic.replace('semanticPreparedReturnPinCallsResults_sound I.stage','semanticPreparedReturnPinFor_sound admission I.stage')
generic=generic.replace('structure BinFacts (I :','structure BinFacts (admission : ReturnPinAdmission) (I :')
# Only type applications change. Declaration names such as BinFacts.modelOf_ne remain stable.
generic=generic.replace('BinFacts I ', 'BinFacts admission I ')
generic=generic.replace('abbrev okB := ReturnPinBinaryFor.okB','abbrev okBFor (admission : ReturnPinAdmission) := ReturnPinBinaryFor.okBFor admission\nlocal notation "okB" => okBFor admission')
generic=generic.replace('returnPinCallsExtra','admission.extra')
# Reopened binary sections need the same local shorthand.
parts=generic.split('namespace E2E.ReturnPinBinaryFor\n')
for i in range(2,len(parts)):
 at=parts[i].index('variable {admission : E2E.LinkCheck.ReturnPinAdmission}\n')+len('variable {admission : E2E.LinkCheck.ReturnPinAdmission}\n')
 parts[i]=parts[i][:at]+'local notation "okB" => okBFor admission\n'+parts[i][at:]
generic='namespace E2E.ReturnPinBinaryFor\n'.join(parts)
(P/'FV/E2E/ReturnPinBinaryKernel.lean').write_text(generic)
# Thin old facade. Old declarations and structure fields remain exact.
facade=original
for e in reversed(entries):
 full=e['namespace']+'.'+e['short']
 if full in keep:continue
 target=full.replace('E2E.ReturnPinBinary.','E2E.ReturnPinBinaryFor.').replace('E2E.ReturnPinStackBound.','E2E.ReturnPinStackBoundFor.')
 needs=('okB ' in e['header'] or 'BinFacts ' in e['header'])
 supplied=' (admission := ReturnPinAdmission.previous)' if needs else ''
 if e['short']=='binFacts_of_checks':
  body='by\n  have facts := '+target+' (admission := ReturnPinAdmission.previous) hI hB\n  exact ⟨facts.ok,facts.code,facts.data⟩\n\n'
 else:
  conversions=[]
  for arg in re.findall(r'\((\w+)\s*:\s*BinFacts\b',e['header']):conversions.append('exact ⟨'+arg+'.ok,'+arg+'.code,'+arg+'.data⟩')
  tactics='assumption'+''.join(' | '+c for c in conversions)
  body='by\n  apply '+target+supplied+' <;> first | '+tactics+'\n\n'
 facade=facade[:e['start']]+e['header']+':= '+body+facade[e['end']:]
facade='import FV.E2E.ReturnPinBinaryKernel\n'+facade
(P/name).write_text(facade)
(P/'binary-kernel-move-v1.json').write_text(json.dumps(dict(old_sha256=hashlib.sha256(original.encode()).hexdigest(),old_headers={e['namespace']+'.'+e['short']:e['header'] for e in entries},generic_roots=[e['namespace'].replace('ReturnPinBinary','ReturnPinBinaryFor').replace('ReturnPinStackBound','ReturnPinStackBoundFor')+'.'+e['short'] for e in entries if e['namespace']+'.'+e['short'] not in keep],old_roots=[e['namespace']+'.'+e['short'] for e in entries]),indent=2)+'\n')
print('Moved',len(entries)-len(keep),'proof bodies; retained',len(entries),'old public theorem headers.')
