from pathlib import Path
import hashlib,json,re
E=Path('/home/lee/clifv/.git/agent-evidence/stock-memory-20261029');P=E/'direct-call-production-class-packet-v1';Q=E/'direct-call-arithmetic-live-packet-v1';baseline=json.loads((Q/'predecessor-source-context-v1.json').read_text())
files=['FV/Backend/SemanticABICheck.lean','FV/E2E/CompiledSemanticABI.lean','FV/E2E/CompiledSemanticReturnPins.lean','FV/E2E/CompiledProgramReturnPins.lean','FV/E2E/SemanticABIBoundary.lean','FV/E2E/WorldReturnPinBoundary.lean','FV/E2E/LinkReturnPinWorldX.lean','FV/E2E/ReturnPinAdmission.lean']
original={}
for n in files:
 data=(P/n).read_bytes();assert hashlib.sha256(data).hexdigest()==baseline['owned_predecessor_sources'][n],n;original[n]=data.decode();dst=Q/'shared-predecessor-v1'/n;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(data)
def rename(t):return t.replace('resultCall','liveCall').replace('Stock.ResultCall','Stock.LiveCall').replace('stock_result_call','stock_live_call')
def cases(t):
 lines=t.splitlines(keepends=True);out=[];i=0
 while i<len(lines):
  if re.match(r'^  \| @?resultCall\b',lines[i]):
   j=i+1
   while j<len(lines) and (not lines[j].strip() or lines[j].startswith('    ')):j+=1
   chunk=''.join(lines[i:j]);out.extend([chunk,rename(chunk)]);i=j
  else:out.append(lines[i]);i+=1
 return ''.join(out)
def theorem(t,name):
 start=t.index('theorem '+name);m=re.search(r'\n(?:theorem |end )',t[start:]);assert m;return t[start:start+m.start()]
for n,t in original.items():
 dst=Q/n;dst.parent.mkdir(parents=True,exist_ok=True)
 if n.endswith('SemanticABICheck.lean'):
  t='import FV.Backend.StockLiveCallCheck\n'+t+'''
namespace Backend.SemanticABI
set_option autoImplicit false

def checkLiveCalls (f : Clif.Function) (vc : VCode) : Bool :=
  checkResultCalls f vc || Stock.LiveCall.check f vc

theorem previous_check_live_calls {f : Clif.Function} {vc : VCode}
    (accepted : checkResultCalls f vc = true) : checkLiveCalls f vc = true := by
  simp only [checkLiveCalls,accepted,Bool.true_or]

theorem previous_exact_live_calls {f : Clif.Function} {vc : VCode}
    (absent : Stock.LiveCall.check f vc = false) : checkLiveCalls f vc = checkResultCalls f vc := by
  simp only [checkLiveCalls,absent,Bool.or_false]
end Backend.SemanticABI
'''
 elif n.endswith(('CompiledSemanticABI.lean','CompiledSemanticReturnPins.lean')):
  t='import FV.E2E.StockLiveCallNI\n'+cases(t)
  helper=theorem(original[n],'of_checks_result_calls')
  helper=helper.replace('of_checks_result_calls','of_checks_live_calls').replace('SemanticABI.checkResultCalls','SemanticABI.checkLiveCalls').replace('Stock.ResultCall','Stock.LiveCall').replace('.resultCall','.liveCall')
  helper=helper.replace('of_checks_calls old','of_checks_result_calls old').replace('SemanticABI.checkCalls f vc','SemanticABI.checkResultCalls f vc')
  helper=helper.replace('(fun accepted => old (SemanticABI.previous_check_calls (SemanticABI.previous_check accepted)))','(fun accepted => old (SemanticABI.previous_check_result_calls (SemanticABI.previous_check_calls (SemanticABI.previous_check accepted))))')
  marker='end CompiledSemanticReturnPins' if n.endswith('CompiledSemanticReturnPins.lean') else 'end CompiledSemanticABI'
  t=t.replace(marker,helper+'\n\n'+marker,1)
 elif n.endswith('CompiledProgramReturnPins.lean'):
  helper=theorem(t,'of_checks_result_calls').replace('of_checks_result_calls','of_checks_live_calls').replace('SemanticABI.checkResultCalls','SemanticABI.checkLiveCalls')
  t=t.replace('end CompiledProgramReturnPins',helper+'\n\nend CompiledProgramReturnPins',1)
 elif n.endswith('SemanticABIBoundary.lean'):
  t='import FV.E2E.StockLiveCallFlags\n'+cases(t)
  start=t.index('  | @liveCall cleanup result source equal h =>');end=t.index('\nset_option ',start)
  section=t[start:end].replace('Stock.VoidCall.NI.codeCheck','Stock.LiveCall.codeCheck').replace('void_call_noTls readChecks','Stock.LiveCall.noTls_of_codeCheck readChecks');t=t[:start]+section+t[end:]
 elif n.endswith(('WorldReturnPinBoundary.lean','LinkReturnPinWorldX.lean')):t=cases(t)
 elif n.endswith('ReturnPinAdmission.lean'):
  t=t[:t.rindex('end E2E.LinkCheck')]+'''
/-- The new profile leaves every prior checker and profile unchanged. -/
def returnPinLiveCallsExtra (f : Clif.Function) (vc : VCode) : Bool :=
  returnPinResultCallsExtra f vc || Stock.LiveCall.check f vc

def ReturnPinAdmission.liveCalls : ReturnPinAdmission where
  extra := returnPinLiveCallsExtra
  compiled := by
    intro f k vc vcp rf af fa fb cleanup checked prepared prepOk check alloc emit layout
    apply CompiledSemanticReturnPins.of_checks_live_calls ?_ prepared prepOk check alloc emit layout
    simpa only [returnPinLiveCallsExtra,returnPinResultCallsExtra,returnPinCallsExtra,
      SemanticABI.checkLiveCalls,SemanticABI.checkResultCalls,SemanticABI.checkCalls,SemanticABI.check,
      Bool.or_assoc] using checked

abbrev okRReturnPinLiveCalls := okRReturnPinFor ReturnPinAdmission.liveCalls

end E2E.LinkCheck
'''
 dst.write_text(t)
(Q/'live-shared-inventory-v1.json').write_text(json.dumps({n:dict(predecessor_sha256=hashlib.sha256(original[n].encode()).hexdigest(),candidate_sha256=hashlib.sha256((Q/n).read_bytes()).hexdigest()) for n in files},indent=2)+'\n')
print('Staged',len(files),'owned shared copies; not compiled.')
