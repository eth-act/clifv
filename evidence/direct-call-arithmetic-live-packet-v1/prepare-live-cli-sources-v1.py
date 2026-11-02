from pathlib import Path
import json,hashlib
Q=Path(__file__).resolve().parent;P=Q.parent/'direct-call-production-class-packet-v1'
def write(n,s):
 p=Q/n;assert not p.exists(),n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
n='FVTest/Backend/Main.lean';s=(P/n).read_text();s=s.replace('import FV.Backend.ResultCallProduction','import FV.Backend.LiveCallProduction').replace('compileFileResultCallWhen','compileFileLiveCallWhen');write(n,s)
n='FVTest/Link/LeanLinkMain.lean';s=(P/n).read_text();s='import FV.Backend.Lowering.StockLiveCallRoutes\nimport FV.Link.LiveCallExeWith\n'+s
marker='  -- This complete-file attempt leaves every previous mode and retry action below intact.\n'
assert s.count(marker)==1
start=s.index(marker);end=s.index('  let compiled := if stockEnabled',start);old=s[start:end]
# Prepend one complete action; preserve the complete old action byte-for-byte.
new=old.replace('let returnPinEnabled := !opt && !tailOn && SC0.funcs.any (fun fi =>\n    Backend.Stock.MemorySretCopy.eligible fi.func || (Backend.Stock.VoidCall.sourceData? fi.func).isSome ||\n    (Backend.Stock.ResultCall.sourceData? fi.func).isSome)','let liveCallEnabled := !opt && !tailOn && SC0.funcs.any (fun fi =>\n    (Backend.Stock.LiveCall.sourceData? fi.func).isSome)')
new=new.replace('if returnPinEnabled then','if liveCallEnabled then').replace('Backend.Stock.ResultCall.lowerValidated','Backend.Stock.LiveCall.lowerValidated').replace('Link.ResultCallCompilerWith','Link.LiveCallCompilerWith')
s=s[:start]+new+s[start:];assert old in s;write(n,s)
n='FVTest/E2E/LinkCheckMain.lean';s=(P/n).read_text();s='import FV.Backend.Lowering.StockLiveCallRoutes\nimport FV.E2E.LiveCallChecks\nimport FVTest.E2E.LiveCallLinkProofWith\n'+s
marker='  -- Reproduce complete mode admission before choosing a new per-function default.\n'
s=s.replace(marker,'''  let liveMode := I0.funcs.any (fun fi => (Stock.LiveCall.sourceData? fi.func).isSome) &&
    I0.funcs.all (fun fi => match Stock.LiveCall.lowerValidated fi.func with
      | .error _ => false
      | .ok raw => SemanticABI.checkLiveCalls fi.func raw)
'''+marker,1)
s=s.replace('(SemanticABI.checkResultCalls f a.vc || lowerOkTSB f a.vc)','(SemanticABI.checkLiveCalls f a.vc || lowerOkTSB f a.vc)')
s=s.replace('if resultMode && routeMatches Stock.ResultCall.lowerValidated then none','if (liveMode && routeMatches Stock.LiveCall.lowerValidated) ||\n            (!liveMode && resultMode && routeMatches Stock.ResultCall.lowerValidated) then none')
s=s.replace('let actualLower := Stock.ResultCall.lowerWithRoutes choices','let actualLower := if liveMode then Stock.LiveCall.lowerWithRoutes choices\n    else Stock.ResultCall.lowerWithRoutes choices')
s=s.replace('let lowerName := "(Backend.Stock.ResultCall.lowerWithRoutes [" ++','let lowerName := (if liveMode then "(Backend.Stock.LiveCall.lowerWithRoutes ["\n    else "(Backend.Stock.ResultCall.lowerWithRoutes [") ++')
s=s.replace('  if o.profile then','  let lowerImport := if liveMode then "FV.Backend.Lowering.StockLiveCallRoutes"\n    else "FV.Backend.Lowering.StockResultCallRoutes"\n  let admissionExtra := if liveMode then returnPinLiveCallsExtra else returnPinResultCallsExtra\n  if o.profile then',1)
s=s.replace('let lc := Backend.SemanticABI.checkResultCalls f a.vc','let lc := if liveMode then Backend.SemanticABI.checkLiveCalls f a.vc\n        else Backend.SemanticABI.checkResultCalls f a.vc')
s=s.replace('staticChksSemanticFor returnPinResultCallsExtra','staticChksSemanticFor admissionExtra')
s=s.replace('(lowerImport := "FV.Backend.Lowering.StockResultCallRoutes")','(lowerImport := lowerImport)')
old='      else FVTest.E2E.ResultCallLinkProofWith.leanFilesResultCallWith lowerName'
new='''      else if liveMode then FVTest.E2E.LiveCallLinkProofWith.leanFilesLiveCallWith lowerName I' (funcs.map (·.2)) entries out o.module exe o.deadCleanup noTls stackS stackGood bg (lowerImport := lowerImport)
      else FVTest.E2E.ResultCallLinkProofWith.leanFilesResultCallWith lowerName'''
assert old in s;s=s.replace(old,new,1);write(n,s)
state={'status':'source_only_not_verified','prior_packet':'direct-call-production-class-packet-v1 immutable complete49-source predecessor','files':{n:hashlib.sha256((Q/n).read_bytes()).hexdigest() for n in ['FVTest/Backend/Main.lean','FVTest/Link/LeanLinkMain.lean','FVTest/E2E/LinkCheckMain.lean']},'entire_previous_linker_action_retained':True,'old_explicit_routes_unchanged':True,'new_route_index':None,'frozen_constructor_files_unchanged':True}
(Q/'live-cli-source-preparation-v1.json').write_text(json.dumps(state,indent=2)+'\n');print('Three CLI source drafts staged. No kernel or runtime pass claimed.')
