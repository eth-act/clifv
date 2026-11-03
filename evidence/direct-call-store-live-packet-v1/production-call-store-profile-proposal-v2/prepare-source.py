from pathlib import Path
import json,hashlib,shutil,subprocess,difflib
E=Path('/home/lee/clifv/.git/agent-evidence/stock-memory-20261029');Q=E/'direct-call-store-live-packet-v1';old=Q/'production-call-store-profile-proposal-v1';D=Q/'production-call-store-profile-proposal-v2';D.mkdir();shutil.copytree(old/'source',D/'source');support=Q/'production-current-adapter-prep-v2/preserved-support';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();origin={}
for name in ['Binary','Exec','Checks','GeneratedStack']:
 src=support/f'FV/E2E/LiveCall{name}.lean';text=src.read_text().replace('LiveCall','CallStore').replace('ReturnPinAdmission.liveCalls','ReturnPinAdmission.callStores')
 text='import FV.E2E.CallStoreAdmission\n'+text
 if name=='Checks':text=text.replace('import FV.E2E.ResultCallChecks','import FV.E2E.LiveCallChecks').replace('ResultCallChecks.accepts_previous','LiveCallChecks.accepts_previous')
 dest=D/f'source/FV/E2E/CallStore{name}.lean';dest.write_text(text);origin[str(dest.relative_to(D/'source'))]={'source':str(src),'source_sha256':sha(src),'kind':'thin generic-kernel aliases; no copied binary/executable kernel'}
src=support/'FVTest/E2E/LiveCallLinkProofWith.lean';text=src.read_text().replace('LiveCall','CallStore').replace('ProofApi.liveCalls','ProofApi.callStores').replace('"FV.Backend.Lowering.StockCallStoreRoutes"','"FV.Backend.General7CallStoreProduction"');dest=D/'source/FVTest/E2E/CallStoreLinkProofWith.lean';dest.parent.mkdir(parents=True);dest.write_text(text);origin[str(dest.relative_to(D/'source'))]={'source':str(src),'source_sha256':sha(src),'kind':'thin existing generic-emitter profile'}
mainLink=subprocess.check_output(['git','show','2c600854:FVTest/Link/LeanLinkMain.lean'],text=True);start=mainLink.index('  let returnPinEnabled :=');end=mainLink.index('  let compiled :=',start);oldBlock=mainLink[start:end];branch=oldBlock;guardEnd=branch.index('\n  if returnPinEnabled then');branch='  let callStoreEnabled := !opt && !tailOn'+branch[guardEnd:];branch=branch.replace('if returnPinEnabled then','if callStoreEnabled then').replace('Backend.Stock.VoidCall.NI.lowerValidated','Backend.Stock.GeneralLoopCfg7.CallStoreNI.lowerValidated').replace('Link.ReturnPinCompilerWith','Link.CallStoreCompilerWith');newLink='import FV.Backend.General7CallStoreProduction\nimport FV.Link.CallStoreExeWith\n'+mainLink[:start]+branch+mainLink[start:];dest=D/'source/FVTest/Link/LeanLinkMain.lean';dest.parent.mkdir(parents=True);dest.write_text(newLink)
checker=subprocess.check_output(['git','show','2c600854:FVTest/E2E/LinkCheckMain.lean'],text=True);new='import FV.Backend.General7CallStoreProduction\nimport FV.E2E.CallStoreChecks\nimport FVTest.E2E.CallStoreLinkProofWith\n'+checker;marker='  let I0 : LinkInput := { funcs := fis.toList, addrs, syms := [], raStar := 8, D := 0 }\n';assert marker in new;new=new.replace(marker,marker+'''  -- Derive the mode from every actual raw artifact. A typed file retains its previous mode.
  let callStoreMode := I0.funcs.all fun fi =>
    match Stock.GeneralLoopCfg7.CallStoreNI.lowerValidated fi.func with
    | .error _ => false
    | .ok raw => SemanticABI.checkCallStores fi.func raw
''');start=new.index('        if (Stock.MemorySretCopy.eligible f');end=new.index('      (Link.parMap route I0.funcs).filterMap id',start);new=new[:start]+'''        let routeMatches (lower : Clif.Function → Except String VCode) : Bool :=
          match I0.pipeOfWithLowering lower (productionStage o.deadCleanup) fi with
          | .error _ => false
          | .ok a => (checkAlloc a.vcp a.rf).toBool &&
              Backend.Proof.Driver.prepCheck (productionStage o.deadCleanup f a.vc) a.vcp &&
              ((if callStoreMode then SemanticABI.checkCallStores f a.vc
                else SemanticABI.checkCalls f a.vc) || lowerOkTSB f a.vc) && artB I0 rd phs a
        if callStoreMode && routeMatches Stock.GeneralLoopCfg7.CallStoreNI.lowerValidated then none
        else
          let routes := Stock.GeneralLoopCfg7.NI.lowerRoutes.zipIdx
          let probes := if Stock.MemorySretCopy.eligible f || (Stock.VoidCall.sourceData? f).isSome then
              routes.drop 21 ++ routes.take 21
            else routes
          -- An explicit route0 retains legacy artifacts when the new default differs.
          (probes.find? fun (lower,_) => routeMatches lower).map fun (_,index) => (f.name,index)
'''+new[end:];a=new.index('  let actualLower :=');b=new.index('  if o.profile then',a);new=new[:a]+'''  let actualLower := if callStoreMode then Stock.GeneralLoopCfg7.CallStoreNI.lowerWithRoutes choices
    else Stock.GeneralLoopCfg7.NI.lowerWithRoutes choices
  let lowerName := (if callStoreMode then "(Backend.Stock.GeneralLoopCfg7.CallStoreNI.lowerWithRoutes ["
    else "(Backend.Stock.GeneralLoopCfg7.NI.lowerWithRoutes [") ++
    ", ".intercalate (choices.map fun (name,idx) => "(" ++ leanStr name ++ ", " ++ toString idx ++ ")") ++ "])"
  let lowerImport := if callStoreMode then "FV.Backend.General7CallStoreProduction"
    else "FV.Backend.Lowering.StockGeneralLoopCfg7NI"
  let admissionExtra := if callStoreMode then returnPinCallStoresExtra else returnPinCallsExtra
'''+new[b:];new=new.replace('      let lc := Backend.SemanticABI.checkCalls f a.vc','      let lc := if callStoreMode then Backend.SemanticABI.checkCallStores f a.vc\n        else Backend.SemanticABI.checkCalls f a.vc');new=new.replace('staticChksSemanticFor returnPinCallsExtra','staticChksSemanticFor admissionExtra');new=new.replace('(lowerImport := "FV.Backend.Lowering.StockVoidCallNI")','(lowerImport := lowerImport)');oldEmit='''      else FVTest.E2E.ReturnPinLinkProofWith.leanFilesReturnPinWith lowerName I' (funcs.map (·.2)) entries out o.module exe o.deadCleanup noTls stackS stackGood bg (lowerImport := lowerImport)''';assert oldEmit in new;new=new.replace(oldEmit,'''      else if callStoreMode then FVTest.E2E.CallStoreLinkProofWith.leanFilesCallStoreWith lowerName I' (funcs.map (·.2)) entries out o.module exe o.deadCleanup noTls stackS stackGood bg (lowerImport := lowerImport)
'''+oldEmit);(D/'source/FVTest/E2E/LinkCheckMain.lean').write_text(new)
(D/'diffs').mkdir()
for rel in ['FVTest/Backend/Main.lean','FVTest/Link/LeanLinkMain.lean','FVTest/E2E/LinkCheckMain.lean']:
 before=subprocess.check_output(['git','show','2c600854:'+rel],text=True);after=(D/'source'/rel).read_text();(D/'diffs'/rel.replace('/','_')).write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='current/'+rel,tofile='candidate/'+rel)))
assert oldBlock in newLink,'Complete old ReturnPin attempt lost';assert 'SemanticCompilerWith.compileWithRoutes routes SC0 file0 deadCleanup' in newLink;assert checker[checker.index('  let (b, exe)'):checker.index('  let choices :')] != ''
j=json.loads((old/'manifest.json').read_text());j['status']='SOURCE_ONLY;NO_KERNEL_DEFAULT_OR_EXECUTION_CLAIM';j['new_sources']={p.relative_to(D/'source').as_posix():sha(p) for p in (D/'source').rglob('*.lean')};j['prior_source_packet_sha256']=sha(old/'manifest.json');j['thin_alias_origins']=origin;j['staged_existing_path_copies']=['FVTest/Backend/Main.lean','FVTest/Link/LeanLinkMain.lean','FVTest/E2E/LinkCheckMain.lean'];j['complete_previous_linker_action_retained']=True;j['typed_emitter_retained']=True;j['cached_ReturnPinCtx_retained']=True;j['actual_default_probe']='New call-store default first when all actual raw entries pass internal admission; otherwise full General7 predecessor with explicit route recovery.';j['routes']='No new indices. Explicit choices retain all General7 routes0–23 and old out-of-range behavior.';j['remaining']=['Bind complete source/config/native context and import cycles','Focused generic/profile/three-CLI kernels and repository audits','Exact old headers/AX and all accepted stage/identity comparisons','Construct complete return-trace dispatcher and first-fault provider internally','Run actual raw/cleanup three-CLI/generated and linked execution, with original float variant','Flag exact shared CLI boundary before tracked edits and publication'];(D/'manifest.json').write_text(json.dumps(j,indent=2)+'\n');print(sha(D/'manifest.json'),len(j['new_sources']))
