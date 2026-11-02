from pathlib import Path
import hashlib,json
Q=Path(__file__).resolve().parent;P=Q.parent/'direct-call-production-class-packet-v1';C=Q/'reviewed-live-admission-before-consumers-v1';C.mkdir()
files=json.loads((Q/'live-shared-inventory-v1.json').read_text())
# Preserve all current shared admission sources before the additive profile lemma.
saved={}
for p in [*Q.glob('FV/E2E/*.lean'),Q/'FV/Backend/SemanticABICheck.lean']:
 if p.name.startswith('StockLiveCall'):continue
 n=p.relative_to(Q);d=C/n;d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(p.read_bytes());saved[str(n)]=hashlib.sha256(p.read_bytes()).hexdigest()
(C/'manifest.json').write_text(json.dumps(saved,indent=2)+'\n')
def write(n,text):
 p=Q/n;assert not p.exists(),n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
# Thin profile aliases reuse one already-proved binary/executable/checker/stack kernel.
for name in ['Binary','Exec','Checks','GeneratedStack']:
 source=(P/f'FV/E2E/ResultCall{name}.lean').read_text().replace('ResultCall','LiveCall').replace('.resultCalls','.liveCalls')
 if name=='Checks':
  source=source.replace('import FV.E2E.ReturnPinChecksWith','import FV.E2E.ResultCallChecks')
  source=source.replace('okRReturnPinLiveCalls_previous (ReturnPinChecksWith.accepts_previous lower I cleanup previous)','okRReturnPinLiveCalls_previous (ResultCallChecks.accepts_previous lower I cleanup previous)')
 write(f'FV/E2E/LiveCall{name}.lean',source)
source=(P/'FV/Link/ResultCallExeWith.lean').read_text().replace('ResultCall','LiveCall').replace('.resultCalls','.liveCalls')
source=source.replace('import FV.Link.ReturnPinExeSourceWith','import FV.Link.ResultCallExeWith')
source=source.replace('ReturnPinCompilerWith.attempt','ResultCallCompilerWith.attempt').replace('okRReturnPinCalls (productionStage','okRReturnPinResultCalls (productionStage')
source=source.replace('ResultCallCompilerWith.accepts_previous previous','ResultCallCompilerWith.accepts_previous_semantic previous')
write('FV/Link/LiveCallExeWith.lean',source)
source=(P/'FVTest/E2E/ResultCallLinkProofWith.lean').read_text().replace('ResultCall','LiveCall').replace('.resultCalls','.liveCalls')
# ProofApi is a record. Add one profile without changing the old emitter or its profile values.
source=source.replace('def leanFilesLiveCallWith', '''def ReturnPinLinkProofWith.ProofApi.liveCalls : ReturnPinLinkProofWith.ProofApi :=
  ⟨"FV.E2E.LiveCallChecks", "LiveCallChecks", "FV.E2E.LiveCallGeneratedStack",
    "LiveCallGeneratedStack", "LiveCallBinary", "okRReturnPinLiveCalls"⟩

def leanFilesLiveCallWith''')
# Fully qualify the profile because this namespace is a sibling of the generic emitter.
source=source.replace('leanFilesReturnPinFor .liveCalls','leanFilesReturnPinFor ReturnPinLinkProofWith.ProofApi.liveCalls')
write('FVTest/E2E/LiveCallLinkProofWith.lean',source)
# Old profiles and rejection interfaces stay unchanged. Only the new live profile gets this lemma.
p=Q/'FV/E2E/ReturnPinAdmission.lean';text=p.read_text();assert text.endswith('end E2E.LinkCheck\n')
text=text[:-len('end E2E.LinkCheck\n')]+'''/-- The live-result profile preserves every complete result-call program acceptance. -/
theorem okRReturnPinLiveCalls_previous {stage : Clif.Function → VCode → VCode}
    {I : LinkInput} {R : Res} (previous : okRReturnPinResultCalls stage I R = true) :
    okRReturnPinLiveCalls stage I R = true := by
  simp only [okRReturnPinResultCalls,okRReturnPinFor,Bool.and_eq_true] at previous
  simp only [okRReturnPinLiveCalls,okRReturnPinFor,Bool.and_eq_true]
  refine ⟨?_,previous.2⟩
  simp only [okRSemanticFor,chksSemanticFor,List.all_append,Bool.and_eq_true,List.all_eq_true] at previous ⊢
  refine ⟨previous.1.1,?_⟩
  intro e member
  have old := previous.1.2 e member
  refine ⟨?_,old.2⟩
  simp only [staticChksSemanticFor,List.all_map,List.all_eq_true,Function.comp_def] at old ⊢
  intro check present
  obtain ⟨raw,rawMember,rfl⟩ := List.mem_map.mp present
  have accepted := old.1 _ (List.mem_map.mpr ⟨raw,rawMember,rfl⟩)
  by_cases named : raw.1 = "compiled: lowerCheck"
  · simp only [named,↓reduceIte] at accepted ⊢
    simpa only [ReturnPinAdmission.liveCalls,ReturnPinAdmission.resultCalls,
      returnPinLiveCallsExtra,← Bool.or_assoc,accepted,Bool.true_or]
  · simpa only [named,↓reduceIte] using accepted

end E2E.LinkCheck
''';p.write_text(text)
print('Prepared six thin consumer modules and additive admission preservation; NOT YET VERIFIED')
