import FV.E2E.LinkSemanticNI
import FV.E2E.PreparedPipeline
import FV.E2E.SemanticPipelineCheck
import FV.E2E.SemanticPreparedMetadata

/-! Pipeline provenance for transactional production attempts. Every successful
artifact retains the original preparation, allocation, emission and layout facts;
the existing source/SSA checks supply source correctness for either attempt. -/
set_option autoImplicit false

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver

structure SemanticPreparedFacts (stage : Clif.Function → VCode → VCode) (I : LinkInput) (R : Res) (g : Clif.Function) (a : Art) : Prop where
  pipe : prepare (stage g a.vc) = .ok a.vcp ∧ lowerRFunc a.vcp a.rf = .ok a.af ∧
    emitFunc a.k a.af = .ok a.fa ∧ a.fa.layout = .ok a.fb ∧
    a.base = BitVec.ofNat 64 (I.baseOf g.name)
  lowerOk : SemanticNI.check g a.vc = true
  prepOk : prepCheck (stage g a.vc) a.vcp = true
  check : checkAlloc a.vcp a.rf = .ok ()
  covered : FormsCovered ⟨a.fa.k, a.af.slotBase⟩
    a.vcp
  rets : allInsts a.vc (retsB g) = true
  outFits : ∀ e ∈ g.externs, ((progOf R).func? e.2.name).isSome = true →
    outFitsB e.2.sig (RAFrame.compute a.vcp a.rf).intBase = true
  nodup : (regLocs g.sig).Nodup
  argReg : ∀ r ∈ regLocs g.sig, r.isArgReg = true
  width : ∀ p ∈ g.sig.params, p.ty.width ≤ 64
  callee : calleeB (progOf R) (fun n => I.syms.lookup n) g = true → (g.slots = [] →
    (RAFrame.compute a.vcp a.rf).size =
      a.af.frameSize - clobberBytes a.af.saves) ∧ slotFitsB g a = true
  sites : allInsts a.vcp (siteB (siteOk (progOf R) g
    (indToB (fun n => I.syms.lookup n) g) a.vcp)) = true
  declSig : ∀ e ∈ g.externs.map (·.2), ∀ h, (progOf R).func? e.name = some h → e.sig = h.sig
  entry : entryB g a.vcp = true
  fits : a.base.toNat + 4 * a.fb.words.size ≤ 2 ^ 64
  ra : raCallB (tabOf R) g a = true
  depth : frameDrop a.af ≤ I.D
  free : Clif.LinkFree g
  subsetE : Compile.functionE g = true
  abi : sigAbiOk g.sig = true ∧ ∀ e ∈ g.externs, sigAbiOk e.2.sig = true
  indOk : indSigsOk g = true
  ind : indB (progOf R) (fun n => I.syms.lookup n) g = true

theorem semanticPreparedFacts (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res} (hR : PreparedResults stage I R) (h : okRSemanticNI stage I R = true) {g : Clif.Function}
    (hg : g ∈ (progOf R).funcs) : SemanticPreparedFacts stage I R g (artOf R g) := by
  have checked : okRSemanticFor (fun _ _ => false) stage I R = true := by
    rw [okRSemanticFor_previous]
    exact h
  have facts := semanticPreparedFactsFor (fun _ _ => false) stage hR checked hg
  exact {
    pipe := facts.pipe
    lowerOk := (by simpa only [Bool.or_false] using facts.lowerOk)
    prepOk := facts.prepOk
    check := facts.check
    covered := facts.covered
    rets := facts.rets
    outFits := facts.outFits
    nodup := facts.nodup
    argReg := facts.argReg
    width := facts.width
    callee := facts.callee
    sites := facts.sites
    declSig := facts.declSig
    entry := facts.entry
    fits := facts.fits
    ra := facts.ra
    depth := facts.depth
    free := facts.free
    subsetE := facts.subsetE
    abi := facts.abi
    indOk := facts.indOk
    ind := facts.ind
  }

theorem semanticPreparedIndFacts (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res} (hR : PreparedResults stage I R) (h : okRSemanticNI stage I R = true) {g : Clif.Function}
    (hg : g ∈ (progOf R).funcs) (hnf : ¬ Clif.IndFree g) :
    ∀ h ∈ (progOf R).funcs, mayB (fun n => I.syms.lookup n) g h.name = true →
      ((∃ sig ∈ indSigs g, LinkSys.IndSigMatch sig h) ∨
        (DeclN g h.name ∧ ∃ sig ∈ indSigs g, LinkSys.IndTyMatch sig h)) →
      (∃ bytes, sigParamBytes h.sig = .ok bytes ∧ bytes.length ≤ 8) ∧
      ∀ sig ∈ indSigs g, LinkSys.IndTyMatch sig h → h.sig.returns.length = sig.returns.length →
        (sigRets h.sig).length = (sigRets sig).length := by
  have checked : okRSemanticFor (fun _ _ => false) stage I R = true := by
    rw [okRSemanticFor_previous]
    exact h
  exact semanticPreparedIndFactsFor (fun _ _ => false) stage hR checked hg hnf

theorem semanticPreparedResults_sound (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res} (hstage : stage = (fun _ => id) ∨ stage = cleanupStage) (hR : PreparedResults stage I R) (hI : okRSemanticNI stage I R = true) {B : BaseEnv}
    {F : BitVec 64 → Prop} (hB : BaseOk (ofRes I R B F)) (hF : ∀ a, (ofRes I R B F).Img a → F a) :
    (ofRes I R B F).OkSemanticNI := by
  have checked : okRSemanticFor (fun _ _ => false) stage I R = true := by
    rw [okRSemanticFor_previous]
    exact hI
  have metadata := semanticPreparedMetadata_sound (fun _ _ => false) stage hR checked hB hF
  refine metadata.toSemanticNI fun g hg => ?_
  have facts := semanticPreparedFacts stage hR hI hg
  obtain ⟨prepared,alloc,emit,layout,_⟩ := facts.pipe
  rcases hstage with rfl | rfl
  · exact CompiledSemanticNI.of_checks (cleanup := false) facts.lowerOk prepared facts.prepOk
      facts.check alloc emit layout
  · exact CompiledSemanticNI.of_checks (cleanup := true) facts.lowerOk prepared facts.prepOk
      facts.check alloc emit layout

end E2E.LinkCheck
