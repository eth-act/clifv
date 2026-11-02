import FV.E2E.ReturnPinBinaryKernel
import FV.E2E.SemanticBinaryGood
import FV.E2E.PreparedReturnPinCalls
import FV.E2E.BinaryBoundaryFacts

namespace E2E.ReturnPinBinary
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.SemanticBinary
set_option autoImplicit false
set_option Elab.async false

def okB (I : SemanticStackBound.CompilerInput) : Bool :=
  okRReturnPinCalls I.stage I.toLinkInput I.results

/-- Every previously checked program keeps its complete binary-checker verdict. -/
theorem okB_previous {I : SemanticStackBound.CompilerInput} (previous : SemanticStackBound.okB I = true) :
    okB I = true :=
  okRReturnPinCalls_previous (okRReturnPins_of_previous I.stage
    (I.toLinkInput.resultsProductionWith_prepared I.lower I.cleanup) previous)

theorem okB_sound {I : SemanticStackBound.CompilerInput} (checked : okB I = true)
    {B : BaseEnv} {F : BitVec 64 → Prop} (base : BaseOk (SemanticStackBound.ofInput I B F))
    (world : ∀ a,(SemanticStackBound.ofInput I B F).Img a → F a) :
    (SemanticStackBound.ofInput I B F).OkSemanticReturnPins := by
  apply E2E.ReturnPinBinaryFor.okB_sound (admission := ReturnPinAdmission.previous) <;> first | assumption

theorem binary_correct_depth {I : SemanticStackBound.CompilerInput} (checked : okB I = true) (B : BaseEnv)
    (base : BaseOk (sys I B)) {n : String} {f : Clif.Function} (found : (prog I).func? n = some f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (outside : OutsideCall I (fun _ => none) f (frameDrop (art I f).af + I.D*M) r args cs.mem)
    (source : ClifRun I B f r args cs)
    (traps : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M+1) cs) := by
  apply E2E.ReturnPinBinaryFor.binary_correct_depth (admission := ReturnPinAdmission.previous) <;> first | assumption

structure BinFacts (I : SemanticStackBound.CompilerInput) (X : Image) (R : BitVec 64 → Prop)
    (roB : BitVec 64 → Option (BitVec 8)) : Prop where
  ok : okB I = true
  code : ∀ a, img I a → X.kept a ∧ (X.mem a = some (imgMem I a) ∨ R a)
  data : ∀ a b, roB a = some b → X.kept a ∧ X.mem a = some b

theorem BinFacts.previous {I : SemanticStackBound.CompilerInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (previous : SemanticBinary.BinFacts I X R roB) :
    BinFacts I X R roB := ⟨okB_previous previous.ok,previous.code,previous.data⟩

theorem BinFacts.modelOf_ne {I : SemanticStackBound.CompilerInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFacts I X R roB) {f : Clif.Function}
    {r : Arm.ArmState} (hX : X.Intact r) : ∀ a, (modelOf I f r).mem a ≠ r.mem a → R a := by
  exact E2E.ReturnPinBinaryFor.BinFacts.modelOf_ne (admission := ReturnPinAdmission.previous)
    (I := I) (X := X) (R := R) (roB := roB) (f := f) (r := r)
    ⟨hbin.ok,hbin.code,hbin.data⟩ hX

theorem binary_correct_depthX {I : SemanticStackBound.CompilerInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFacts I X R roB) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : X.Intact r)
    (ho : OutsideCall I roB f (frameDrop (art I f).af + I.D * M) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    (∀ a, (modelOf I f r).mem a ≠ r.mem a → R a) ∧
    ((∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c) →
      (sys I B).RunGoodL M f (modelOf I f r)) := by
  apply E2E.ReturnPinBinaryFor.binary_correct_depthX (admission := ReturnPinAdmission.previous) <;> first | assumption | exact ⟨hbin.ok,hbin.code,hbin.data⟩

theorem binary_correct_peakX {I : SemanticStackBound.CompilerInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFacts I X R roB) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : X.Intact r)
    (ho : OutsideCall I roB f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    (hr : ClifRun I B f r args cs) (hd : Clif.DepthLe B.env (prog I) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog I) B.env F d) (prog I).bare cs) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach d f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (F + 1) cs) ∧
    (∀ a, (modelOf I f r).mem a ≠ r.mem a → R a) ∧
    ((∃ vals cm, Clif.runLoop B.env (prog I) (F + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (F + 1) cs = .trapped c) →
      (sys I B).RunGoodL d f (modelOf I f r)) := by
  apply E2E.ReturnPinBinaryFor.binary_correct_peakX (admission := ReturnPinAdmission.previous) <;> first | assumption | exact ⟨hbin.ok,hbin.code,hbin.data⟩

theorem binFacts_of_checks {I : SemanticStackBound.CompilerInput} {D : List Clif.DataObject} {file : ByteArray}
    (hI : okB I = true) (hB : BinCheck.BinOkWithResults I I.results D file) :
    BinFacts I (imageOf file) (BinCheck.RelocAtWithResults I I.results) (BinCheck.roByte I D) where
  ok := hI
  code := (E2E.ReturnPinBinaryFor.binFacts_of_checks (admission := ReturnPinAdmission.previous) hI hB).code
  data := (E2E.ReturnPinBinaryFor.binFacts_of_checks (admission := ReturnPinAdmission.previous) hI hB).data


end E2E.ReturnPinBinary

namespace E2E.ReturnPinStackBound
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.StackBound E2E.SemanticStackBound
set_option autoImplicit false
set_option Elab.async false
abbrev CompilerInput := SemanticStackBound.CompilerInput
abbrev okB := ReturnPinBinary.okB
abbrev ofInput := SemanticStackBound.ofInput

theorem okB_names {I : CompilerInput} (checked : okB I = true) :
    ((progOf I.results).funcs.map (·.name)).Nodup := by
  apply E2E.ReturnPinStackBoundFor.okB_names (admission := ReturnPinAdmission.previous) <;> first | assumption

theorem facts {I : CompilerInput} (checked : okB I = true) {g : Clif.Function}
    (member : g ∈ (progOf I.results).funcs) :
    SemanticPreparedFactsFor returnPinCallsExtra I.stage I.toLinkInput I.results g (artOf I.results g) := by
  apply E2E.ReturnPinStackBoundFor.facts (admission := ReturnPinAdmission.previous) <;> first | assumption

theorem edgeB_of_callee {I : CompilerInput} (hI : okB I = true) {B : BaseEnv}
    {F : BitVec 64 → Prop} {g h : Clif.Function} (hg : g ∈ (progOf I.results).funcs)
    (hc : (ofInput I B F).Callee g h) : edgeB (fun n => I.syms.lookup n) g h = true := by
  apply E2E.ReturnPinStackBoundFor.edgeB_of_callee (admission := ReturnPinAdmission.previous) <;> first | assumption

theorem goodN_iff {I : CompilerInput} (hI : okB I = true) {n : String} :
    SemanticStackBound.goodN I n = true ↔
      ∃ f, (progOf I.results).func? n = some f ∧ ¬ SemanticStackBound.CycleFrom (SemanticStackBound.Calls I I.results) f := by
  apply E2E.ReturnPinStackBoundFor.goodN_iff (admission := ReturnPinAdmission.previous) <;> first | assumption

theorem budget_of {I : CompilerInput} (hI : okB I = true) (B : BaseEnv) (F : BitVec 64 → Prop) :
    (ofInput I B F).Budget ((ofInput I B F).hybrid (SemanticStackBound.budO I) (SemanticStackBound.budMax I)) := by
  apply E2E.ReturnPinStackBoundFor.budget_of (admission := ReturnPinAdmission.previous) <;> first | assumption

variable {modes : Clif.Function → ReturnPinMode}
theorem backend_correct_program_stackX (L : LinkSys) (hL : L.OkReturnPins modes) {κ : Nat → Clif.Function → Nat}
    (hκ : L.Budget κ) {f : Clif.Function} (b : Nat) (hb : ∀ M, κ M f = b)
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s)
    (hroom : frameDrop (L.A f).af + b ≤ (spv s).toNat)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + b) (spv s) a)
    (hF : L.F = frameWG b (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs) ∧
      ((∃ vals cm, Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) ∨
        (∃ c, Clif.runLoop L.base L.P (M + 1) cs = .trapped c) → L.RunGoodL M f s) := by
  apply E2E.ReturnPinStackBoundFor.backend_correct_program_stackX <;> first | assumption

theorem crate_correct_stackNX {I : SemanticStackBound.CompilerInput} (hI : okB I = true) {n : String}
    (hn : SemanticStackBound.goodN I n = true) : SemanticStackBound.StackStmtX I n := by
  apply E2E.ReturnPinStackBoundFor.crate_correct_stackNX (admission := ReturnPinAdmission.previous) <;> first | assumption

end E2E.ReturnPinStackBound

namespace E2E.ReturnPinBinary
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.SemanticBinary E2E.SemanticStackBound
theorem binary_correctX {I : SemanticStackBound.CompilerInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFacts I X R roB) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} (hn : SemanticStackBound.goodN I n = true) {f : Clif.Function}
    (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : X.Intact r)
    (ho : OutsideCall I roB f (SemanticStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    (∀ a, (modelOf I f r).mem a ≠ r.mem a → R a) ∧
    ((∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c) →
      (sys I B).RunGoodL M f (modelOf I f r)) := by
  apply E2E.ReturnPinBinaryFor.binary_correctX (admission := ReturnPinAdmission.previous) <;> first | assumption | exact ⟨hbin.ok,hbin.code,hbin.data⟩

end E2E.ReturnPinBinary

namespace E2E.ReturnPinBinary
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.SemanticBinary
variable {modes : Clif.Function → ReturnPinMode}
theorem trapsExplicit_of_run {L : LinkSys} (hL : L.OkReturnPins modes) {f : Clif.Function} (hf : f ∈ L.P.funcs)
    {M : Nat} {args : List Clif.Val} {cs : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (hcs : ClifEntry f args cs) (hsym : cs.mem.symbols = L.syms)
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) :
    TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs := by
  apply E2E.ReturnPinBinaryFor.trapsExplicit_of_run <;> first | assumption

end E2E.ReturnPinBinary

namespace E2E.ReturnPinBinary
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.SemanticBinary
variable {modes : Clif.Function → ReturnPinMode}
theorem trapsExplicit_of_runD {L : LinkSys} (hL : L.OkReturnPins modes) {f : Clif.Function} (hf : f ∈ L.P.funcs)
    {F d : Nat} {args : List Clif.Val} {cs : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (hcs : ClifEntry f args cs) (hsym : cs.mem.symbols = L.syms)
    (hd : Clif.DepthLe L.base L.P d cs)
    (hrun : Clif.runLoop L.base L.P (F + 1) cs = .returned vals cm) :
    TrapsExplicit (Clif.linkEnvD L.P L.base F d) L.P.bare cs := by
  apply E2E.ReturnPinBinaryFor.trapsExplicit_of_runD <;> first | assumption

/-! ## The binary facts -/


end E2E.ReturnPinBinary
