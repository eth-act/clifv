import FV.E2E.SemanticBinaryGood
import FV.E2E.SemanticBinaryTS
import FV.E2E.BinaryGoodT

/-! # Typed copies of `FV.E2E.SemanticBinaryGood` (#722)

The declarations of `FV.E2E.SemanticBinaryGood` that depend on the link contract, for the typed
contract `LinkSys.OkT` and the typed checks `SemanticStackBound.okBTS` (suffix `TS`). -/

namespace E2E
set_option autoImplicit false
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck

namespace SemanticStackBound

/-- `ProgStmtSTS` with `RunGoodL` for a returning or trapping outcome. -/
def ProgStmtSXTS (L : LinkSys) (I : SemanticStackBound.CompilerInput) (n : String) : Prop :=
  ∀ (f : Clif.Function), L.P.func? n = some f →
  ∀ (M : Nat) (ra : BitVec 64) (s w₀ : Arm.ArmState) (args : List Clif.Val) (cs : Clif.State),
    AbiEntry (L.A f).fb (L.A f).base ra s →
    stackFn I f ≤ (spv s).toNat → (∀ a, L.Img a → ¬ StackBelow (stackFn I f) (spv s) a) →
    L.F = frameWG (bud I f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s →
    (∀ a, L.Img a → s.mem a = L.imgMem a) →
    BodyEntry (L.A f).af s w₀ → ArgsIn f.sig args s → ClifEntry f args cs →
    StackArgsAvoid L.Img f.sig args s →
    Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀ →
    (L.NeedSlots → L.PlaceAt cs.mem (spv w₀)) →
    TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs →
    ArmRefinesT (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs) ∧
      ((∃ vals cm, Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) ∨
        (∃ c, Clif.runLoop L.base L.P (M + 1) cs = .trapped c) → L.RunGoodL M f s)

/-- `StackStmtTS` with `ProgStmtSXTS`. -/
def StackStmtXTS (I : SemanticStackBound.CompilerInput) (n : String) : Prop :=
  ∀ (B : BaseEnv) (F : BitVec 64 → Prop), BaseOk (ofInput I B F) →
    (∀ a, (ofInput I B F).Img a → F a) → ProgStmtSXTS (ofInput I B F) I n

/-- `crate_correct_stackNTS` with `RunGoodL` for a returning or trapping outcome. -/
theorem crate_correct_stackNXTS {I : SemanticStackBound.CompilerInput} (hI : okBTS I = true)
    {n : String} (hn : goodN I n = true) : StackStmtXTS I n := by
  intro B F hB hFI f hf M _ _ _ _ _ hent hroom hgfree hFeq himg hbe hargs hcs hsav hrel hpl htr
  have hf' : (progOf I.results).func? n = some f := hf
  unfold goodN at hn
  rw [hf'] at hn
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hn
  have hbud : bud I f = b := by simp [bud, hb]
  exact backend_correct_program_stackXT _ (okBTS_sound hI hB hFI) (budget_ofTS hI B F) (bud I f)
    (fun M => by simp [LinkSys.hybrid, hb, hbud]) (Clif.Program.func?_some hf).1 M hent hroom
    hgfree hFeq himg hbe hargs hcs hsav hrel hpl htr

end SemanticStackBound

namespace SemanticBinary

/-- `binary_correctTS` with `RunGoodL` of the model's run for a returning or trapping outcome. -/
theorem binary_correctXTS {I : SemanticStackBound.CompilerInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFactsTS I X R roB) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} (hn : SemanticStackBound.goodN I n = true)
    {f : Clif.Function} (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : X.Intact r)
    (ho : OutsideCall I roB f (SemanticStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefinesT (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    (∀ a, (modelOf I f r).mem a ≠ r.mem a → R a) ∧
    ((∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c) →
      (sys I B).RunGoodL M f (modelOf I f r)) := by
  have hB' : BaseOk (SemanticStackBound.ofInput I B (worldF I f (SemanticStackBound.bud I f) r)) :=
    baseOk_F hB
  have himgF : ∀ a, (SemanticStackBound.ofInput I B (worldF I f (SemanticStackBound.bud I f) r)).Img a →
      worldF I f (SemanticStackBound.bud I f) r a := fun _ h => .inr h
  have hL := SemanticStackBound.okBTS_sound hbin.ok hB' himgF
  have hro : ∀ a b, roB a = some b → r.mem a = b := fun a b h =>
    hX a b (hbin.data a b h).1 (hbin.data a b h).2
  obtain ⟨hent, -, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ :=
    premisesTS hL (Clif.Program.func?_some hf).1 hro ho hr
  obtain ⟨hA, hG⟩ := SemanticStackBound.crate_correct_stackNXTS hbin.ok hn B _ hB' himgF f hf M _ _ _
    args cs hent (by rw [spv_modelOf]; exact ho.stack) hgfree rfl himg hbe hargs hr.entry hsav hrel
    hpl htr
  refine ⟨?_, (binary_correctTS hbin B hB hn hf M hX ho hr htr).2, fun hout => runGoodL_F (hG hout)⟩
  rw [mach_F I B (fun _ => False) (worldF I f (SemanticStackBound.bud I f) r)]
  exact hA

/-- **The model state differs from `r` only at the bytes `R`**. -/
theorem BinFactsTS.modelOf_ne {I : SemanticStackBound.CompilerInput} {X : Image}
    {R : BitVec 64 → Prop} {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFactsTS I X R roB)
    {f : Clif.Function} {r : Arm.ArmState} (hX : X.Intact r) :
    ∀ a, (modelOf I f r).mem a ≠ r.mem a → R a := by
  intro a hne
  by_cases hi : img I a
  · rw [mem_modelOf_img hi] at hne
    rcases (hbin.code a hi).2 with h | h
    · exact absurd (hX a _ (hbin.code a hi).1 h).symm hne
    · exact h
  · exact absurd (mem_modelOf_not hi) hne

/-- **`binary_correctXTS` for any program, recursive ones included** (`binary_correct_depthX`
with `OkT`; the stack premise `frameDrop + (D * M + pbMax I)`, #581: with the stack probes of the
deepest activation). -/
theorem binary_correct_depthXTS {I : SemanticStackBound.CompilerInput} {X : Image}
    {R : BitVec 64 → Prop} {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFactsTS I X R roB)
    (B : BaseEnv) (hB : BaseOk (sys I B)) {n : String} {f : Clif.Function}
    (hf : (prog I).func? n = some f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : X.Intact r)
    (ho : OutsideCall I roB f (frameDrop (art I f).af + (I.D * M + pbMax I)) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefinesT (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    (∀ a, (modelOf I f r).mem a ≠ r.mem a → R a) ∧
    ((∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c) →
      (sys I B).RunGoodL M f (modelOf I f r)) := by
  have hB' : BaseOk (SemanticStackBound.ofInput I B (worldF I f (I.D * M + pbMax I) r)) := baseOk_F hB
  have himgF : ∀ a, (SemanticStackBound.ofInput I B (worldF I f (I.D * M + pbMax I) r)).Img a →
      worldF I f (I.D * M + pbMax I) r a := fun _ h => .inr h
  have hL := SemanticStackBound.okBTS_sound hbin.ok hB' himgF
  have hro : ∀ a b, roB a = some b → r.mem a = b := fun a b h =>
    hX a b (hbin.data a b h).1 (hbin.data a b h).2
  obtain ⟨hent, hres, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ :=
    premisesTS hL (Clif.Program.func?_some hf).1 hro ho hr
  obtain ⟨hA, hG⟩ := backend_correct_program_budgetXT _ hL (LinkSys.budget_KT _ hL)
    (Clif.Program.func?_some hf).1 M hent
    ⟨hres, (LinkSys.budget_KT _ hL).2 M f (Clif.Program.func?_some hf).1⟩ rfl hgfree
    himg hbe hargs hr.entry hsav hrel hpl htr
  refine ⟨?_, hbin.modelOf_ne hX, fun hout => runGoodL_F (hG hout)⟩
  rw [mach_F I B (fun _ => False) (worldF I f (I.D * M + pbMax I) r)]
  exact hA

/-- **`binary_correct_depthXTS` for the run's peak call depth** (`binary_correct_peakX` with
`OkT`; the stack premise `frameDrop + (D * d + pbMax I)`, #581). -/
theorem binary_correct_peakXTS {I : SemanticStackBound.CompilerInput} {X : Image}
    {R : BitVec 64 → Prop} {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFactsTS I X R roB)
    (B : BaseEnv) (hB : BaseOk (sys I B)) {n : String} {f : Clif.Function}
    (hf : (prog I).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : X.Intact r)
    (ho : OutsideCall I roB f (frameDrop (art I f).af + (I.D * d + pbMax I)) r args cs.mem)
    (hr : ClifRun I B f r args cs) (hd : Clif.DepthLe B.env (prog I) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog I) B.env F d) (prog I).bare cs) :
    ArmRefinesT (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach d f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (F + 1) cs) ∧
    (∀ a, (modelOf I f r).mem a ≠ r.mem a → R a) ∧
    ((∃ vals cm, Clif.runLoop B.env (prog I) (F + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (F + 1) cs = .trapped c) →
      (sys I B).RunGoodL d f (modelOf I f r)) := by
  have hB' : BaseOk (SemanticStackBound.ofInput I B (worldF I f (I.D * d + pbMax I) r)) := baseOk_F hB
  have himgF : ∀ a, (SemanticStackBound.ofInput I B (worldF I f (I.D * d + pbMax I) r)).Img a →
      worldF I f (I.D * d + pbMax I) r a := fun _ h => .inr h
  have hL := SemanticStackBound.okBTS_sound hbin.ok hB' himgF
  have hro : ∀ a b, roB a = some b → r.mem a = b := fun a b h =>
    hX a b (hbin.data a b h).1 (hbin.data a b h).2
  obtain ⟨hent, hres, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ :=
    premisesTS hL (Clif.Program.func?_some hf).1 hro ho hr
  obtain ⟨hA, hG⟩ := backend_correct_program_peakXT _ hL (LinkSys.budget_KT _ hL)
    (Clif.Program.func?_some hf).1 F d hent
    ⟨hres, (LinkSys.budget_KT _ hL).2 d f (Clif.Program.func?_some hf).1⟩ rfl hgfree
    himg hbe hargs hr.entry hsav hrel hpl
    hd htr
  refine ⟨?_, hbin.modelOf_ne hX, fun hout => runGoodL_F (hG hout)⟩
  rw [mach_F I B (fun _ => False) (worldF I f (I.D * d + pbMax I) r)]
  exact hA

/-- `binary_correct_of_checksTS` with `RunGoodL` of the model's run for a returning or trapping
outcome. -/
theorem binary_correct_of_checksXTS {I : SemanticStackBound.CompilerInput}
    {D : List Clif.DataObject} {file : ByteArray}
    (hI : SemanticStackBound.okBTS I = true) (hbin : BinCheck.BinOkWithResults I I.results D file)
    (B : BaseEnv) (hB : BaseOk (sys I B))
    {n : String} (hn : SemanticStackBound.goodN I n = true) {f : Clif.Function}
    (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (SemanticStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefinesT (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    (∀ a, (modelOf I f r).mem a ≠ r.mem a → BinCheck.RelocAtWithResults I I.results a) ∧
    ((∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c) →
      (sys I B).RunGoodL M f (modelOf I f r)) :=
  binary_correctXTS (binFacts_of_checksTS hI hbin) B hB hn hf M hX ho hr htr

end SemanticBinary

end E2E
