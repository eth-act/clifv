import FV.E2E.LinkGood
import FV.E2E.Binary

/-! # The per-state facts of the run through the stack-bound and binary theorems (L3 (c))

`backend_correct_program_budgetX` (`FV/E2E/LinkGood.lean`) adds to the whole-program theorem, for a
returning or trapping outcome, `RunGoodL`: the per-state facts of every state of the linked run
whose step ends without error. Here they are carried through the stack-bound wrappers
(`backend_correct_program_stackX`, `crate_correct_stackNX`) and the binary-level theorems
(`binary_correctX`, `binary_correct_of_checksX`), across the exterior `F` of the proof's linked
system (`runGoodL_F`: the linked machine does not depend on it). -/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- `backend_correct_program_stack` with `RunGoodL` for a returning or trapping outcome. -/
theorem backend_correct_program_stackX (L : LinkSys) (hL : L.Ok) {κ : Nat → Clif.Function → Nat}
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
  have hd := L.frameDrop_eq hL hf
  have hres : StackAvail b (L.A f).af s := by
    unfold StackAvail
    rw [show (L.A f).af.frameSize + 16 + b = frameDrop (L.A f).af + b by omega]
    refine stackRoom_of hroom fun a ha => hgfree a (hL.imgAddr f hf a ?_)
    simpa [CodeAddr, hent.program] using ha
  rw [← hb M] at hres hF hgfree
  exact backend_correct_program_budgetX L hL hκ hf M hent hres hF hgfree himg hbe hargs hcs hsav
    hrel hpl htr

namespace StackBound

open LinkCheck

/-- `ProgStmtS` with `RunGoodL` for a returning or trapping outcome. -/
def ProgStmtSX (L : LinkSys) (I : LinkInput) (n : String) : Prop :=
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
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs) ∧
      ((∃ vals cm, Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) ∨
        (∃ c, Clif.runLoop L.base L.P (M + 1) cs = .trapped c) → L.RunGoodL M f s)

/-- `StackStmt` with `ProgStmtSX`. -/
def StackStmtX (I : LinkInput) (n : String) : Prop :=
  ∀ (B : BaseEnv) (F : BitVec 64 → Prop), BaseOk (LinkSys.ofInput I B F) →
    (∀ a, (LinkSys.ofInput I B F).Img a → F a) → ProgStmtSX (LinkSys.ofInput I B F) I n

/-- `crate_correct_stackN` with `RunGoodL` for a returning or trapping outcome. -/
theorem crate_correct_stackNX {I : LinkInput} (hI : okB I = true) {n : String}
    (hn : goodN I n = true) : StackStmtX I n := by
  intro B F hB hFI f hf M _ _ _ _ _ hent hroom hgfree hFeq himg hbe hargs hcs hsav hrel hpl htr
  have hf' : (progOf I.results).func? n = some f := hf
  unfold goodN at hn
  rw [hf'] at hn
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hn
  have hbud : bud I f = b := by simp [bud, hb]
  exact backend_correct_program_stackX _ (okB_sound hI hB hFI) (budget_of hI B F) (bud I f)
    (fun M => by simp [LinkSys.hybrid, hb, hbud]) (Clif.Program.func?_some hf).1 M hent hroom
    hgfree hFeq himg hbe hargs hcs hsav hrel hpl htr

end StackBound

namespace Binary

open LinkCheck

/-! ## `RunGoodL` does not depend on the exterior `F` -/

theorem reachL_F {I : LinkInput} {B : BaseEnv} {F F' : BitVec 64 → Prop} {M : Nat}
    {f : Clif.Function} {c : Arm.ArmState} {M' : Nat} {g : Clif.Function} {c' t : Arm.ArmState}
    (h : (LinkSys.ofInput I B F').ReachL M f c M' g c' t) :
    (LinkSys.ofInput I B F).ReachL M f c M' g c' t := by
  induction h with
  | act hj =>
    rw [mach_F I B F' F] at hj ⊢
    exact .act hj
  | nest hj hc herr _ ih =>
    rw [mach_F I B F' F] at hj hc herr ih
    exact .nest hj hc herr ih

theorem goodAt_F {I : LinkInput} {B : BaseEnv} {F F' : BitVec 64 → Prop} {M : Nat}
    {g : Clif.Function} {c t : Arm.ArmState} (h : (LinkSys.ofInput I B F).GoodAt M g c t) :
    (LinkSys.ofInput I B F').GoodAt M g c t := by
  obtain ⟨X, K, G, gv, heq, hg, hi⟩ := h
  rw [hooks_F I B F F' M, mach_F I B F F' M] at heq
  rw [hooks_F I B F F' M] at hg
  exact ⟨X, K, G, gv, heq, hg, hi⟩

/-- **`RunGoodL` does not depend on the exterior `F`** of the linked system. -/
theorem runGoodL_F {I : LinkInput} {B : BaseEnv} {F F' : BitVec 64 → Prop} {M : Nat}
    {f : Clif.Function} {c : Arm.ArmState} (h : (LinkSys.ofInput I B F).RunGoodL M f c) :
    (LinkSys.ofInput I B F').RunGoodL M f c := fun M' g c' t hR he =>
  goodAt_F (h M' g c' t (reachL_F hR) (by rw [mach_F I B F F']; exact he))

/-! ## The binary-level theorems -/

/-- `binary_correct` with `RunGoodL` of the model's run for a returning or trapping outcome. -/
theorem binary_correctX {I : LinkInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFacts I X R roB) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} (hn : StackBound.goodN I n = true) {f : Clif.Function}
    (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : X.Intact r)
    (ho : OutsideCall I roB f (StackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    (∀ a, (modelOf I f r).mem a ≠ r.mem a → R a) ∧
    ((∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c) →
      (sys I B).RunGoodL M f (modelOf I f r)) := by
  have hB' : BaseOk (LinkSys.ofInput I B (worldF I f (StackBound.bud I f) r)) := baseOk_F hB
  have himgF : ∀ a, (LinkSys.ofInput I B (worldF I f (StackBound.bud I f) r)).Img a →
      worldF I f (StackBound.bud I f) r a := fun _ h => .inr h
  have hL := okB_sound hbin.ok hB' himgF
  have hro : ∀ a b, roB a = some b → r.mem a = b := fun a b h =>
    hX a b (hbin.data a b h).1 (hbin.data a b h).2
  obtain ⟨hent, -, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ :=
    premises hL (Clif.Program.func?_some hf).1 hro ho hr
  obtain ⟨hA, hG⟩ := StackBound.crate_correct_stackNX hbin.ok hn B _ hB' himgF f hf M _ _ _ args
    cs hent (by rw [spv_modelOf]; exact ho.stack) hgfree rfl himg hbe hargs hr.entry hsav hrel hpl
    htr
  refine ⟨?_, (binary_correct hbin B hB hn hf M hX ho hr htr).2, fun hout => runGoodL_F (hG hout)⟩
  rw [mach_F I B (fun _ => False) (worldF I f (StackBound.bud I f) r)]
  exact hA

/-- `binary_correct_of_checks` with `RunGoodL` of the model's run for a returning or trapping
outcome. -/
theorem binary_correct_of_checksX {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hI : okB I = true) (hbin : BinCheck.BinOk I D file) (B : BaseEnv) (hB : BaseOk (sys I B))
    {n : String} (hn : StackBound.goodN I n = true) {f : Clif.Function}
    (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (StackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    (∀ a, (modelOf I f r).mem a ≠ r.mem a → BinCheck.RelocAt I a) ∧
    ((∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c) →
      (sys I B).RunGoodL M f (modelOf I f r)) :=
  binary_correctX (binFacts_of_checks hI hbin) B hB hn hf M hX ho hr htr

end Binary

end E2E
