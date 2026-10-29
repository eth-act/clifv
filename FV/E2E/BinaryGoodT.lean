import FV.E2E.BinaryGood
import FV.E2E.LinkGoodT
import FV.E2E.BinaryT
import FV.E2E.BinCheckT
import FV.E2E.LinkArmT
import FV.E2E.LinkCheckT
import FV.E2E.StackBoundT

/-! # Typed copies of `FV.E2E.BinaryGood` (S11e5 Stage C, slice 8)

The declarations of `FV.E2E.BinaryGood` that depend on the integer link contract
(`LinkSys.Ok`, `LinkSys.Thm`, `okB`, `ArmRefines`), for the typed contract `LinkSys.OkT`
(suffix `T`; `LinkSys.Ok.*` as `LinkSys.OkT.*`). -/

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver

/-- `backend_correct_program_stack` with `RunGoodL` for a returning or trapping outcome. -/
theorem backend_correct_program_stackXT (L : LinkSys) (hL : L.OkT) {κ : Nat → Clif.Function → Nat}
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
    ArmRefinesT (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs) ∧
      ((∃ vals cm, Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) ∨
        (∃ c, Clif.runLoop L.base L.P (M + 1) cs = .trapped c) → L.RunGoodL M f s) := by
  have hd := L.frameDrop_eqT hL hf
  have hres : StackAvail b (L.A f).af s := by
    refine ⟨?_, by rw [← hb M]; exact hκ.2 M f hf⟩
    rw [show (L.A f).af.frameSize + 16 + b = frameDrop (L.A f).af + b by omega]
    refine stackRoom_of hroom fun a ha => hgfree a (hL.imgAddr f hf a ?_)
    simpa [CodeAddr, hent.program] using ha
  rw [← hb M] at hres hF hgfree
  exact backend_correct_program_budgetXT L hL hκ hf M hent hres hF hgfree himg hbe hargs hcs hsav
    hrel hpl htr
namespace StackBound
open LinkCheck

/-- `ProgStmtS` with `RunGoodL` for a returning or trapping outcome. -/
def ProgStmtSXT (L : LinkSys) (I : LinkInput) (n : String) : Prop :=
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

/-- `StackStmt` with `ProgStmtSX`. -/
def StackStmtXT (I : LinkInput) (n : String) : Prop :=
  ∀ (B : BaseEnv) (F : BitVec 64 → Prop), BaseOk (LinkSys.ofInput I B F) →
    (∀ a, (LinkSys.ofInput I B F).Img a → F a) → ProgStmtSXT (LinkSys.ofInput I B F) I n

/-- `crate_correct_stackN` with `RunGoodL` for a returning or trapping outcome. -/
theorem crate_correct_stackNXT {I : LinkInput} (hI : okBT I = true) {n : String}
    (hn : goodN I n = true) : StackStmtXT I n := by
  intro B F hB hFI f hf M _ _ _ _ _ hent hroom hgfree hFeq himg hbe hargs hcs hsav hrel hpl htr
  have hf' : (progOf I.results).func? n = some f := hf
  unfold goodN at hn
  rw [hf'] at hn
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hn
  have hbud : bud I f = b := by simp [bud, hb]
  exact backend_correct_program_stackXT _ (okB_soundT hI hB hFI) (budget_ofT hI B F) (bud I f)
    (fun M => by simp [LinkSys.hybrid, hb, hbud]) (Clif.Program.func?_some hf).1 M hent hroom
    hgfree hFeq himg hbe hargs hcs hsav hrel hpl htr
end StackBound
namespace Binary
open LinkCheck

/-- `binary_correct` with `RunGoodL` of the model's run for a returning or trapping outcome. -/
theorem binary_correctXT {I : LinkInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFactsT I X R roB) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} (hn : StackBound.goodN I n = true) {f : Clif.Function}
    (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : X.Intact r)
    (ho : OutsideCall I roB f (StackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefinesT (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    (∀ a, (modelOf I f r).mem a ≠ r.mem a → R a) ∧
    ((∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c) →
      (sys I B).RunGoodL M f (modelOf I f r)) := by
  have hB' : BaseOk (LinkSys.ofInput I B (worldF I f (StackBound.bud I f) r)) := baseOk_F hB
  have himgF : ∀ a, (LinkSys.ofInput I B (worldF I f (StackBound.bud I f) r)).Img a →
      worldF I f (StackBound.bud I f) r a := fun _ h => .inr h
  have hL := okB_soundT hbin.ok hB' himgF
  have hro : ∀ a b, roB a = some b → r.mem a = b := fun a b h =>
    hX a b (hbin.data a b h).1 (hbin.data a b h).2
  obtain ⟨hent, -, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ :=
    premisesT hL (Clif.Program.func?_some hf).1 hro ho hr
  obtain ⟨hA, hG⟩ := StackBound.crate_correct_stackNXT hbin.ok hn B _ hB' himgF f hf M _ _ _ args
    cs hent (by rw [spv_modelOf]; exact ho.stack) hgfree rfl himg hbe hargs hr.entry hsav hrel hpl
    htr
  refine ⟨?_, (binary_correctT hbin B hB hn hf M hX ho hr htr).2, fun hout => runGoodL_F (hG hout)⟩
  rw [mach_F I B (fun _ => False) (worldF I f (StackBound.bud I f) r)]
  exact hA

/-- **The model state differs from `r` only at the bytes `R`** (the binary facts, the loader
premise). -/
theorem BinFactsT.modelOf_neT {I : LinkInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFactsT I X R roB) {f : Clif.Function}
    {r : Arm.ArmState} (hX : X.Intact r) : ∀ a, (modelOf I f r).mem a ≠ r.mem a → R a := by
  intro a hne
  by_cases hi : img I a
  · rw [mem_modelOf_img hi] at hne
    rcases (hbin.code a hi).2 with h | h
    · exact absurd (hX a _ (hbin.code a hi).1 h).symm hne
    · exact h
  · exact absurd (mem_modelOf_not hi) hne

/-- **`binary_correctX` for any program, recursive ones included**: the stack premise is the
depth-`M` budget `frameDrop + (D * M + pbMax I)` (`LinkSys.budget_KT`: every frame of a call
level is at most `D`, and the deepest activation's stack probes write up to `pbMax I` bytes below
its frame, #581: the former `frameDrop + D * M` is too small for a program with probes)
instead of the stack bound `stackFn` of a non-recursive program, so no call-graph premise
(`goodN`) is left; with read-only data factsT `roB` (unlike `binary_correct_depth`). `M` is both
the CLIF run's fuel and the depth of the linked machine. -/
theorem binary_correct_depthXT {I : LinkInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFactsT I X R roB) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
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
  have hB' : BaseOk (LinkSys.ofInput I B (worldF I f (I.D * M + pbMax I) r)) := baseOk_F hB
  have himgF : ∀ a, (LinkSys.ofInput I B (worldF I f (I.D * M + pbMax I) r)).Img a →
      worldF I f (I.D * M + pbMax I) r a := fun _ h => .inr h
  have hL := okB_soundT hbin.ok hB' himgF
  have hro : ∀ a b, roB a = some b → r.mem a = b := fun a b h =>
    hX a b (hbin.data a b h).1 (hbin.data a b h).2
  obtain ⟨hent, hres, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ :=
    premisesT hL (Clif.Program.func?_some hf).1 hro ho hr
  obtain ⟨hA, hG⟩ := backend_correct_program_budgetXT _ hL (LinkSys.budget_KT _ hL)
    (Clif.Program.func?_some hf).1 M hent
    ⟨hres, (LinkSys.budget_KT _ hL).2 M f (Clif.Program.func?_some hf).1⟩ rfl hgfree himg hbe hargs
    hr.entry hsav hrel hpl htr
  refine ⟨?_, hbin.modelOf_neT hX, fun hout => runGoodL_F (hG hout)⟩
  rw [mach_F I B (fun _ => False) (worldF I f (I.D * M + pbMax I) r)]
  exact hA

/-- **`binary_correct_depthX` for the run's peak call depth** (L1d): the whole-program CLIF run
of at most `F + 1` steps reaches no state with more than `d` callers (`Clif.DepthLe`); the stack
premise is the depth-`d` budget `frameDrop + (D * d + pbMax I)` (#581: with the probes of the
deepest activation), independent of the fuel `F`, and the linked
machine has depth `d`. The run premise `TrapsExplicit` is under the environment whose program
callees run with fuel `F` and at most `d - 1` callers of their own (`Clif.linkEnvD`). -/
theorem binary_correct_peakXT {I : LinkInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFactsT I X R roB) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
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
  have hB' : BaseOk (LinkSys.ofInput I B (worldF I f (I.D * d + pbMax I) r)) := baseOk_F hB
  have himgF : ∀ a, (LinkSys.ofInput I B (worldF I f (I.D * d + pbMax I) r)).Img a →
      worldF I f (I.D * d + pbMax I) r a := fun _ h => .inr h
  have hL := okB_soundT hbin.ok hB' himgF
  have hro : ∀ a b, roB a = some b → r.mem a = b := fun a b h =>
    hX a b (hbin.data a b h).1 (hbin.data a b h).2
  obtain ⟨hent, hres, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ :=
    premisesT hL (Clif.Program.func?_some hf).1 hro ho hr
  obtain ⟨hA, hG⟩ := backend_correct_program_peakXT _ hL (LinkSys.budget_KT _ hL)
    (Clif.Program.func?_some hf).1 F d hent
    ⟨hres, (LinkSys.budget_KT _ hL).2 d f (Clif.Program.func?_some hf).1⟩ rfl hgfree himg hbe hargs
    hr.entry hsav hrel hpl
    hd htr
  refine ⟨?_, hbin.modelOf_neT hX, fun hout => runGoodL_F (hG hout)⟩
  rw [mach_F I B (fun _ => False) (worldF I f (I.D * d + pbMax I) r)]
  exact hA

/-- `binary_correct_of_checks` with `RunGoodL` of the model's run for a returning or trapping
outcome. -/
theorem binary_correct_of_checksXT {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hI : okBT I = true) (hbin : BinCheck.BinOk I D file) (B : BaseEnv) (hB : BaseOk (sys I B))
    {n : String} (hn : StackBound.goodN I n = true) {f : Clif.Function}
    (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (StackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) :
    ArmRefinesT (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (Clif.runLoop B.env (prog I) (M + 1) cs) ∧
    (∀ a, (modelOf I f r).mem a ≠ r.mem a → BinCheck.RelocAt I a) ∧
    ((∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c) →
      (sys I B).RunGoodL M f (modelOf I f r)) :=
  binary_correctXT (binFacts_of_checksT hI hbin) B hB hn hf M hX ho hr htr
end Binary
end E2E
