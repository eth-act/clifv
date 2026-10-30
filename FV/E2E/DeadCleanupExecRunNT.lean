import FV.E2E.DeadCleanupExecRunN
import FV.E2E.DeadCleanupBinaryT
import FV.E2E.DeadCleanupBinCheckT
import FV.E2E.DeadCleanupExecBytesT
import FV.E2E.DeadCleanupExecStaticT
import FV.E2E.DeadCleanupLinkCheckT
import FV.E2E.DeadCleanupStackBoundT
import FV.E2E.ExecBytesT
import FV.E2E.LinkArmT
import FV.E2E.LinkCheckT
import FV.E2E.PipelineCheckT
import FV.E2E.StackBoundT

/-! # Typed copies of `FV.E2E.DeadCleanupExecRunN` (S11e5 Stage C, slice 8)

The declarations of `FV.E2E.DeadCleanupExecRunN` that depend on the integer link contract
(`LinkSys.Ok`, `LinkSys.Thm`, `okB`, `ArmRefines`), for the typed contract `LinkSys.OkT`
(suffix `T`; `LinkSys.Ok.*` as `LinkSys.OkT.*`). -/

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false
open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck
section Defs
variable (I : LinkInput) (B : BaseEnv) (file : ByteArray)
end Defs
section Lemmas
variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

theorem runOkSN_of_nT (hI : okBCleanupT I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hH : HooksSim I B) {M : Nat}
    {f : Clif.Function} (hf : f ∈ (prog I).funcs) {c : Arm.ArmState}
    (h : RunOkN I B file M f c) : RunOkSN I B file M f c :=
  fun M' g t hR he => stepOk_of_dT hI hc hF hH (reachN_mem hR hf) (h M' g t hR he)
end Lemmas
section Core
variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}
end Core
section Transfer
variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- **The model's outcome transfers to the executable machine** (`exec_of_model`) under
`RunOkSN`. -/
theorem exec_of_modelNT (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {M : Nat} {f : Clif.Function}
    (hf : f ∈ (prog I).funcs) {r : Arm.ArmState} (hpc : Arm.r .PC r = (art I f).base)
    (hra : ∀ k < (art I f).fb.words.size, xreg 30 r ≠ (art I f).base + BitVec.ofNat 64 (4 * k))
    (hd : ∀ a, (modelOf I f r).mem a ≠ r.mem a → E2E.DeadCleanupBinCheck.RelocAt I a)
    (hrun : RunOkSN I B file M f (modelOf I f r)) {o : Clif.Outcome}
    (h : ArmRefinesT (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r) o) :
    ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (E2E.DeadCleanupBinCheck.RelocAt I) o := by
  have hFf := hF f hf
  have hsim := sim_modelOf hd
  have hra' : ∀ k < (art I f).fb.words.size,
      xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
    simp only [xreg, r_modelOf]; exact hra
  have hpc' : Arm.r .PC (modelOf I f r) = (art I f).base := by rw [r_modelOf]; exact hpc
  have hsimN := act_simN (B := B) hF M f _ r hf hpc' hsim hrun
  cases o with
  | returned vals cm =>
    obtain ⟨n, hret, hx, hmem⟩ := h
    obtain ⟨k', hk'⟩ := hsimN n (no_return hFf hra' hret.err) (fun hs => by
      obtain ⟨k, hk, he⟩ := second_code hFf hs
      exact hra k hk (by rw [← he, hret.pc])) hret.err
    refine ⟨k', ⟨?_, ?_, ?_, fun n hn => ?_, fun n h8 h16 => ?_⟩, fun j v q hv hq => ?_,
      fun a b hv hb hR => ?_⟩
    · rw [hk'.1, hret.pc]
    · rw [hk'.1, hret.err]
    · simp only [spv]; rw [hk'.1]; exact (hret.sp.trans (spv_modelOf I f r))
    · simp only [xreg]; rw [hk'.1]; exact (hret.savedX n hn).trans (r_modelOf I f r _)
    · rw [hk'.1, hret.savedV n h8 h16, r_modelOf]
    · have hxq := hx j v q hv hq
      cases q <;> simp only [regVal] at hxq ⊢ <;> (try rw [hk'.1]) <;> exact hxq
    · show Arm.read_store _ _ = b
      rw [show Arm.read_store (BitVec.ofNat 64 a) (runX (step I B file) k' r).mem =
        (runX (step I B file) k' r).mem (BitVec.ofNat 64 a) from rfl, hk'.2 _ hR]
      exact hmem a b hv hb
  | trapped c0 =>
    obtain ⟨n, htrap⟩ := h
    have hguard := no_return (B := B) hFf hra' htrap.err
    by_cases hs : Second I f (Arm.r .PC (runX ((sys I B).mach M f) n (modelOf I f r)))
    · -- a trap at a second word: one executable step after the first word
      obtain ⟨rl, hrl, ht, he⟩ := hs
      cases n with
      | zero => exact (not_second_base hFf ⟨rl, hrl, ht, hpc'.symm.trans he⟩).elim
      | succ n1 =>
      have hok1 := hrun _ _ _ (ReachN.act (k := n1) fun j hj => hguard j (by omega))
        (by rw [← runX_succ' ((sys I B).mach M f)]; exact htrap.err)
      have hpc1 := hok1.cf rl hrl ht (by rw [← runX_succ' ((sys I B).mach M f) n1]; exact he)
      obtain ⟨k', hk'⟩ := hsimN n1 (fun j hj => hguard j (by omega))
        (by rw [hpc1]; exact first_not_second hFf hrl ht) hok1.err
      obtain ⟨hpcE, herrE⟩ := pair_first_pc hFf hrl ht hpc1 hok1 hk'
      refine ⟨k' + 1, ?_⟩
      rw [runX_succ'] at htrap ⊢
      exact ⟨by rw [← herrE]; exact htrap.err, by rw [← hpcE]; exact htrap.site⟩
    · obtain ⟨k', hk'⟩ := hsimN n hguard hs htrap.err
      exact ⟨k', by rw [hk'.1]; exact htrap.err, by rw [hk'.1]; exact htrap.site⟩
  | stuck _ => trivial
  | outOfFuel => trivial
end Transfer

/-- **`binary_correct_exec_static` under the error-guarded hypothesis `RunOkN`**: under the
premisesT of `binary_correct_of_checks_acyclic`, the outside-code contract `HooksSim`, the code
map check `codeMapB` and `StepOkD` at the states of the model's run whose step ends without error
(nested only into calls that return), the executable machine run from `r` refines the
whole-program CLIF run. -/
theorem binary_correct_exec_staticNT {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hI : okBCleanupT I = true) (hcm : codeMapB I (tabOf I.resultsCleanup) = true)
    (hbin : DeadCleanupBinCheck.BinOk I D file) (B : BaseEnv) (hB : BaseOk (sys I B)) (hH : HooksSim I B)
    {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls I I.resultsCleanup) f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hrun : RunOkN I B file M f (modelOf I f r)) :
    ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (E2E.DeadCleanupBinCheck.RelocAt I)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hn := (DeadCleanupStackBound.goodN_iffT hI).2 ⟨f, hf, hc⟩
  obtain ⟨h1, h2⟩ := binary_correct_of_checksT hI hbin B hB hn hf M hX ho hr htr
  have hfm := (Clif.Program.func?_some hf).1
  have hB' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)) := baseOk_F hB
  have hL := okBCleanup_soundT hI hB' fun _ h => .inr h
  have hfacts := binFacts_of_checksT hI hbin
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := premisesT hL hfm hro ho hr
  have hL' := okBCleanup_soundT hI (baseOk_F (F' := img I) hB) fun _ h => h
  have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOkT hI hbin hL' hg
  exact exec_of_modelNT hF hfm (by rw [← r_modelOf I f r]; exact hent.pc) hent.raOutside h2
    (runOkSN_of_nT hI hcm hF hH hfm hrun) h1
end E2E.DeadCleanupExecBytes
