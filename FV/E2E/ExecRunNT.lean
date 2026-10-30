import FV.E2E.ExecRunN
import FV.E2E.ExecBytesT
import FV.E2E.ExecStaticT
import FV.E2E.LinkArmT
import FV.E2E.LinkCheckT

/-! # Typed copies of `FV.E2E.ExecRunN` (S11e5 Stage C, slice 8)

The declarations of `FV.E2E.ExecRunN` that depend on the integer link contract
(`LinkSys.Ok`, `LinkSys.Thm`, `okB`, `ArmRefines`), for the typed contract `LinkSys.OkT`
(suffix `T`; `LinkSys.Ok.*` as `LinkSys.OkT.*`). -/

namespace E2E.ExecBytes
open Backend Backend.Proof E2E.LinkCheck E2E.Binary E2E.BinCheck
section Defs
variable (I : LinkInput) (B : BaseEnv) (file : ByteArray)
end Defs
section Lemmas
variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

theorem runOkSN_of_nT (hI : okBT I = true) (hc : codeMapB I (tabOf I.results) = true)
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
    (hd : ∀ a, (modelOf I f r).mem a ≠ r.mem a → RelocAt I a)
    (hrun : RunOkSN I B file M f (modelOf I f r)) {o : Clif.Outcome}
    (h : ArmRefinesT (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r) o) :
    ExecRefinesT (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAt I) o := by
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
end E2E.ExecBytes
