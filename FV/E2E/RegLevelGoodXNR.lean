import FV.E2E.RegLevelGoodXN
import FV.E2E.RegLevelReadsIn

/-!
# `GoodXNR` at one line (SEM1 #537, step 3p)

`RL.goodXN_ofIns`/`RL.goodXN_line` with the located reads `RL.ReadsIn` (`RL.GoodXNR`): the D2
premise is `ReadsIn`, which gives D2 (`RL.ReadsIn.readsAt`).
-/

namespace Backend.Proof

open Backend E2E

/-- `RL.goodXN_ofIns` with `GoodXNR`. -/
theorem RL.goodXNR_ofIns {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {u : Arm.ArmState} {j : Nat}
    {x : Insn} {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    (hx : x.hooked = false) (htl : x.tlsTail = false) (hgood : R.Good u)
    (herr : Arm.r .ERR u = .None) (hprog : u.program = R.fb.program R.base)
    (hnext : R.NextOk u (R.step u)) (hrd : R.ReadsInY Y u) : R.GoodXNY Y u :=
  ⟨RL.goodXN_ofIns hR hj hpc hx htl hgood herr hprog hnext (hrd.readsAt hR), hrd⟩

/-- `RL.goodXN_line` with `GoodXNR`. -/
theorem RL.goodXNR_line {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {u : Arm.ArmState} {j : Nat}
    {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    (hnc : (∀ n, x ≠ .bl n) ∧ ∀ r, x ≠ .blr r)
    (hx : x.tlsTail = false) (hgood : R.Good u) (herr : Arm.r .ERR u = .None)
    (hprog : u.program = R.fb.program R.base) (hnext : R.NextOk u (R.step u))
    (hgot : ∀ rd rn n, x = .ldrGotLo12 rd rn n → ∀ a, R.G a → u.mem a = R.s0.mem a)
    (hblr : ∀ r, x = .blr r → (R.vc.DestsInt → r ≠ .xzr) ∧ ∀ k w, R.fb.words[k]? = some w →
      Arm.read_mem_bytes 4 (R.base + BitVec.ofNat 64 (4 * k)) u = w)
    (hcall : ((∃ n, x = .bl n) ∨ ∃ r, x = .blr r) → R.CallPre u) (hrd : R.ReadsInY Y u) :
    R.GoodXNY Y u :=
  ⟨RL.goodXN_line hR hj hpc hnc hx hgood herr hprog hnext hgot hblr hcall (hrd.readsAt hR), hrd⟩

/-- `ReadsIn` at a `GoodX` state whose line is hooked or holds no load. -/
theorem RL.goodXNR_of_goodXN {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {u : Arm.ArmState}
    (hg : R.GoodXN u) (h : ∀ x, R.AtLine u x → x.loads = false) : R.GoodXNY Y u :=
  ⟨hg, RL.readsIn_of_goodX hR hg.1 h⟩

end Backend.Proof
