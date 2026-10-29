module

public import FV.E2E.RegLevelOp
public import FV.E2E.RegLevelNoCall

@[expose] public section

/-!
# `GoodXN` at one line (SEM1 #537, step 2k)

`RL.goodX_ofIns`/`RL.goodX_line` with `RL.GoodXN` (docs/plans/uninit.md §5.5): at an unhooked line
(`RL.goodXN_ofIns`) or a line that is no `bl`/`blr` (`RL.goodXN_line`) the state is no call state.
-/

namespace Backend.Proof

open Backend E2E

/-- `RL.goodX_ofIns` with `GoodXN` (the line is unhooked, so no call line). -/
theorem RL.goodXN_ofIns {R : RL} (hR : R.Wf) {u : Arm.ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    (hx : x.hooked = false) (htl : x.tlsTail = false) (hgood : R.Good u)
    (herr : Arm.r .ERR u = .None) (hprog : u.program = R.fb.program R.base)
    (hnext : R.NextOk u (R.step u)) (hrd : R.ReadsAt u) : R.GoodXN u :=
  ⟨RL.goodX_ofIns hR hj hpc hx htl hgood herr hprog hnext hrd, RL.noCallAt_of_line hR hj hpc hx⟩

/-- `RL.goodX_line` with `GoodXN` at a line that is no `bl`/`blr`. -/
theorem RL.goodXN_line {R : RL} (hR : R.Wf) {u : Arm.ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    (hnc : (∀ n, x ≠ .bl n) ∧ ∀ r, x ≠ .blr r)
    (hx : x.tlsTail = false) (hgood : R.Good u) (herr : Arm.r .ERR u = .None)
    (hprog : u.program = R.fb.program R.base) (hnext : R.NextOk u (R.step u))
    (hgot : ∀ rd rn n, x = .ldrGotLo12 rd rn n → ∀ a, R.G a → u.mem a = R.s0.mem a)
    (hblr : ∀ r, x = .blr r → (R.vc.DestsInt → r ≠ .xzr) ∧ ∀ k w, R.fb.words[k]? = some w →
      Arm.read_mem_bytes 4 (R.base + BitVec.ofNat 64 (4 * k)) u = w)
    (hcall : ((∃ n, x = .bl n) ∨ ∃ r, x = .blr r) → R.CallPre u) (hrd : R.ReadsAt u) :
    R.GoodXN u :=
  ⟨RL.goodX_line hR hj hpc hx hgood herr hprog hnext hgot hblr hcall hrd,
    RL.noCallAt_of_noCall hR hj hpc hnc⟩

end Backend.Proof
