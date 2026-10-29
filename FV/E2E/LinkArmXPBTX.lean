module

public import FV.E2E.LinkArmXPBT
public import FV.E2E.ExtSemGuardRX

@[expose] public section

/-!
# The induction step's call semantics with program-keeping guards (SEM1 #537, #680 (3), #690)

`XPBTGX`: `XPBTG` with the guard `CallPostNX` (#690), the `XI` for
`backend_correct_world_*PRGX`; `XPBTGX_ext` (`ext` of each guarded call, from `XPRBT_ext`),
`XPBTGX_eq_of` (stage 2 interface: where every non-vacuous contract of call `n` accepts
`XPRBT`'s result, every answer is `XPRBT`'s).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **`XPBTI` guarded by `CallPostNX`.** -/
noncomputable def XPBTGX (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
    (env : Clif.Env) (cs : Clif.State) (c : BitVec 64) : ExtSemI :=
  (L.XPBTI κ M g F P R).guardRI (CallPostNX env L.P.bare cs (g.externs.map (·.2)) (indSigs g)
    (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
    L.Xb.sym)

/-- **`ext` of the guarded calls.** -/
theorem XPBTGX_ext (hL : L.Ok) {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {env : Clif.Env} {cs : Clif.State}
    {c : BitVec 64} (n : Nat) :
    ∀ d uses w outs w', ((L.XPBTGX κ M g F P R env cs c).at n).call d uses w = some (outs, w') →
      Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program :=
  guardRXI_ext (L.XPBTI κ M g F P R) n fun _ _ _ _ _ hx herr => L.XPRBT_ext hL hx herr

/-- **Stage 2 interface** (`ExtSem.guardR_eq_of` on `CallPostNX`). -/
theorem XPBTGX_eq_of {M : Nat} {g : Clif.Function}
    {F : BitVec 64 → Prop} {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState}
    {env : Clif.Env} {cs : Clif.State} {c : BitVec 64} {n : Nat} {d : Option String}
    {uses : List CV} {w : Arm.ArmState}
    (h : (¬ ∀ r, CallPostNX env L.P.bare cs (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
      L.Xb.sym n d uses w r) →
      ∃ x, (L.XPRBT κ M g F P R n).call d uses w = some x ∧
        CallPostNX env L.P.bare cs (g.externs.map (·.2)) (indSigs g)
          (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
          L.Xb.sym n d uses w x)
    {r : List CV × Arm.ArmState}
    (hr : ((L.XPBTGX κ M g F P R env cs c).at n).call d uses w = some r) :
    (L.XPRBT κ M g F P R n).call d uses w = some r :=
  ExtSem.guardR_eq_of (X := (L.XPBTI κ M g F P R).at n) h hr

end LinkSys

end E2E
