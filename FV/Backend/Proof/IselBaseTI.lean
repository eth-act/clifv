module

public import FV.Backend.Proof.IselFloatMem
public import FV.Backend.Proof.LowerContractT

@[expose] public section

/-!
# Integer rules over typed contexts: the common facts (S11e5 Stage C, slice 7)

The integer `lower` roots are proven over `CtxInv` (every value an integer in an X register).
Over a float-capable context (`CtxT`: `CtxInvT`, the typed scope, integer externs) only the
values in integer positions are (`IntPos`): the `intArgs` operands of the instruction (`intOps`)
and of the instructions the rules look through (`CtxInvT.intPos_of_def`). The `…TI` proofs are the
`CtxInv` ones with `CtxInv.valueReg`/`valTyE`/`typedReg` replaced by `CtxInvT.valueRegI`/
`valTyEI`/`typedRegI`, whose integer-position premise `int_posA` finds in the proof's context
(`int_posT`, or the value's type).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-- **Root rule correctness on the subset-E instructions of a typed context**. -/
abbrev LowerRuleOkTI := LowerRuleOkTX (fun i => Compile.instE i = true)

/-- A value with an E type is in an integer position. -/
theorem intPos_of_valueType {ctx : Ctx} {x : Nat} {t : CTy} (h : ctx.valueType? x = some t)
    (ht : t ∈ eCTys) : IntPos ctx x := fun t' h' => by
  rw [h] at h'
  cases h'
  exact ht

open Lean Elab Tactic in
/-- `int_posA` closes `IntPos ctx y` with `int_posT hctx` (`hctx : CtxInvT f ctx` in the
context), with `hops : ∀ x ∈ intArgs inst, IntPos ctx x` (the root instruction's operands), or
from a hypothesis `ctx.valueType? y = some t` with `t` an E type. -/
elab "int_posA" : tactic => do
  let h := mkIdent `hctx
  let hops := mkIdent `hops
  evalTactic (← `(tactic| first
    | int_posT $h
    | (exact $hops _ (by simp [Backend.Proof.intArgs]))
    | (exact Backend.Proof.intPos_of_valueType (by assumption) (by simp [Backend.Proof.eCTys]))))

/-- `CtxInv.valueReg` at an integer position. -/
theorem CtxInvT.valueRegI {f : Clif.Function} {ctx : Ctx} (h : CtxInvT f ctx) (x : Nat) (r : Reg)
    (hr : ctx.valueReg? x = some r) (hx : IntPos ctx x := by int_posA) : r = .vreg x .int :=
  h.valueReg_int hr hx

/-- `CtxInv.valTyE` at an integer position. -/
theorem CtxInvT.valTyEI {f : Clif.Function} {ctx : Ctx} (_h : CtxInvT f ctx) (x : Nat) (t : CTy)
    (ht : ctx.valueType? x = some t) (hx : IntPos ctx x := by int_posA) : t ∈ eCTys :=
  hx t ht

/-- `CtxInv.typedReg` at an integer position. -/
theorem CtxInvT.typedRegI {f : Clif.Function} {ctx : Ctx} (h : CtxInvT f ctx) (x : Nat) (t : CTy)
    (ht : ctx.valueType? x = some t) (hx : IntPos ctx x := by int_posA) :
    ctx.valueReg? x = some (.vreg x .int) := by
  rw [h.typedReg x t ht, valClass_of_eCTys (hx t ht)]

end Backend.Proof
