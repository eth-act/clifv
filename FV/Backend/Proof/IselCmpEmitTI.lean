import FV.Backend.Proof.IselCmpEmit

/-!
# `IselCmpEmit` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselCmpEmit`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
section Ext
variable (ctx : Ctx) (st : LState)
end Ext
theorem iconst_data_invTI {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {y j : Nat}
    {info : IInfo} {w : V} (hj : ctx.defInst? y = some j) (hi : ctx.insts[j]? = some info)
    (hd : V.data 152 35 [V.data 151 57 [], w] = info.data) :
    ∃ ty imm, w = .int (imm64OfIconst ty imm) ∧ eTy ty = true ∧ info.clif = some (.iconst ty imm) :=
  iconst_data_invT hctx hj hi hd

section Rules
variable {F : BitVec 64 → Prop} {isem : Sem} {f : Clif.Function} {ctx : Ctx}
end Rules
section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
end
end Backend.Proof
