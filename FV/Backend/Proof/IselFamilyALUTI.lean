module

public import FV.Backend.Proof.IselFamilyALU
public import FV.Backend.Proof.IselBaseTI
public import FV.Backend.Proof.IselFamilyTI

@[expose] public section

/-!
# `IselFamilyALU` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselFamilyALU`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Isle Isle.Interp Isle.Aarch64
/-- **`iadd_base_case`** (`lower.isle:86`, `(lower (iadd ty x y)) → (add ty x y)`), i8..i64. -/
theorem iadd_base_case_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_86 :=
  aluRR_ruleOkTI hp (cop := .iadd) (aop := .add) rfl hp.t2357 term_2357_kind variantNames_Iadd rfl
    rfl (.inl rfl)
    (fun ctx _ _ _ _ _ _ st tr m hi hty hw hd => match_86 hp ctx hi hty hw hd st tr m)
    (fun ctx _ _ _ _ _ _ st tr n hc hx hy hw => rhs_86 hp ctx hc hx hy hw st tr n)
    (fun ctx _ _ _ _ st tr n v s' hxy => rhs_86_none hp ctx hxy st tr n v s')
    F isem MR env cp hR hMR

/-- **`isub_base_case`** (`lower.isle:801`, `(lower (isub ty x y)) → (sub ty x y)`), i8..i64. -/
theorem isub_base_case_okTI {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOkTI isem MR env cp p rule_lower_801 :=
  aluRR_ruleOkTI hp (cop := .isub) (aop := .sub) rfl hp.t2358 term_2358_kind variantNames_Isub rfl
    rfl (.inr (.inl rfl))
    (fun ctx _ _ _ _ _ _ st tr m hi hty hw hd => match_801 hp ctx hi hty hw hd st tr m)
    (fun ctx _ _ _ _ _ _ st tr n hc hx hy hw => rhs_801 hp ctx hc hx hy hw st tr n)
    (fun ctx _ _ _ _ st tr n v s' hxy => rhs_801_none hp ctx hxy st tr n v s')
    F isem MR env cp hR hMR

end Backend.Proof
