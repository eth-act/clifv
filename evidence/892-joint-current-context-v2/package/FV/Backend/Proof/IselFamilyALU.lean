import FV.Backend.Proof.IselFamily
import FV.Backend.Proof.IselRulesALU

/-!
# The two-register ALU root rules, proved with the template (`aluRR_ruleOk`)

Each rule: its three forward lemmas (`IselRulesALU`: match, right-hand side at every width,
right-hand side failing on an operand without a register) and one line here. All widths
i8..i64 at once (the rule chooses the 32- or 64-bit operation; `aluVal_holds` is the width
argument).
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000 in
theorem variantNames_Iadd : (variantNames 151)[73]? = some "Iadd" := rfl
set_option maxRecDepth 20000 in
theorem variantNames_Isub : (variantNames 151)[74]? = some "Isub" := rfl

/-- **`iadd_base_case`** (`lower.isle:86`, `(lower (iadd ty x y)) → (add ty x y)`), i8..i64. -/
theorem iadd_base_case_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_86 :=
  aluRR_ruleOk hp (cop := .iadd) (aop := .add) rfl hp.t2357 term_2357_kind variantNames_Iadd rfl
    rfl (.inl rfl)
    (fun ctx _ _ _ _ _ _ st tr m hi hty hw hd => match_86 hp ctx hi hty hw hd st tr m)
    (fun ctx _ _ _ _ _ _ st tr n hc hx hy hw => rhs_86 hp ctx hc hx hy hw st tr n)
    (fun ctx _ _ _ _ st tr n v s' hxy => rhs_86_none hp ctx hxy st tr n v s')
    F isem MR env cp hR hMR

/-- **`isub_base_case`** (`lower.isle:801`, `(lower (isub ty x y)) → (sub ty x y)`), i8..i64. -/
theorem isub_base_case_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_801 :=
  aluRR_ruleOk hp (cop := .isub) (aop := .sub) rfl hp.t2358 term_2358_kind variantNames_Isub rfl
    rfl (.inr (.inl rfl))
    (fun ctx _ _ _ _ _ _ st tr m hi hty hw hd => match_801 hp ctx hi hty hw hd st tr m)
    (fun ctx _ _ _ _ _ _ st tr n hc hx hy hw => rhs_801 hp ctx hc hx hy hw st tr n)
    (fun ctx _ _ _ _ st tr n v s' hxy => rhs_801_none hp ctx hxy st tr n v s')
    F isem MR env cp hR hMR

end Backend.Proof
