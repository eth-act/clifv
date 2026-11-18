import FV.Backend.Proof.IselContract

/-!
# #35: the `fma` root family

The scalar `fma` roots of `lower` (`lower.isle:608`, `rule_lower_608`, id 693:
`lower (fma ty x y z)` → `fmadd`; `lower.isle:609`, `rule_lower_609`, id 694:
`lower (fma (ty_scalar_float ty) x y (fneg _ z))` → `fnmsub`; the helpers' scalar rules emit
`fpu_rrrr` with `MAdd`/`MSub`/`NMSub`/`NMAdd`) are closure roots of their own: `fmaRootRule`,
and their family over float-capable contexts `LowerRulesCorrectFM` (proven in
`IselFloatFma.lean`, `lowerRulesCorrectFM_program`). The other float families are unchanged.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-- The `fma` root rules of `lower` (#35): `rule_lower_608` (id 693) and `rule_lower_609`
(id 694). -/
def fmaRootRule (r : Rule) : Bool := r.id == 693 || r.id == 694

/-- **#35's target (`fma`)**: over float-capable contexts (`CtxInvT`), the `fma` roots are
correct. -/
def LowerRulesCorrectFM (p : Program) : Prop :=
  ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program),
    Refines F isem → MRStable F MR →
    ∀ r ∈ p.rulesOf TId.lower, fmaRootRule r = true → LowerRuleOkT isem MR env cp p r

end Backend.Proof
