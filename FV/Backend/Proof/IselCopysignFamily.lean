import FV.Backend.Proof.IselContract

/-!
# #35: the `fcopysign` root family

The scalar `fcopysign` root of `lower` (`rule_lower_685`, id 712: `lower (fcopysign ty x y)` →
`fcopy_sign`, whose scalar rule `inst.isle:4612` emits `ushr` + `sli`) is a closure root of its
own: `copysignRootRule`, and its family over float-capable contexts `LowerRulesCorrectCS`
(proven in `IselFloatCopysign.lean`, `lowerRulesCorrectCS_program`). The other float families
(`floatArithRootRule`, `LowerRulesCorrectFT`, …) are unchanged.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-- The `fcopysign` root rule of `lower` (#35): `rule_lower_685` (id 712). -/
def copysignRootRule (r : Rule) : Bool := r.id == 712

/-- **#35's target (`fcopysign`)**: over float-capable contexts (`CtxInvT`), the `fcopysign`
root is correct. -/
def LowerRulesCorrectCS (p : Program) : Prop :=
  ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program),
    Refines F isem → MRStable F MR →
    ∀ r ∈ p.rulesOf TId.lower, copysignRootRule r = true → LowerRuleOkT isem MR env cp p r

end Backend.Proof
