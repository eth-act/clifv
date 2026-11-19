import FV.Backend.Proof.IselContract

/-!
# #35: the `fma` root family

The scalar `fma` roots of `lower` (`lower.isle:608`, `rule_lower_608`, id 693:
`lower (fma ty x y z)` → `fmadd`; `lower.isle:609`, `rule_lower_609`, id 694:
`lower (fma (ty_scalar_float ty) x y (fneg _ z))` → `fnmsub`; the helpers' scalar rules emit
`fpu_rrrr` with `MAdd`/`MSub`/`NMSub`/`NMAdd`) are closure roots of their own: `fmaRootRule`,
and their family over float-capable contexts `LowerRulesCorrectFM` (proven in
`IselFloatFma.lean`, `lowerRulesCorrectFM_program`). The other float families are unchanged.

The helpers' rule 3 (`fneg` on the second operand) is not exact on NaN signs
(`Compile.fmaNegYFree`), so the family is stated over contexts without such an `fma`
(`FmaNegYFree`, from `Compile.fmaNegYFree` by `fmaNegYFree_of_buildCtx`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-- The `fma` root rules of `lower` (#35): `rule_lower_608` (id 693) and `rule_lower_609`
(id 694). -/
def fmaRootRule (r : Rule) : Bool := r.id == 693 || r.id == 694

/-- **No `fma` of the context has an `fneg`-defined second operand** (`Compile.fmaNegYFree`;
`fmadd`/`fnmsub`'s rule 3 would fold it with the wrong NaN sign). -/
def FmaNegYFree (ctx : Ctx) : Prop :=
  ∀ (ii : Nat) (info : IInfo) (ty : Clif.Ty) (x y z : Nat), ctx.insts[ii]? = some info →
    info.clif = some (.float .fma ty [x, y, z]) →
    ∀ (ty' : Clif.Ty) (w : Nat), ctx.defClif? y ≠ some (.float .fneg ty' [w])

/-- `LowerRuleOkT` over the contexts satisfying `Q` as well (the premise `Q ctx` right after
`CtxInvT f ctx`). -/
def LowerRuleOkTC (Q : Ctx → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInvT f ctx → Q ctx →
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst),
  ctx.insts[ii]? = some info → info.clif = some inst →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ii]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx inst info.results st rss st' ms

/-- A subset-E context has no `fma` (`Compile.instE`), so it satisfies `FmaNegYFree`. -/
theorem CtxInv.fmaNegYFree {f : Clif.Function} {ctx : Ctx} (h : CtxInv f ctx) : FmaNegYFree ctx := by
  intro ii info ty x y z hi hc
  have := h.instE ii info _ hi hc
  simp [Compile.instE] at this

/-- On subset-E contexts `LowerRuleOkTC FmaNegYFree` is `LowerRuleOk`. -/
theorem LowerRuleOkTC.toOk {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {p : Program} {r : Rule} (h : LowerRuleOkTC FmaNegYFree isem MR env cp p r) :
    LowerRuleOk isem MR env cp p r := by
  intro f ctx hctx ii info inst hi hic
  exact h f ctx hctx.toT hctx.fmaNegYFree ii info inst hi hic

/-- **#35's target (`fma`)**: over float-capable contexts (`CtxInvT`) without an `fma` whose
second operand is an `fneg` (`FmaNegYFree`), the `fma` roots are correct. -/
def LowerRulesCorrectFM (p : Program) : Prop :=
  ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program),
    Refines F isem → MRStable F MR →
    ∀ r ∈ p.rulesOf TId.lower, fmaRootRule r = true → LowerRuleOkTC FmaNegYFree isem MR env cp p r

end Backend.Proof
