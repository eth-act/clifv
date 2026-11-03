import FV.Backend.Proof.IselExclSound

/-!
# The float memory roots under `CtxInv` (S11e4, floats #35)

`CtxInv` describes subset-E contexts, whose values are all integers. There the float memory
roots of the closure never match: the abstract checker of the excluded roots (`fails`, sound by
`fails_sound`) rejects each of them (the float `load`/`store` patterns test `ty_float_or_vec` on
an E type). So their `MemRuleOkR` (`load.f32` 1047, `load.f64` 1048, float `store` 1073/1074)
holds vacuously under `CtxInv`, which is how `MemRulesCorrectR` covers them (`MemRulesCorrectR`
has no `MemRefinesFP` for the FP accesses). Their contract over float-capable contexts (`CtxInvT`,
where they do match) is `MemRulesCorrectRT` (`IselFloatMem`). The non-memory float roots
(`f32const`/`f64const`/`bitcast`) are proven over `CtxInvT` (`LowerRuleOkT`) and enter
`LowerRulesCorrect` through `LowerRuleOkT.toOk`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-- A rule whose pattern the checker rejects matches no instruction of a `CtxInv` context. -/
theorem match_false_of_fails {r : Rule} {q : Pattern} (hr : r.args = [q])
    (hf : fails program .inst q = true) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    {ii : Nat} {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info)
    (hc : info.clif = some inst) {cfg : Config} {m : Nat} {s : LState × Array RuleId}
    {env' : Interp.Env V} {s1 : LState × Array RuleId}
    (hmatch : (matchRule program (sem ctx) cfg m r [.inst ii]).run s = .ok (some env', s1)) : False := by
  cases m with
  | zero => rw [matchRule.eq_1] at hmatch; cases hmatch
  | succ m =>
    obtain ⟨env0, ha, -⟩ := matchRule_some_inv hmatch
    rw [hr] at ha
    obtain ⟨e1, h1, -⟩ := matchArgs_cons_inv ha
    exact fails_sound hctx q .inst _ _ _ _ hf ⟨ii, info, inst, rfl, hi, hc, hctx.data ii info inst hi hc⟩ h1

theorem memRuleOkR_of_fails {Rd F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} {r : Rule} {q : Pattern}
    (hr : r.args = [q]) (hf : fails program .inst q = true) :
    MemRuleOkR Rd F sb syms isem MR env cp program r := by
  intro f ctx hctx _ ii info inst hi hic cfg _ m n st tr env' s1 out st' tr' _ _ _ _ hmatch _
  exact (match_false_of_fails hr hf hctx hi hic hmatch).elim

set_option maxRecDepth 100000

theorem fails_lower_2625 : fails program .inst (rule_lower_2625.args.head!) = true := by decide +kernel
theorem fails_lower_2628 : fails program .inst (rule_lower_2628.args.head!) = true := by decide +kernel
theorem fails_lower_2746 : fails program .inst (rule_lower_2746.args.head!) = true := by decide +kernel
theorem fails_lower_2750 : fails program .inst (rule_lower_2750.args.head!) = true := by decide +kernel

/-! ## The `CtxInv` obligations of the float memory roots (vacuous) -/

section
variable {Rd F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Sem}
  {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}

theorem load_f32_ok_vac : MemRuleOkR Rd F sb syms isem MR env cp program rule_lower_2625 :=
  memRuleOkR_of_fails rfl fails_lower_2625
theorem load_f64_ok_vac : MemRuleOkR Rd F sb syms isem MR env cp program rule_lower_2628 :=
  memRuleOkR_of_fails rfl fails_lower_2628
theorem store_f32_ok_vac : MemRuleOkR Rd F sb syms isem MR env cp program rule_lower_2746 :=
  memRuleOkR_of_fails rfl fails_lower_2746
theorem store_f64_ok_vac : MemRuleOkR Rd F sb syms isem MR env cp program rule_lower_2750 :=
  memRuleOkR_of_fails rfl fails_lower_2750
end

end Backend.Proof
