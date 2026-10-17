import FV.Backend.Proof.IselExcl

/-!
# The float data-movement roots under `CtxInv` (S11e4, floats #35)

`CtxInv` describes subset-E contexts, whose values are all integers. There the float roots of
the closure never match: the abstract checker of the excluded roots (`fails`, sound by
`fails_sound`) rejects each of them (`F32const`/`F64const`/`Bitcast` are not E opcodes; the
float `load`/`store` patterns test `ty_float_or_vec` on an E type). So their `LowerRuleOk`
(`f32const` 584, `f64const` 585, `bitcast` 1080/1083/1084/1085) and `MemRuleOkR` (`load.f32`
1047, `load.f64` 1048, float `store` 1073/1074) hold vacuously under `CtxInv`, which is how
`LowerRulesCorrect`/`MemRulesCorrectR` cover them. Their contracts over float-capable contexts
(`CtxInvT`, where they do match) are `LowerRulesCorrectT`/`MemRulesCorrectRT`.
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

theorem lowerRuleOk_of_fails {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {r : Rule} {q : Pattern} (hr : r.args = [q]) (hf : fails program .inst q = true) :
    LowerRuleOk isem MR env cp program r := by
  intro f ctx hctx ii info inst hi hic cfg _ m n st tr env' s1 out st' tr' _ _ _ _ hmatch _
  exact (match_false_of_fails hr hf hctx hi hic hmatch).elim

theorem memRuleOkR_of_fails {Rd F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} {r : Rule} {q : Pattern}
    (hr : r.args = [q]) (hf : fails program .inst q = true) :
    MemRuleOkR Rd F sb syms isem MR env cp program r := by
  intro f ctx hctx _ ii info inst hi hic cfg _ m n st tr env' s1 out st' tr' _ _ _ _ hmatch _
  exact (match_false_of_fails hr hf hctx hi hic hmatch).elim

set_option maxRecDepth 100000

theorem fails_lower_63 : fails program .inst (rule_lower_63.args.head!) = true := by decide +kernel
theorem fails_lower_68 : fails program .inst (rule_lower_68.args.head!) = true := by decide +kernel
theorem fails_lower_2625 : fails program .inst (rule_lower_2625.args.head!) = true := by decide +kernel
theorem fails_lower_2628 : fails program .inst (rule_lower_2628.args.head!) = true := by decide +kernel
theorem fails_lower_2746 : fails program .inst (rule_lower_2746.args.head!) = true := by decide +kernel
theorem fails_lower_2750 : fails program .inst (rule_lower_2750.args.head!) = true := by decide +kernel
theorem fails_lower_2779 : fails program .inst (rule_lower_2779.args.head!) = true := by decide +kernel
theorem fails_lower_2793 : fails program .inst (rule_lower_2793.args.head!) = true := by decide +kernel
theorem fails_lower_2798 : fails program .inst (rule_lower_2798.args.head!) = true := by decide +kernel
theorem fails_lower_2803 : fails program .inst (rule_lower_2803.args.head!) = true := by decide +kernel

/-! ## The `CtxInv` obligations of the float roots (vacuous) -/

theorem f32const_ok_vac {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} :
    LowerRuleOk isem MR env cp program rule_lower_63 := lowerRuleOk_of_fails rfl fails_lower_63
theorem f64const_ok_vac {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} :
    LowerRuleOk isem MR env cp program rule_lower_68 := lowerRuleOk_of_fails rfl fails_lower_68
theorem bitcast_fp_fp_ok_vac {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} :
    LowerRuleOk isem MR env cp program rule_lower_2779 := lowerRuleOk_of_fails rfl fails_lower_2779
theorem bitcast_gpr_fp_ok_vac {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} :
    LowerRuleOk isem MR env cp program rule_lower_2793 := lowerRuleOk_of_fails rfl fails_lower_2793
theorem bitcast_fp_gpr_ok_vac {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} :
    LowerRuleOk isem MR env cp program rule_lower_2798 := lowerRuleOk_of_fails rfl fails_lower_2798
theorem bitcast_gpr_gpr_ok_vac {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} :
    LowerRuleOk isem MR env cp program rule_lower_2803 := lowerRuleOk_of_fails rfl fails_lower_2803

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
