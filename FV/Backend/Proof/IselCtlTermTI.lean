import FV.Backend.Proof.IselCtlRuleIds
import FV.Backend.Proof.IselTermFactsTy
import FV.Backend.Proof.PairsC
import FV.Backend.Proof.LowerContractT

/-!
# Family Ctl over typed contexts: the `lower` rules on terminators (S11e5 Stage C, slice 5)

`LowerTermRuleOkT` for `rule_lower_2237` (`trap` → `udf`, rule id 964: `trap_ruleOkT`, the
integer proof) and `rule_lower_2574` (`return`, rule id 1037: `ret_ruleOkT`). Over a typed
context (`CtxT`) `lower_return` puts value `x` in its vreg of class `valClassOf ctx x`
(`CtxInvT.valueReg`: `mapM_valueRegT`) and pins it to the next return register of that class
(`retRegsC` by class, `retRegsC_eq`: `retRegsT`); the `rets` has class-general pairs
(`argPairsC`, `operands_retsC`). Assembly: `lowerTermRulesCorrectT_program`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- The value registers of a float-capable context: value `x` in vreg `x` of its class
(`CtxInvT.valueReg`). -/
theorem mapM_valueRegT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) :
    ∀ {xs : List Nat} {rs : List Reg}, xs.mapM ctx.valueReg? = some rs →
      rs = xs.map fun x => Reg.vreg x (valClassOf ctx x)
  | [], rs, h => by simp at h; simp [h]
  | x :: xs, rs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨r, hr, rs', hrs, rfl⟩ := h
    rw [hctx.valueReg x r hr, mapM_valueRegT hctx hrs]
    rfl

theorem filter_isUse_retOpsC (ns : List (Nat × RegClass × Reg)) :
    (retOpsC ns).filter Operand.isUse = retOpsC ns := by
  rw [List.filter_eq_self]
  intro o ho
  simp only [retOpsC, List.mem_map] at ho
  obtain ⟨q, -, rfl⟩ := ho
  rfl

theorem vuses_retOpsC {V : Type} (ns : List (Nat × RegClass × Reg)) (ρ : Nat → V) :
    vuses (retOpsC ns).toArray ρ = ns.map (ρ ·.1) := by
  simp only [vuses, List.toList_toArray, filter_isUse_retOpsC]
  simp [retOpsC]

theorem vuseNums_retsC (ns : List (Nat × RegClass × Reg)) :
    vuseNums (.rets (argPairsC ns)) = ns.map (·.1) := by
  simp only [vuseNums, operands_retsC, List.toList_toArray, filter_isUse_retOpsC]
  simp [retOpsC]

theorem vdefs_retsC (ns : List (Nat × RegClass × Reg)) : vdefs (.rets (argPairsC ns)) = [] := by
  simp only [vdefs, operands_retsC, List.toList_toArray, filter_isDef_retOpsC, List.map_nil]

set_option maxHeartbeats 800000 in
/-- **`trap`** (`rule_lower_2237`) over typed contexts: `udf`. -/
theorem trap_ruleOkT {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem}
    {MR : MemRelT} (hR : Refines F isem) : LowerTermRuleOkT isem MR p rule_lower_2237 := by
  intro f ctx _ ti t data hrt hd hi cfg hc m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kU := fun n (hn : 30 ≤ n) s c v s' h => udf_ok hp (ctx := ctx) hc (n := n) (s := s) (c := c)
    (v := v) (s' := s') hn h
  have kS := fun n (hn : 60 ≤ n) i s v s' h => side_effect_inst_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  cases t with
  | ret xs =>
    rw [termData_ret] at hd; cases hd
    cases hp
    isel_inv [*, rule_lower_2237] at hmatch
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    simp at *
  | trap c =>
    rw [termData_trap] at hd; cases hd
    cases hp
    isel_inv [*, rule_lower_2237] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    repeat (isel_inv_simp [] at * <;> isel_destruct <;> subst_vars)
    have h528 := ‹ApplyInternal _ _ _ _ 46 528 _ _ _ _›
    obtain ⟨hs1, rfl⟩ := kU _ (by omega) _ _ _ _ h528
    have h243 := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
    obtain ⟨mi, hmi, hs2, rfl⟩ := kS _ (by omega) _ _ _ _ h243
    rw [ofV_udf] at hmi
    cases hmi
    simp only at hs1 hs2
    subst hs2
    rw [hs1]
    refine ⟨[.udf c], by simp [LState.emit], ⟨by simp [LState.emit], by simp [vdefs, operands_udf], ?_⟩⟩
    intro fr cm ρ w _ _ _ _
    obtain ⟨w'', h⟩ := seqRun_one_halt hR (operands_udf c) (ρ := ρ) (ispec_udf c w) rfl
    exact ⟨by simp [UsesOk, vuseNums, operands_udf], 0, _, _, _, _, _, _, h, rfl⟩
  | _ => simp [retOrTrap] at hrt

set_option maxHeartbeats 800000 in
/-- **`return`** (`rule_lower_2574`) over typed contexts: `rets` pinning each value to the next
return register of its class (`retRegsT`). -/
theorem ret_ruleOkT {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem}
    {MR : MemRelT} (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerTermRuleOkT isem MR p rule_lower_2574 := by
  intro f ctx hctx ti t data hrt hd hi cfg hc m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kR := fun n (hn : 60 ≤ n) xs s v s' h => lower_return_okTy hp (ctx := ctx) hc (n := n)
    (xs := xs) (s := s) (v := v) (s' := s') hn h
  cases t with
  | trap c =>
    rw [termData_trap] at hd; cases hd
    cases hp
    isel_inv [*, rule_lower_2574] at hmatch
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    simp at *
  | ret xs =>
    rw [termData_ret] at hd; cases hd
    cases hp
    ctl_inv [*, rule_lower_2574] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    repeat (isel_inv_simp [ext_value_list_slice_iff] at * <;> isel_destruct <;> subst_vars)
    have h294 := ‹ApplyInternal _ _ _ _ 25 294 _ _ _ _›
    obtain ⟨rs, hrs, ps, hps, hs, -⟩ := kR _ (by omega) _ _ _ _ h294
    simp only at hs
    subst hs
    have hrs' := mapM_valueRegT hctx.inv hrs
    subst hrs'
    have hcl : (Reg.homeCls ∘ fun x => Reg.vreg x (valClassOf ctx x)) = valClassOf ctx := by
      funext x; rfl
    rw [regsClasses_single, List.map_map, hcl] at hps
    simp only [List.length_map] at hps
    have hps' : ps = retRegsT ((xs.map (valClassOf ctx)).take
        (xs.length - (sretRet ctx.func).length)) 0 0 ++
        List.replicate (xs.length - (xs.length - (sretRet ctx.func).length)) (Reg.x 8) := by
      unfold retRegsK at hps
      obtain ⟨rs', h1, rfl⟩ := Option.map_eq_some_iff.mp hps
      rw [retRegsC_eq _ _ _ _ h1, List.length_map]
    have hpl : ps.length = xs.length := by
      rw [hps']; simp [retRegsT_length, List.length_take]
    have hz : (xs.map fun x => Reg.vreg x (valClassOf ctx x)).zip ps =
        argPairsC ((xs.zip ps).map fun q => (q.1, valClassOf ctx q.1, q.2)) := by
      simp [argPairsC, List.zip_map_left, Function.comp_def]
    rw [hz]
    generalize hns : (xs.zip ps).map (fun q => (q.1, valClassOf ctx q.1, q.2)) = ns
    have hfst : ns.map (·.1) = xs := by
      rw [← hns, List.map_map]
      exact List.map_fst_zip (by omega)
    have hsnd : ns.map (·.2.2) = ps := by
      rw [← hns, List.map_map]
      exact List.map_snd_zip (by omega)
    have hnl : ns.length = xs.length := by rw [← hns]; simp [hpl]
    refine ⟨[.rets (argPairsC ns)], by simp [LState.emit],
      ⟨by simp [LState.emit], by simp [vdefs_retsC], ?_⟩⟩
    intro fr cm ρ w _ hvh _ hmr
    show ∀ vals, fr.getMany xs = .ok vals → _
    intro vals hvals
    obtain ⟨hlen, hv⟩ := getMany_ok hvals
    obtain ⟨w'', hrun, hsw⟩ := seqRun_one_stop hR (operands_retsC ns) (ρ := ρ) (w := w)
      (ctl := .ret) (by simp) (ispec_rets _ _ w)
      (by rw [List.toList_toArray, filter_isDef_retOpsC]; rfl)
    refine ⟨?_, 0, _, _, _, _, _, _, hrun, ?_, ?_, ?_, hMR _ _ _ _ (SameWorld.nf hsw) hmr⟩
    · intro mi hmi u hu
      simp only [List.mem_singleton] at hmi
      subst hmi
      rw [vuseNums_retsC, hfst] at hu
      right
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
      obtain ⟨v, hv'⟩ : ∃ v, vals[j]? = some v := ⟨vals[j]'(by omega), by simp [hj, hlen]⟩
      rw [hv (j := j) _ v (by simp [hj]) hv']
      rfl
    · have hL : List.map (fun x => x.snd) (argPairsC ns) = ns.map (fun q => q.2.2) := by
        simp [argPairsC, List.map_map]
      rw [hL, hsnd]
      exact hps'
    · simp [argPairsC, hnl, hlen]
    · rw [vuses_retOpsC]
      have : ns.map (ρ ·.1) = xs.map ρ := by
        rw [show (fun q : Nat × RegClass × Reg => ρ q.1) = ρ ∘ (·.1) from rfl, ← List.map_map,
          hfst]
      refine ⟨by simp [this, hlen], fun j v x hvj hxj => ?_⟩
      rw [this, List.getElem?_map] at hxj
      cases hxj' : xs[j]? with
      | none => rw [hxj'] at hxj; cases hxj
      | some y =>
        rw [hxj'] at hxj
        cases hxj
        exact hvh y v (hv j y v hxj' hvj)
  | _ => simp [retOrTrap] at hrt

/-- **`LowerTermRulesCorrectT`**: the `trap` and class-aware `return` rules of `lower` are
correct over typed contexts. -/
theorem lowerTermRulesCorrectT_program : LowerTermRulesCorrectT program := by
  intro F isem MR hR hMR r hr hroot
  simp only [termRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
  rcases hroot with h | h
  · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2237 (by rw [h]; rfl)]
    exact trap_ruleOkT data_program hR
  · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2574 (by rw [h]; rfl)]
    exact ret_ruleOkT data_program hR hMR

end Backend.Proof
