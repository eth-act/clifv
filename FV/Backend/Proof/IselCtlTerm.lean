import FV.Backend.Proof.IselCtlBase
import FV.Backend.Proof.LowerLemmas

/-!
# Family Ctl: the `lower` rules on terminators (`trap`, `return`)

`LowerTermRuleOk` for `rule_lower_2237` (`trap` → `udf`, rule id 964) and `rule_lower_2574`
(`return` → `lower_return` → `rets` with the values in x0.., rule id 1037).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

theorem ofV_udf (c : Clif.TrapCode) : MInst.ofV (.data 58 123 [.op (.trapCode c)]) = some (.udf c) := rfl

theorem operands_udf (c : Clif.TrapCode) : (MInst.udf c).operands = .ok #[] := rfl

theorem ispec_udf (c : Clif.TrapCode) (w : Arm.ArmState) :
    ispec (.udf c) [] w = some ([], w, .halt) := rfl

/-! ## `rets` -/

/-- `(vreg x, p)` pairs of a `Rets`. -/
def retPairs (ns : List (Nat × Reg)) : List (Reg × Reg) := ns.map fun q => (Reg.vreg q.1 .int, q.2)

/-- The operands of `Rets (retPairs ns)`: fixed early uses. -/
def retOps (ns : List (Nat × Reg)) : List Operand :=
  ns.map fun q => (⟨q.1, .int, .use, .early, .fixed q.2⟩ : Operand)

open Driver in
theorem mapM_fixedUse (ns : List (Nat × Reg)) : ∀ (s : Array Operand),
    ((retPairs ns).mapM
      (fun (x : Reg × Reg) => do let r ← collectOp (OpSpec.fixedUse x.2) x.1; pure (r, x.2))).run s =
      .ok (retPairs ns, s ++ (retOps ns).toArray) := by
  induction ns with
  | nil => intro s; simp [retPairs, retOps] <;> rfl
  | cons q ns ih =>
    intro s
    simp only [retPairs, retOps, List.map_cons, List.mapM_cons, StateT.run_bind] at ih ⊢
    have h1 : (collectOp (OpSpec.fixedUse q.2) (Reg.vreg q.1 .int)).run s =
        .ok (Reg.vreg q.1 .int, s.push ⟨q.1, .int, .use, .early, .fixed q.2⟩) := rfl
    rw [h1, Driver.except_ok_bind, StateT.run_pure, Driver.except_pure, Driver.except_ok_bind, ih,
      Driver.except_ok_bind, StateT.run_pure, Driver.except_pure]
    simp

open Driver in
theorem operands_rets (ns : List (Nat × Reg)) :
    (MInst.rets (retPairs ns)).operands = .ok (retOps ns).toArray := by
  rw [operands_eq]
  simp only [MInst.visitOperands, StateT.run_bind, mapM_fixedUse]
  simp [bind, Except.bind, StateT.run, pure, StateT.pure, Except.pure]

theorem filter_retOps (ns : List (Nat × Reg)) : (retOps ns).filter Operand.isUse = retOps ns := by
  induction ns with
  | nil => rfl
  | cons q ns ih =>
    simp only [retOps, List.map_cons] at ih ⊢
    rw [List.filter_cons_of_pos (by rfl), ih]

theorem vuses_retOps {V : Type} (ns : List (Nat × Reg)) (ρ : Nat → V) :
    vuses (retOps ns).toArray ρ = ns.map (ρ ·.1) := by
  simp only [vuses, filter_retOps]
  simp [retOps]

theorem vuseNums_rets (ns : List (Nat × Reg)) : vuseNums (.rets (retPairs ns)) = ns.map (·.1) := by
  simp only [vuseNums, operands_rets, filter_retOps]
  simp [retOps]

theorem vdefs_rets (ns : List (Nat × Reg)) : vdefs (.rets (retPairs ns)) = [] := by
  simp only [vdefs, operands_rets]
  simp [retOps, Operand.isDef]
  intro _ _ _ _ h; subst h; simp

theorem retRegs_eq {n : Nat} {ps : List Reg} (h : retRegs n = some ps) :
    n ≤ 8 ∧ ps = (List.range n).map Reg.x := by
  unfold retRegs at h
  split at h
  · exact ⟨‹_›, (Option.some.inj h).symm⟩
  · cases h

/-- The value registers of `buildCtx` (`CtxInv.valueReg`). -/
theorem mapM_valueReg {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) :
    ∀ {xs : List Nat} {rs : List Reg}, xs.mapM ctx.valueReg? = some rs →
      rs = xs.map fun x => Reg.vreg x .int
  | [], rs, h => by simp at h; simp [h]
  | x :: xs, rs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨r, hr, rs', hrs, rfl⟩ := h
    rw [hctx.valueReg x r hr, mapM_valueReg hctx hrs]
    rfl

theorem getMany_ok {fr : Clif.Frame} :
    ∀ {xs : List Nat} {vals : List Clif.Val}, fr.getMany xs = .ok vals →
      vals.length = xs.length ∧ ∀ (j : Nat) x v, xs[j]? = some x → vals[j]? = some v → fr.regs x = some v
  | [], vals, h => by
    simp [Clif.Frame.getMany] at h; subst h; simp
  | x :: xs, vals, h => by
    simp only [Clif.Frame.getMany] at h
    cases hx : fr.get x with
    | ok v =>
      rw [hx] at h
      cases hxs : fr.getMany xs with
      | ok vs =>
        rw [hxs] at h
        simp [bind, Clif.Res.bind, pure] at h
        subst h
        obtain ⟨hl, hv⟩ := getMany_ok hxs
        refine ⟨by simp [hl], fun j y u hy hu => ?_⟩
        cases j with
        | zero =>
          simp at hy hu; subst hy hu
          simp only [Clif.Frame.get, Clif.Res.ofOption] at hx
          split at hx <;> simp_all
        | succ j => exact hv j y u (by simpa using hy) (by simpa using hu)
      | _ => rw [hxs] at h; simp [bind, Clif.Res.bind] at h
    | _ => rw [hx] at h; simp [bind, Clif.Res.bind] at h

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

include hp hc in
/-- `lower_return`: the value registers, `rets` pinning them to x0.. -/
theorem lower_return_ok {n : Nat} (hn : 60 ≤ n) {xs : List Nat} {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 25 294 [.values xs] s v s') :
    ∃ rs ps, xs.mapM ctx.valueReg? = some rs ∧ retRegs rs.length = some ps ∧
      s'.1 = s.1.emit (.rets (rs.zip ps)) ∧ v = .regsVec [] := by
  isel_split hp hc h 294
  ctl_inv [*, rule_prelude_lower_1493] at hm he
  simp only [mapM_single_map, List.length_map, Option.some.injEq] at *
  subst_vars
  exact ⟨_, ‹_›, _, ‹_›, rfl⟩

end

/-- **`trap`** (`rule_lower_2237`). -/
theorem trap_ruleOk {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    (hR : Refines F isem) : LowerTermRuleOk isem MR p rule_lower_2237 := by
  intro f ctx hctx ti t data hrt hd hi cfg hc m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
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

theorem ispec_rets (us : List (Reg × Reg)) (uses : List CV) (w : Arm.ArmState) :
    ispec (.rets us) uses w = some ([], w, .ret) := rfl

theorem filter_isDef_retOps (ns : List (Nat × Reg)) : (retOps ns).filter Operand.isDef = [] := by
  simp [retOps, Operand.isDef]
  intro _ _ _ _ h; subst h; simp

set_option maxHeartbeats 800000 in
/-- **`return`** (`rule_lower_2574`). -/
theorem ret_ruleOk {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    (hR : Refines F isem) (hMR : MRStable F MR) : LowerTermRuleOk isem MR p rule_lower_2574 := by
  intro f ctx hctx ti t data hrt hd hi cfg hc m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kR := fun n (hn : 60 ≤ n) xs s v s' h => lower_return_ok hp (ctx := ctx) hc (n := n)
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
    have hrs' := mapM_valueReg hctx hrs
    subst hrs'
    obtain ⟨h8, rfl⟩ := retRegs_eq hps
    simp only [List.length_map] at h8 ⊢
    have hz : (xs.map fun x => Reg.vreg x .int).zip ((List.range xs.length).map Reg.x) =
        retPairs (xs.zip ((List.range xs.length).map Reg.x)) := by
      simp [retPairs, List.zip_map_left, Prod.map]
    rw [hz]
    refine ⟨[.rets (retPairs (xs.zip ((List.range xs.length).map Reg.x)))], by simp [LState.emit],
      ⟨by simp [LState.emit], by simp [vdefs_rets], ?_⟩⟩
    intro fr cm ρ w _ hvh _ hmr
    show ∀ vals, fr.getMany xs = .ok vals → _
    intro vals hvals
    obtain ⟨hlen, hv⟩ := getMany_ok hvals
    have hfst : (xs.zip ((List.range xs.length).map Reg.x)).map (·.1) = xs :=
      List.map_fst_zip (by simp)
    have hsnd : (xs.zip ((List.range xs.length).map Reg.x)).map (·.2) =
        (List.range xs.length).map Reg.x := List.map_snd_zip (by simp)
    obtain ⟨w'', hrun, hsw⟩ := seqRun_one_stop hR
      (operands_rets (xs.zip ((List.range xs.length).map Reg.x))) (ρ := ρ) (w := w) (ctl := .ret)
      (by simp) (ispec_rets _ _ w) (by rw [List.toList_toArray, filter_isDef_retOps]; rfl)
    refine ⟨?_, 0, _, _, _, _, _, _, hrun, ?_, ?_, ?_, hMR _ _ _ _ (SameWorld.nf hsw) hmr⟩
    · intro mi hmi u hu
      simp only [List.mem_singleton] at hmi
      subst hmi
      rw [vuseNums_rets, hfst] at hu
      right
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
      obtain ⟨v, hv'⟩ : ∃ v, vals[j]? = some v := ⟨vals[j]'(by omega), by simp [hj, hlen]⟩
      rw [hv (j := j) _ v (by simp [hj]) hv']
      rfl
    · simp [retPairs, List.map_map, Function.comp_def] at hsnd ⊢
      rw [hsnd]
    · simp [retPairs, hlen]
    · rw [vuses_retOps]
      have : (xs.zip ((List.range xs.length).map Reg.x)).map (ρ ·.1) = xs.map ρ := by
        rw [show (fun q : Nat × Reg => ρ q.1) = ρ ∘ (·.1) from rfl, ← List.map_map, hfst]
      refine ⟨by simp [this, hlen], fun j v x hvj hxj => ?_⟩
      rw [this, List.getElem?_map] at hxj
      cases hxj' : xs[j]? with
      | none => rw [hxj'] at hxj; cases hxj
      | some y =>
        rw [hxj'] at hxj
        cases hxj
        exact hvh y v (hv j y v hxj' hvj)
  | _ => simp [retOrTrap] at hrt

end Backend.Proof
