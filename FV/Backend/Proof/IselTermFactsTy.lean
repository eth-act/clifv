import FV.Backend.Proof.IselTermIntPos
import FV.Compile.SubsetT
import FV.Backend.Proof.IselTermFacts
import FV.Backend.Proof.SpillEdgesIsel
import FV.Backend.Proof.IselFlow

/-!
# The emitted code of the terminator rules over float-capable contexts (S11e5 Stage C)

`IselTermFactsRules` and `SpillEdgesIsel` run the terminator rules symbolically for the shape
of their code over integer contexts (`CtxInv`). This file runs them over float-capable contexts
(`CtxInvT`): a `return` pins values of either class (`lower_return_okTy`: `rets` at the
signature's return registers, x0.. or v0..), a `brif` tests a condition in an integer position
and a `br_table` dispatches on one (`TermIntPos`, from `Compile.termIntOperands`: the CLIF
verifier's typing, in the scope through `Compile.opsTypedT`), the `tbz`/`tbnz` look-through
reads the integer operand of a `band` (`CtxInvT.intOps`).

The suffix `Ty` marks the typed variants (`TermShapeT`, `LowerTermShapeOkT`, `trap_shapeT`,
`ret_shapeT` and `termShapeT_runTerm` already name the integer ones with the stronger
`return`/`trap` conclusion).

* `termShape_runTermTy`: `lower` on a `return`/`trap` appends code ending in an instruction
  without successors;
* `branchShape_runTermTy`: `lower_branch` on a branch appends code ending in an instruction
  targeting the branch's labels; `jumpShape_runTermTy`: exactly the `jump` on a `jump`;
* `term_emitsTy`: the lowering of a non-`try_call` terminator emits code (`term_emits`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- On an integer context every terminator operand is in an integer position. -/
theorem CtxInv.termIntPos {f : Clif.Function} {ctx : Ctx} (h : CtxInv f ctx) (t : Clif.Terminator) :
    TermIntPos ctx t :=
  fun x _ => h.intPos x

/-! ## Contexts -/

/-- Filling in the terminator's data at `buildCtx`'s placeholder keeps `CtxInvT`. -/
theorem ctxInvT_termCtx {f : Clif.Function} {ctx : Ctx} (h : CtxInvT f ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (data : V) :
    CtxInvT f (Driver.termCtx ctx ti data) := by
  have hne : ∀ x d, ctx.defInst? x = some d → d ≠ ti := by
    intro x d hd e
    subst e
    obtain ⟨info, hi, hx⟩ := h.defInst x d hd
    rw [hph] at hi; cases hi; cases hx
  refine ⟨h.func, fun ii info inst hi hc => ?_, fun ii info inst hi hc => ?_, h.valueReg,
    h.typedReg, fun x d hd => ?_, fun x d info hd hi => ?_, h.slotOff, fun ii info hi => ?_,
    h.valTyM, fun ii info inst x hi hc hx => ?_, fun ii info inst hi hc => ?_⟩
  · by_cases e : ii = ti
    · subst e; rw [Driver.termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [Driver.termCtx_insts_ne e] at hi; exact h.data ii info inst hi hc
  · by_cases e : ii = ti
    · subst e; rw [Driver.termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [Driver.termCtx_insts_ne e] at hi; exact h.resTys ii info inst hi hc
  · rw [Driver.termCtx_insts_ne (hne x d hd)]; exact h.defInst x d hd
  · rw [Driver.termCtx_insts_ne (hne x d hd)] at hi; exact h.defClif x d info hd hi
  · by_cases e : ii = ti
    · subst e; rw [Driver.termCtx_insts_self hph] at hi; cases hi; intro t ht; cases ht
    · rw [Driver.termCtx_insts_ne e] at hi; exact h.resTysM ii info hi
  · by_cases e : ii = ti
    · subst e; rw [Driver.termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [Driver.termCtx_insts_ne e] at hi; exact h.addr64 ii info inst x hi hc hx
  · by_cases e : ii = ti
    · subst e; rw [Driver.termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [Driver.termCtx_insts_ne e] at hi; exact h.intOps ii info inst hi hc

/-- The terminator's context keeps `CtxInvT` and holds the terminator's data at `ti`. -/
theorem termCtx_factsTy {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some (⟨.op .unit, [], [], none⟩ : IInfo)) (data : V) :
    CtxInvT f (Driver.termCtx ctx ti data) ∧
      (Driver.termCtx ctx ti data).insts[ti]? = some ⟨data, [], [], none⟩ :=
  ⟨ctxInvT_termCtx hctx hph data, Driver.termCtx_insts_self hph data⟩

/-- The instruction behind a matched data value (`ctxInv_clif` over `CtxInvT`). -/
theorem ctxInvT_clif {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {y j : Nat}
    {info : IInfo} (hj : ctx.defInst? y = some j) (hi : ctx.insts[j]? = some info) :
    ∃ cl, info.clif = some cl ∧ instData f cl = .ok info.data := by
  obtain ⟨cl, hcl⟩ := Option.isSome_iff_exists.mp (hctx.defClif y j info hj hi)
  exact ⟨cl, hcl, hctx.data j info cl hi hcl⟩

/-! ## `lower_return` over float-capable contexts -/

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

include hp hc in
/-- `lower_return` on values of either class: the value registers, `rets` pinning them to the
return registers (`retRegsK`: the first declared returns as `retRegsC` places them, an `sret`
signature's struct pointer in x8). -/
theorem lower_return_okTy {n : Nat} (hn : 60 ≤ n) {xs : List Nat} {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 25 294 [.values xs] s v s') :
    ∃ rs ps, xs.mapM ctx.valueReg? = some rs ∧
      retRegsK (rs.length - (sretRet ctx.func).length)
          (regsClasses (rs.map fun r => [r])) = some ps ∧
      s'.1 = s.1.emit (.rets (rs.zip ps)) ∧ v = .regsVec [] := by
  isel_split hp hc h 294
  ctl_inv [*, rule_prelude_lower_1493] at hm he
  simp only [mapM_single_map, List.length_map, Option.some.injEq] at *
  subst_vars
  exact ⟨_, ‹List.mapM ctx.valueReg? xs = some _›, _, ‹retRegsK _ _ = some _›, rfl⟩

end

/-! ## Shapes over float-capable contexts -/

/-- `LowerTermShapeOkT` over float-capable contexts. -/
def LowerTermShapeOkTy (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInvT f ctx →
  ∀ (ti : Nat) (t : Clif.Terminator) (data : V), retOrTrap t = true → termData t = .ok data →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti]).run (st, tr) = .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ti]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    TermShapeT st st'

/-- `BranchShapeOk` over float-capable contexts, on a branch whose integer operands are in
integer positions. -/
def BranchShapeOkTy (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInvT f ctx →
  ∀ (ti : Nat) (t : Clif.Terminator) (data : V) (targets : List Label), termData t = .ok data →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ → BrIdxTyped ctx t → TermIntPos ctx t →
  TargetsLen t targets →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (∀ pre post, p.rulesOf TId.lower_branch = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti, .labels targets]).run (st, tr) =
        .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ti, .labels targets]).run (st, tr) =
      .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    BranchShape st st' targets

/-! ## `return`, `trap` -/

set_option maxHeartbeats 800000 in
/-- **`trap`** (`rule_lower_2237`): `udf`. -/
theorem trap_shapeTy {p : Program} (hp : Data p) : LowerTermShapeOkTy p rule_lower_2237 := by
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
    simp only at hs1 hs2
    subst hs2
    rw [hs1]
    rw [ofV_udf] at hmi
    cases hmi
    exact ⟨[], .udf c, by simp [LState.emit], rfl⟩
  | _ => simp [retOrTrap] at hrt

set_option maxHeartbeats 800000 in
/-- **`return`** (`rule_lower_2574`): `rets`, of values of either class. -/
theorem ret_shapeTy {p : Program} (hp : Data p) : LowerTermShapeOkTy p rule_lower_2574 := by
  intro f ctx _ ti t data hrt hd hi cfg hc m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
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
    exact ⟨[], .rets (rs.zip ps), by simp [LState.emit], rfl⟩
  | _ => simp [retOrTrap] at hrt

/-! ## Branches -/

/-- **`jump`** (`rule_lower_3270`). -/
theorem jump_shapeTy {p : Program} (hp : Data p) : BranchShapeOkTy p rule_lower_3270 := by
  intro f ctx _ ti t data targets hd hi _ _ _ cfg hc m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  have hf := ruleFmt_term hp (r := rule_lower_3270) rfl hp.t2462 term_2462_kind hd hi hmatch
  cases t with
  | jump d =>
    obtain ⟨l, he, rfl⟩ := jump_shapeJ hp hd hi hc hm hn hmatch heval
    exact ⟨[], .jump l, he, rfl⟩
  | _ => simp [termFmt] at hf

set_option maxHeartbeats 4000000 in
/-- **`lower_brif`** (`rule_lower_3231`): the condition's code (on an integer-position
condition), then a conditional branch. -/
theorem brif_shapeTy {p : Program} (hp : Data p) : BranchShapeOkTy p rule_lower_3231 := by
  intro f ctx hctx ti t data targets hd hi _ hip _ cfg hc m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kE2 := fun n (hn : 30 ≤ n) i j s v s' h => emit_side_effect_inst2_ok hp (ctx := ctx) hc
    (n := n) (i := i) (j := j) (s := s) (v := v) (s' := s') hn h
  have kB := fun n (hn : 100 ≤ n) c P (hsh : CondShape c P) a b s v s' h =>
    br_cond_result_ok hp (ctx := ctx) hc (n := n) (c := c) (P := P) (a := a) (b := b) (s := s)
      (v := v) (s' := s') hn hsh h
  have kNZ := fun n (hn : 300 ≤ n) x (hxi : IntPos ctx x) s c s' hvb h =>
    is_nonzero_cmp_okT hp hc refines_ispec hctx (n := n) hn (x := x) hxi (s := s) (c := c)
      (s' := s') hvb h
  have hf := ruleFmt_term hp (r := rule_lower_3231) rfl hp.t2452 term_2452_kind hd hi hmatch
  cases t with
  | brif x tb eb =>
    have hxi : IntPos ctx x := hip x (by simp [Compile.termIntOperands])
    rw [termData_brif] at hd; cases hd
    cases hp
    brif_inv [*, rule_lower_3231] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    have hdat := ‹V.data 152 5 _ = _›
    simp only [V.data.injEq, List.cons.injEq, and_true, true_and] at hdat
    obtain ⟨rfl, rfl⟩ := hdat
    have h650 := ‹ApplyInternal _ _ _ _ 123 650 _ _ _ _›
    obtain ⟨ms0, hfr, hsh, -⟩ := kNZ _ (by omega) _ hxi _ _ _ hvb h650
    have h722 := ‹ApplyInternal _ _ _ _ 46 722 _ _ _ _›
    obtain ⟨hs2, rfl⟩ := kB _ (by omega) _ _ hsh _ _ _ _ _ h722
    have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    rcases hsh with ⟨k, i, sz, rfl, hsz, -⟩ | ⟨k, i, sz, rfl, hsz, -⟩ |
      ⟨mi, mm, cond, rfl, hmi, -, -, hdm, -⟩
    · obtain ⟨mi', hmi', hs3, -⟩ := kE _ (by omega) _ _ _ _ h242
      rw [ofV_condBr_zero hsz] at hmi'
      cases hmi'
      simp only at hs2 hs3
      rw [hs3, hs2]
      exact ⟨ms0, _, emitted_emit_of_frag hfr _, rfl⟩
    · obtain ⟨mi', hmi', hs3, -⟩ := kE _ (by omega) _ _ _ _ h242
      rw [ofV_condBr_notZero hsz] at hmi'
      cases hmi'
      simp only at hs2 hs3
      rw [hs3, hs2]
      exact ⟨ms0, _, emitted_emit_of_frag hfr _, rfl⟩
    · obtain ⟨m1, m2, hs3, hm1, hm2⟩ := kE2 _ (by omega) _ _ _ _ _ h242
      rw [hmi] at hm1
      cases hm1
      rw [ofV_condBr_cond] at hm2
      cases hm2
      simp only at hs2 hs3
      rw [hs3, hs2]
      exact ⟨ms0 ++ [mm], _, emitted_emit_of_frag (hfr.append (Frag.emit_nodef _ hdm)) _, rfl⟩
  | _ => simp [termFmt] at hf

set_option maxHeartbeats 4000000 in
/-- **`tbnz`** (`rule_lower_3251`): the tested value is the integer operand of a `band`. -/
theorem tbnz_shapeTy {p : Program} (hp : Data p) : BranchShapeOkTy p rule_lower_3251 := by
  intro f ctx hctx ti t data targets hd hi _ _ _ cfg hc m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kT := fun n (hn : 60 ≤ n) a b r bit s v s' h => tbnz_inst_ok hp (ctx := ctx) hc (n := n)
    (a := a) (b := b) (r := r) (bit := bit) (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have hf := ruleFmt_term hp (r := rule_lower_3251) rfl hp.t2452 term_2452_kind hd hi hmatch
  cases t with
  | brif x tb eb =>
    rw [termData_brif] at hd; cases hd
    cases hp
    brif_inv [*, rule_lower_3251, ctor_tcbc_iff] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    have hdat := ‹V.data 152 5 _ = _›
    simp only [V.data.injEq, List.cons.injEq, and_true, true_and] at hdat
    obtain ⟨rfl, rfl⟩ := hdat
    repeat (isel_inv_simp [ctor_tcbc_iff] at * <;> isel_destruct <;> subst_vars)
    obtain ⟨hj1⟩ : Nonempty (ctx.defInst? x = some _) := ⟨‹_›⟩
    obtain ⟨hi1⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹ctx.insts[_]? = some _›⟩
    obtain ⟨cl1, hcl1, hdat1⟩ := ctxInvT_clif hctx hj1 hi1
    obtain ⟨hd1⟩ : Nonempty (V.data 152 2 _ = _) := ⟨‹_›⟩
    rw [← hd1] at hdat1
    obtain ⟨ty1, a, b, rfl, he1, hfs1⟩ := instData_binary_inv (cop := .band) variantNames_Band rfl hdat1
    have hai : IntPos ctx a := hctx.intOps _ _ _ hi1 hcl1 a (by simp [intArgs])
    simp only [List.cons.injEq, and_true] at hfs1
    subst hfs1
    repeat (isel_inv_simp [ctor_tcbc_iff] at * <;> isel_destruct <;> subst_vars)
    obtain ⟨hj2⟩ : Nonempty (ctx.defInst? b = some _) := ⟨‹_›⟩
    obtain ⟨hd2⟩ : Nonempty (V.data 152 35 _ = _) := ⟨‹_›⟩
    obtain ⟨hi2⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹ctx.insts[_]? = some _›⟩
    obtain ⟨ty2, imm, rfl, he2, hcl2⟩ := iconst_data_invT hctx hj2 hi2 hd2
    repeat (isel_inv_simp [ctor_tcbc_iff] at * <;> isel_destruct <;> subst_vars)
    have hra := hctx.valueReg_int ‹ctx.valueReg? a = some _› hai
    subst hra
    have h667 := ‹ApplyInternal _ _ _ _ 46 667 _ _ _ _›
    obtain ⟨hs1, rfl⟩ := kT _ (by omega) _ _ _ _ _ _ _ h667
    have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
    rw [ofV_tbb_nz] at hmi
    cases hmi
    simp only at hs1 hs2
    rw [hs2, hs1]
    exact ⟨[], _, emitted_emit _ _, rfl⟩
  | _ => simp [termFmt] at hf

set_option maxHeartbeats 4000000 in
/-- **`tbz`** (`rule_lower_3257`): the tested value is the integer operand of a `band`. -/
theorem tbz_shapeTy {p : Program} (hp : Data p) : BranchShapeOkTy p rule_lower_3257 := by
  intro f ctx hctx ti t data targets hd hi _ _ _ cfg hc m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kT := fun n (hn : 60 ≤ n) a b r bit s v s' h => tbz_inst_ok hp (ctx := ctx) hc (n := n)
    (a := a) (b := b) (r := r) (bit := bit) (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have hf := ruleFmt_term hp (r := rule_lower_3257) rfl hp.t2452 term_2452_kind hd hi hmatch
  cases t with
  | brif x tb eb =>
    rw [termData_brif] at hd; cases hd
    cases hp
    brif_inv [*, rule_lower_3257, ctor_tcbc_iff, ext_fits_in_64_iff] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    have hdat := ‹V.data 152 5 _ = _›
    simp only [V.data.injEq, List.cons.injEq, and_true, true_and] at hdat
    obtain ⟨rfl, rfl⟩ := hdat
    repeat (isel_inv_simp [ctor_tcbc_iff, ext_fits_in_64_iff] at * <;> isel_destruct <;> subst_vars)
    obtain ⟨hj0⟩ : Nonempty (ctx.defInst? x = some _) := ⟨‹_›⟩
    obtain ⟨hi0⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹ctx.insts[_]? = some _›⟩
    obtain ⟨cl0, hcl0, hdat0⟩ := ctxInvT_clif hctx hj0 hi0
    obtain ⟨hd0⟩ : Nonempty (V.data 152 14 _ = _) := ⟨‹_›⟩
    rw [← hd0] at hdat0
    obtain ⟨cc, tyc, c, z, rfl, rfl, hcc⟩ := instData_icmp_inv hdat0
    have hcc' : cc = .eq := by cases cc <;> simp_all [ccIdx]
    subst hcc'
    repeat (isel_inv_simp [ctor_tcbc_iff, ext_fits_in_64_iff] at * <;> isel_destruct <;> subst_vars)
    obtain ⟨j1, hj1, info1, hi1, hd1⟩ : ∃ j, ctx.defInst? c = some j ∧ ∃ i, ctx.insts[j]? = some i ∧
      V.data 152 2 _ = i.data := ⟨_, ‹_›, _, ‹_›, ‹_›⟩
    obtain ⟨j3, hj3, info3, hi3, hd3⟩ : ∃ j, ctx.defInst? z = some j ∧ ∃ i, ctx.insts[j]? = some i ∧
      V.data 152 35 _ = i.data := ⟨_, ‹_›, _, ‹_›, ‹_›⟩
    obtain ⟨ty3, imm0, rfl, he3, hcl3⟩ := iconst_data_invT hctx hj3 hi3 hd3
    obtain ⟨cl1, hcl1, hdat1⟩ := ctxInvT_clif hctx hj1 hi1
    rw [← hd1] at hdat1
    obtain ⟨ty1, a, b, rfl, he1, hfs1⟩ := instData_binary_inv (cop := .band) variantNames_Band rfl hdat1
    have hai : IntPos ctx a := hctx.intOps _ _ _ hi1 hcl1 a (by simp [intArgs])
    simp only [List.cons.injEq, and_true] at hfs1
    subst hfs1
    repeat (isel_inv_simp [ctor_tcbc_iff, ext_fits_in_64_iff] at * <;> isel_destruct <;> subst_vars)
    obtain ⟨j2, hj2, info2, hi2, hd2⟩ : ∃ j, ctx.defInst? b = some j ∧ ∃ i, ctx.insts[j]? = some i ∧
      V.data 152 35 _ = i.data := ⟨_, ‹_›, _, ‹_›, ‹_›⟩
    obtain ⟨ty2, imm, rfl, he2, hcl2⟩ := iconst_data_invT hctx hj2 hi2 hd2
    repeat (isel_inv_simp [ctor_tcbc_iff, ext_fits_in_64_iff] at * <;> isel_destruct <;> subst_vars)
    have hra := hctx.valueReg_int ‹ctx.valueReg? a = some _› hai
    subst hra
    have h668 := ‹ApplyInternal _ _ _ _ 46 668 _ _ _ _›
    obtain ⟨hs1, rfl⟩ := kT _ (by omega) _ _ _ _ _ _ _ h668
    have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
    rw [ofV_tbb_z] at hmi
    cases hmi
    simp only at hs1 hs2
    rw [hs2, hs1]
    exact ⟨[], _, emitted_emit _ _, rfl⟩
  | _ => simp [termFmt] at hf

set_option maxHeartbeats 8000000 in
/-- **`br_table`** (`rule_lower_3277`): `emit_island`, the extension of the (integer-position)
index, the bound check, `jt_sequence`. -/
theorem brTable_shapeTy {p : Program} (hp : Data p) : BranchShapeOkTy p rule_lower_3277 := by
  intro f ctx hctx ti t data targets hd hi hbt hip htl cfg hc m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  have kS := fun n (hn : 60 ≤ n) i s v s' h => side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kI := fun n (hn : 30 ≤ n) k s v s' h => emit_island_ok hp (ctx := ctx) hc (n := n)
    (k := k) (s := s) (v := v) (s' := s') hn h
  have kZ := fun n (hn : 40 ≤ n) x s v s' h => zext32_ok hp (ctx := ctx) hc (n := n)
    (x := x) (s := s) (v := v) (s' := s') hn h
  have kB := fun n (hn : 300 ≤ n) k r d ts s v s' hk hr h => br_table_impl_ok hp (ctx := ctx) hc
    refines_ispec (n := n) (k := k) (r := r) (d := d) (ts := ts) (s := s) (v := v) (s' := s') hn hk
    hr h
  have hf := ruleFmt_term hp (r := rule_lower_3277) rfl hp.t2451 term_2451_kind hd hi hmatch
  cases t with
  | brTable x dc tbl =>
    have hxi : IntPos ctx x := hip x (by simp [Compile.termIntOperands])
    rw [termData_brTable] at hd; cases hd
    cases hp
    brif_inv [*, rule_lower_3277, ext_jump_table_targets_iff, ctor_jump_table_size_iff,
      ctor_targets_jt_space_iff, ctor_u32_into_u64_iff] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    repeat (isel_inv_simp [ext_jump_table_targets_iff, ctor_jump_table_size_iff,
      ctor_targets_jt_space_iff, ctor_u32_into_u64_iff] at * <;> isel_destruct <;> subst_vars)
    rename LState => st
    obtain ⟨⟨wx, hwx, hTx⟩, htbl⟩ := hbt _ _ _ rfl
    have hlen := htl _ _ _ rfl
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    have h669 := ‹ApplyInternal _ _ _ _ 46 669 _ _ _ _›
    obtain ⟨hs1, rfl⟩ := kI _ (by omega) _ _ _ _ h669
    have h243 := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
    obtain ⟨mi, hmi, hs2, -⟩ := kS _ (by omega) _ _ _ _ h243
    rw [show ∀ n : Nat, (4 * (8 + (n : Int))) = ((4 * (8 + n) : Nat) : Int) from
      fun n => by push_cast; omega, ofV_emitIsland] at hmi
    cases hmi
    have h556 := ‹ApplyInternal _ _ _ _ 27 556 _ _ _ _›
    have hext := kZ _ (by omega) _ _ _ _ h556
    rw [hs2, hs1] at hext
    obtain ⟨k, msx, rfl, hFx, hkl, -, -⟩ := ExtOut.semT refines_ispec hctx hxi
      (pass := [.int 32, .int 64]) (by exact hvb) (.inl rfl) (by simp) (fun _ => by simp) hext
    have h670 := ‹ApplyInternal _ _ _ _ 13 670 _ _ _ _›
    have hJ := kB _ (by omega) _ _ _ _ _ _ _ (by omega) hkl h670
    simp only at hJ
    obtain ⟨ms0, st2, t1, t2, hF0, rfl, -⟩ := hJ
    have hFall := ((Frag.emit_nodef _ (m := .emitIsland _) rfl).append hFx).append hF0
    exact ⟨_, _, emitted_emit_of_frag hFall _, rfl⟩
  | _ => simp [termFmt] at hf

/-! ## From the rules to the driver's calls -/

/-- The root rules of `lower_branch` outside the closure never match a branch terminator (in
any context: `branchExcludedUnmatchable` without `CtxInv`, which its proof does not use). -/
theorem branch_excl_nomatch {ctx : Ctx} {ti : Nat} {t : Clif.Terminator} {data : V}
    {targets : List Label} (hrt : retOrTrap t = false) (hd : termData t = .ok data)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) {r : Rule}
    (hr : r ∈ program.rulesOf TId.lower_branch) (hroot : closureRoot r = false) :
    ∀ m s0 env s1, (matchRule program (sem ctx) {} m r [.inst ti, .labels targets]).run s0 ≠
      .ok (some env, s1) := by
  intro m s env' s1 hmatch
  have hok := List.all_eq_true.mp lower_branch_fmts r hr
  simp only [branchFmtOk, hroot, Bool.false_or] at hok
  split at hok
  · rename_i fT hfT
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hok
    obtain ⟨⟨⟨⟨hlo, hhi⟩, h1⟩, h2⟩, h3⟩ := hok
    obtain ⟨info, fs, hinfo, hdat⟩ :=
      ruleFmt_match (vs := [.labels targets]) data_program fmtKinds_program hfT hlo hhi hmatch
    rw [hi] at hinfo
    cases hinfo
    obtain ⟨fs', rfl⟩ := termData_fmt hd
    simp only [V.data.injEq] at hdat
    cases t <;> simp [retOrTrap] at hrt <;> simp [termFmt] at hdat <;>
      first | omega | simp [termData, throw, throwThe, MonadExceptOf.throw] at hd
  · cases hok

/-- **`lower` on a `return`/`trap`** (float-capable context) appends code ending in an
instruction without successors. -/
theorem termShape_runTermTy {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {ti : Nat}
    {t : Clif.Terminator} {data : V} (hrt : retOrTrap t = true) (hd : termData t = .ok data)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) {st : LState} {out : V} {st' : LState}
    {tr : List RuleId} (hvb : ValsBelow ctx st)
    (h : runTerm ctx "lower" [.inst ti] st = .ok (some out, st', tr)) : TermShapeT st st' := by
  obtain ⟨r, hr, m, n, env', s1, tr2, hm, hn, hfirst, hmatch, heval⟩ := runTerm_lower_rule h
  cases hroot : termRootRule r
  · exact absurd hmatch (Driver.lower_term_nomatch hrt hd hi hr hroot m (st, #[]) env' s1)
  · simp only [termRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
    rcases hroot with e | e
    · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2237 (by rw [e]; rfl)] at hfirst hmatch heval
      exact trap_shapeTy data_program f ctx hctx ti t data hrt hd hi {} rfl m n st #[] env' s1 out
        st' tr2 hm hn hvb hfirst hmatch heval
    · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2574 (by rw [e]; rfl)] at hfirst hmatch heval
      exact ret_shapeTy data_program f ctx hctx ti t data hrt hd hi {} rfl m n st #[] env' s1 out
        st' tr2 hm hn hvb hfirst hmatch heval

set_option maxHeartbeats 800000 in
/-- **`lower_branch` on a branch** (float-capable context, integer-position operands) appends
code whose last instruction targets the branch's labels. -/
theorem branchShape_runTermTy {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {ti : Nat}
    {t : Clif.Terminator} {data : V} {targets : List Label} (hrt : retOrTrap t = false)
    (hd : termData t = .ok data) (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩)
    (hbt : BrIdxTyped ctx t) (hip : TermIntPos ctx t) (htl : TargetsLen t targets) {st : LState}
    {out : V} {st' : LState} {tr : List RuleId} (hvb : ValsBelow ctx st)
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] st = .ok (some out, st', tr)) :
    BranchShape st st' targets := by
  obtain ⟨r, hr, m, n, env', s1, tr2, hm, hn, hfirst, hmatch, heval⟩ := runTerm_lower_branch_rule h
  cases hroot : closureRoot r
  · exact absurd hmatch (branch_excl_nomatch hrt hd hi hr hroot m (st, #[]) env' s1)
  · have hr' := hr
    rw [show TId.lower_branch = 687 from rfl, data_program.r687] at hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hroot (by decide +kernel)
    · exact tbnz_shapeTy data_program f ctx hctx ti t data targets hd hi hbt hip htl {} rfl m n st
        #[] env' s1 out st' tr2 hm hn hvb hfirst hmatch heval
    · exact tbz_shapeTy data_program f ctx hctx ti t data targets hd hi hbt hip htl {} rfl m n st
        #[] env' s1 out st' tr2 hm hn hvb hfirst hmatch heval
    · exact absurd hroot (by decide +kernel)
    · exact absurd hroot (by decide +kernel)
    · exact brif_shapeTy data_program f ctx hctx ti t data targets hd hi hbt hip htl {} rfl m n st
        #[] env' s1 out st' tr2 hm hn hvb hfirst hmatch heval
    · exact jump_shapeTy data_program f ctx hctx ti t data targets hd hi hbt hip htl {} rfl m n st
        #[] env' s1 out st' tr2 hm hn hvb hfirst hmatch heval
    · exact brTable_shapeTy data_program f ctx hctx ti t data targets hd hi hbt hip htl {} rfl m n st
        #[] env' s1 out st' tr2 hm hn hvb hfirst hmatch heval

set_option maxHeartbeats 800000 in
/-- **`lower_branch` on a `jump`** appends exactly the `jump` (in any context). -/
theorem jumpShape_runTermTy {ctx : Ctx} {ti : Nat} {d : Clif.BlockCall} {data : V}
    {targets : List Label} (hd : termData (.jump d) = .ok data)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) {st : LState} {out : V} {st' : LState}
    {tr : List RuleId}
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] st = .ok (some out, st', tr)) :
    JumpShape st st' targets := by
  obtain ⟨r, hr, m, n, env', s1, tr2, hm, hn, hfirst, hmatch, heval⟩ := runTerm_lower_branch_rule h
  have hrt : retOrTrap (.jump d) = false := rfl
  cases hroot : closureRoot r
  · exact absurd hmatch (branch_excl_nomatch hrt hd hi hr hroot m (st, #[]) env' s1)
  · have hr' := hr
    rw [show TId.lower_branch = 687 from rfl, data_program.r687] at hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hroot (by decide +kernel)
    · have hf := ruleFmt_term data_program (r := rule_lower_3251) rfl data_program.t2452
        term_2452_kind hd hi hmatch
      simp [termFmt] at hf
    · have hf := ruleFmt_term data_program (r := rule_lower_3257) rfl data_program.t2452
        term_2452_kind hd hi hmatch
      simp [termFmt] at hf
    · exact absurd hroot (by decide +kernel)
    · exact absurd hroot (by decide +kernel)
    · have hf := ruleFmt_term data_program (r := rule_lower_3231) rfl data_program.t2452
        term_2452_kind hd hi hmatch
      simp [termFmt] at hf
    · exact jump_shapeJ data_program hd hi rfl hm hn hmatch heval
    · have hf := ruleFmt_term data_program (r := rule_lower_3277) rfl data_program.t2451
        term_2451_kind hd hi hmatch
      simp [termFmt] at hf

/-- **The lowering of a non-`try_call` terminator emits code** (float-capable context, the
terminator's integer operands in integer positions; `term_emits` over `CtxInvT`). -/
theorem term_emitsTy {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some (⟨.op .unit, [], [], none⟩ : IInfo))
    {t : Clif.Terminator} (ht : t.isTry = false) {data : V}
    (hd : termData (abiTerm f t) = .ok data) {targets : List Label} (htg : TargetsLen t targets)
    {s : LState} (hvb : ValsBelow ctx s) (hbt : BrIdxTyped ctx t) (hip : TermIntPos ctx t)
    {out : V} {s' : LState} {tr : List Isle.RuleId}
    (h : Driver.termCallF ctx ti data t targets s = .ok (some out, s', tr)) :
    s.emitted.size < s'.emitted.size := by
  obtain ⟨hctx', hi'⟩ := termCtx_factsTy hctx hph data
  have hvb' : ValsBelow (Driver.termCtx ctx ti data) s := hvb
  have hbt' : BrIdxTyped (Driver.termCtx ctx ti data) t := hbt
  have hip' : TermIntPos (Driver.termCtx ctx ti data) t := hip
  unfold Driver.termCallF at h
  cases t with
  | ret xs =>
    obtain ⟨ms, i, hem, -⟩ := termShape_runTermTy (t := .ret (xs ++ sretRet f)) hctx' rfl hd hi'
      hvb' h
    rw [hem]; simp
  | trap c =>
    obtain ⟨ms, i, hem, -⟩ := termShape_runTermTy (t := .trap c) hctx' rfl hd hi' hvb' h
    rw [hem]; simp
  | jump d =>
    obtain ⟨ms, i, hem, -⟩ := branchShape_runTermTy hctx' rfl hd hi' hbt' hip' htg hvb' h
    rw [hem]; simp
  | brif c a b =>
    obtain ⟨ms, i, hem, -⟩ := branchShape_runTermTy hctx' rfl hd hi' hbt' hip' htg hvb' h
    rw [hem]; simp
  | brTable x d tbl =>
    obtain ⟨ms, i, hem, -⟩ := branchShape_runTermTy hctx' rfl hd hi' hbt' hip' htg hvb' h
    rw [hem]; simp
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCall fn args et => simp [Clif.Terminator.isTry] at ht
  | tryCallIndirect callee args et => simp [Clif.Terminator.isTry] at ht

end Backend.Proof
