module

public import FV.Backend.Proof.IselMemRoots
public import FV.Backend.Proof.IselFloatBitcast

@[expose] public section

/-!
# S11e4: `load`/`store` of `f32`/`f64` over float-capable contexts

The roots `rule_lower_2625`/`rule_lower_2628` (1047/1048, `load.f32`/`load.f64`) lower to
`ldr s/d` (`aarch64_fpuload32/64`, `MInst.fpuLoad`) through `amode`, and
`rule_lower_2746`/`rule_lower_2750` (1073/1074, `store` of an `f32`/`f64` value) to `str s/d`
(`aarch64_fpustore32/64`, `MInst.fpuStore`).

The addressing-mode contract `amode_ok` is stated over `CtxInv`, where every value is an
integer in an X register. Over `CtxInvT` only the values in integer positions are (`IntPos`,
`CtxInvT.intOps`): the address, and the operands of the `iadd`/`ishl`/`uextend`/`sextend`
instructions `amode` looks through. `amode_okT` is `amode_ok` over `CtxInvT` with the address
in an integer position; `int_posT` finds the `IntPos` facts, `mem_vregsT` uses them to turn
`ctx.valueReg? y = some r` into `r = .vreg y .int`. The VCode semantics of the FP accesses is
`MemRefinesFP`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## `CtxInvT` facts for the address computation -/

/-- The data of a value's defining instruction is `instData` of its CLIF instruction. -/
theorem def_dataT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {y j : Nat} {info : IInfo}
    (hj : ctx.defInst? y = some j) (hi : ctx.insts[j]? = some info) :
    ∃ cl, ctx.defClif? y = some cl ∧ info.clif = some cl ∧ instData f cl = .ok info.data := by
  have hs := hctx.defClif y j info hj hi
  obtain ⟨cl, hcl⟩ := Option.isSome_iff_exists.mp hs
  refine ⟨cl, ?_, hcl, hctx.data j info cl hi hcl⟩
  unfold Ctx.defClif?
  rw [hj]
  show (ctx.insts[j]? >>= fun d => d.clif) = some cl
  rw [hi]; exact hcl

theorem def_dataT' {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {y j : Nat} {info : IInfo}
    {v : V} (hj : ctx.defInst? y = some j) (hi : ctx.insts[j]? = some info) (hd : v = info.data) :
    ∃ cl, ctx.defClif? y = some cl ∧ info.clif = some cl ∧ instData f cl = .ok v := by
  subst hd; exact def_dataT hctx hj hi

/-- An integer-position operand of a value's defining instruction is in an integer position. -/
theorem CtxInvT.intPos_of_def {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {z : Nat}
    {cl : Clif.Inst} (hd : ctx.defClif? z = some cl) {y : Nat} (hy : y ∈ intArgs cl) :
    IntPos ctx y := by
  unfold Ctx.defClif? at hd
  cases hj : ctx.defInst? z with
  | none => rw [hj] at hd; cases hd
  | some j =>
    rw [hj] at hd
    cases hi : ctx.insts[j]? with
    | none =>
      have : (ctx.insts[j]? >>= fun d => d.clif) = some cl := hd
      rw [hi] at this; cases this
    | some info =>
      have : (ctx.insts[j]? >>= fun d => d.clif) = some cl := hd
      rw [hi] at this
      exact hctx.intOps j info cl hi this y hy

open Lean Elab Tactic Meta in
/-- `int_posT hctx` closes `IntPos ctx y`: by a hypothesis, or with `y` an `intArgs` operand of
a defining instruction (`ctx.defClif? z = some cl`, `CtxInvT.intPos_of_def`) or of a context
instruction (`ctx.insts[j]? = some info`, `info.clif = some cl`, `CtxInvT.intOps`). -/
elab "int_posT " hctx:ident : tactic => focus do withMainContext do
  let lctx ← getLCtx
  let mut cands : Array (TSyntax `tactic) := #[← `(tactic| assumption)]
  for d in lctx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let some (_, l, r) := t.eq? | continue
    unless r.isAppOfArity ``Option.some 2 do continue
    if l.isAppOf ``Backend.Ctx.defClif? then
      let h ← Term.exprToSyntax d.toExpr
      cands := cands.push (← `(tactic|
        exact Backend.Proof.CtxInvT.intPos_of_def $hctx $h (by simp [Backend.Proof.intArgs])))
    if l.isAppOfArity ``Backend.IInfo.clif 1 then
      let info := l.appArg!
      for d2 in lctx do
        if d2.isImplementationDetail then continue
        let t2 ← instantiateMVars d2.type
        let some (_, l2, r2) := t2.eq? | continue
        if r2.isAppOfArity ``Option.some 2 && r2.appArg! == info && l2.isAppOf ``GetElem?.getElem? then
          let hi ← Term.exprToSyntax d2.toExpr
          let hc ← Term.exprToSyntax d.toExpr
          cands := cands.push (← `(tactic|
            exact Backend.Proof.CtxInvT.intOps $hctx _ _ _ $hi $hc _ (by simp [Backend.Proof.intArgs])))
  let g ← getMainGoal
  for c in cands do
    let s ← saveState
    try
      evalTactic c
      if (← getGoals).isEmpty && !(← instantiateMVars (mkMVar g)).hasSyntheticSorry &&
          !(← instantiateMVars (mkMVar g)).hasSorry then return
      s.restore
    catch _ => s.restore
  throwError "int_posT: no integer-position fact"

open Lean Elab Tactic Meta in
/-- `mem_vregsT hctx` (`mem_vregs` over `CtxInvT`): substitute `r := .vreg y .int` for every
hypothesis `ctx.valueReg? y = some r` (`r` a local) whose `y` is in an integer position
(`int_posT`); the others stay. -/
elab "mem_vregsT " hctx:ident : tactic => do
  let mut skip : Array FVarId := #[]
  let mut progress := true
  while progress do
    progress := false
    let g ← getMainGoal
    let found ← g.withContext do
      for d in (← getLCtx) do
        if d.isImplementationDetail || skip.contains d.fvarId then continue
        let ty ← instantiateMVars d.type
        let some (_, l, r) := ty.eq? | continue
        unless l.isAppOf ``Backend.Ctx.valueReg? && r.isAppOfArity ``Option.some 2 &&
          r.appArg!.isFVar do continue
        let args := l.getAppArgs
        let posTy ← mkAppM ``Backend.Proof.IntPos #[args[0]!, args[1]!]
        let mv ← mkFreshExprSyntheticOpaqueMVar posTy
        let ok ← (do
            let gs ← Tactic.run mv.mvarId! (evalTactic (← `(tactic| int_posT $hctx)))
            pure gs.isEmpty) <|> pure false
        if ok then
          let e ← mkAppM ``Backend.Proof.CtxInvT.valueReg_int
            #[(← getLocalDeclFromUserName hctx.getId).toExpr, d.toExpr, ← instantiateMVars mv]
          return some (Sum.inl e)
        else
          return some (Sum.inr d.fvarId)
      return none
    match found with
    | some (.inl e) =>
      let g ← g.withContext do
        let g ← g.assert `hvr (← inferType e) e
        let (fv, g) ← g.intro1P
        Lean.Meta.subst g fv
      replaceMainGoal [g]
      progress := true
    | some (.inr fv) =>
      skip := skip.push fv
      progress := true
    | none => pure ()

open Lean Elab Tactic Meta in
/-- `mem_dfgT hctx`: `mem_dfg` over `CtxInvT` (`def_dataT'`). -/
elab "mem_dfgT " hctx:ident : tactic => withMainContext do
  let lctx ← getLCtx
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    unless rhs.isAppOfArity ``Backend.IInfo.data 1 && lhs.isAppOf ``Backend.V.data do continue
    let info := rhs.appArg!
    let mut hi? : Option (LocalDecl × Lean.Expr) := none
    for d2 in lctx do
      if d2.isImplementationDetail then continue
      let t2 ← instantiateMVars d2.type
      if let some (_, l2, r2) := t2.eq? then
        if r2.isAppOfArity ``Option.some 2 && r2.appArg! == info && l2.isAppOf ``GetElem?.getElem? then
          hi? := some (d2, l2.appArg!)
    let some (hi, j) := hi? | continue
    let mut hj? : Option LocalDecl := none
    for d3 in lctx do
      if d3.isImplementationDetail then continue
      let t3 ← instantiateMVars d3.type
      if let some (_, l3, r3) := t3.eq? then
        if r3.isAppOfArity ``Option.some 2 && r3.appArg! == j && l3.isAppOf ``Backend.Ctx.defInst? then
          hj? := some d3
    let some hj := hj? | continue
    let e ← mkAppM ``Backend.Proof.def_dataT' #[(← getLocalDeclFromUserName hctx.getId).toExpr,
      hj.toExpr, hi.toExpr, d.toExpr]
    let stx ← Term.exprToSyntax e
    evalTactic (← `(tactic| (
      obtain ⟨_, _, _, hdat⟩ := $stx
      first
        | have := Backend.Proof.inv_iadd hdat
        | have := Backend.Proof.inv_ishl hdat
        | have := Backend.Proof.inv_iconst hdat
        | have := Backend.Proof.inv_uextend hdat
        | have := Backend.Proof.inv_sextend hdat
        | have := Backend.Proof.inv_stackAddr hdat
      clear hdat
      isel_destruct
      subst_vars)))
    evalTactic (← `(tactic| clear $(mkIdent d.userName)))
    return
  throwError "mem_dfgT: no instruction data to invert"

/-- `mem_invdT hp hctx at h…`: `mem_invd` over `CtxInvT`. -/
macro "mem_invdT " hp:ident hctx:ident " at " h1:ident h2:ident : tactic =>
  `(tactic| ((mem_inv $hp [] at $h1 $h2); (repeat ((mem_dfgT $hctx); (repeat (mem_inv_simp [] at * <;> isel_destruct <;> subst_vars))))))

/-- `scale_log` over `CtxInvT`. -/
theorem scale_logT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {jj : Nat} {info : IInfo}
    {ty1 : Clif.Ty} {z j : Nat} {ty3 : Clif.Ty} {c3 : BitVec ty3.width} {B : Nat}
    (h : true = ((B : Int) == ((u64 (1 * 2 ^ ((((u64 ((u64 (imm64OfIconst ty3 c3) : Nat) : Int) % 256).land
      ((info.resTys.head?.getD CTy.invalid).laneBits - 1) : Nat) : Int).toNat % 64)) : Nat) : Int)))
    (hcl : info.clif = some (.binary .ishl ty1 z j)) (hij : ctx.insts[jj]? = some info)
    (he3 : eTy ty3 = true) (hb : B = 1 ∨ B = 2 ∨ B = 4 ∨ B = 8) :
    ty1 = .i64 → log2 B = c3.toNat % 64 := by
  rintro rfl
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys jj info _ hij hcl
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at h
  have hw := eTy_width he3
  rw [fb_u64_imm64 hw] at h
  exact log2_scale (Nat.lt_of_lt_of_le c3.isLt (Nat.pow_le_pow_right (by decide) hw)) hb h

section Amode
variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)
variable {F : BitVec 64 → Prop} {isem : Sem} {sb : Nat}

include hp hc in
/-- **`amode_reg_scaled base index`** over `CtxInvT`, the index in an integer position. -/
theorem amode_reg_scaled_okT {f : Clif.Function} (hctx : CtxInvT f ctx) {d y : Nat}
    (hy : IntPos ctx y) {n : Nat} (hn : 40 ≤ n) {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 89 576 [.reg (.vreg d .int), .value y] s v s') :
    s'.1 = s.1 ∧ ∃ am, v.amode? = some am ∧ ScaledOk ctx d y am := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 576
  · mem_inv hp [] at hm he
    obtain ⟨cl, hdc, -, hdat⟩ := def_dataT' hctx ‹_› ‹_› ‹_›
    obtain ⟨ty, x, rfl, rfl, -⟩ := instData_extend_inv hdat (.inl rfl)
    simp only [ext_value_type_iff, ctor_put_in_reg_iff, V.ty.injEq, List.cons.injEq, and_true] at *
    isel_destruct; subst_vars
    obtain rfl := hctx.valueReg_int ‹ctx.valueReg? x = some _›
      (hctx.intPos_of_def hdc (by simp [intArgs]))
    exact ⟨rfl, _, rfl, scaled_ext_ok (op := .uextend) rfl hdc ‹_› ‹_› (.inl rfl)⟩
  · mem_inv hp [] at hm he
    obtain ⟨cl, hdc, -, hdat⟩ := def_dataT' hctx ‹_› ‹_› ‹_›
    obtain ⟨ty, x, rfl, rfl, -⟩ := instData_extend_inv hdat (.inr rfl)
    simp only [ext_value_type_iff, ctor_put_in_reg_iff, V.ty.injEq, List.cons.injEq, and_true] at *
    isel_destruct; subst_vars
    obtain rfl := hctx.valueReg_int ‹ctx.valueReg? x = some _›
      (hctx.intPos_of_def hdc (by simp [intArgs]))
    exact ⟨rfl, _, rfl, scaled_ext_ok (op := .sextend) rfl hdc ‹_› ‹_› (.inr rfl)⟩
  · mem_inv hp [] at hm he
    obtain rfl := hctx.valueReg_int ‹ctx.valueReg? y = some _› hy
    refine ⟨_, rfl, fun r hr => ?_, y, rfl, ‹_›, ?_⟩
    · simp only [AMode.regs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, rfl⟩
    intro sb fr ρ hdfg hv yv hy' ht
    refine ⟨by rw [hy']; rfl, fun a w bytes => ?_⟩
    simp only [amodeAddr]
    rw [lo64_of_holds (hv y yv hy') ht]

set_option maxHeartbeats 4000000 in
include hp hc in
/-- **`amode_no_more_iconst ty x off`** over `CtxInvT`, the address in an integer position. -/
theorem amode_nmi_okT (hR : Refines F isem) {f : Clif.Function} (hctx : CtxInvT f ctx) {n : Nat}
    (hn : 200 ≤ n) {x : Nat} (hx : IntPos ctx x) {t : CTy} {off : Int} {st : LState}
    {tr : Array RuleId} {s' : LState × Array RuleId} {v : V} (hvb : ValsBelow ctx st)
    (hb : t.bytes = 1 ∨ t.bytes = 2 ∨ t.bytes = 4 ∨ t.bytes = 8)
    (h : ApplyInternal p (sem ctx) cfg n 89 575 [.ty t, .value x, .int off] (st, tr) v s') :
    ∃ ms am, v.amode? = some am ∧ AmOk F isem sb ctx st s'.1 ms am t.bytes x off := by
  revert hb
  mem_split hp hc h 575
  · -- 4103: non-zero scaled `uimm12`
    intro hb
    mem_invdT hp hctx at hm he
    mem_vregsT hctx
    exact ⟨[], _, rfl, amOk_nil (amVregs_int (by simp [AMode.regs])) (amVregs_one_uoff _ _)
      (uoff_sem ‹_› ‹_› ‹_›)⟩
  · -- 4096: `(ishl y c) + x`
    intro hb
    mem_invdT hp hctx at hm he
    mem_vregsT hctx
    have h577 := ‹ApplyInternal _ _ _ _ 27 577 _ _ _ _›
    have h576 := ‹ApplyInternal _ _ _ _ 89 576 _ _ _ _›
    have hlog := scale_logT hctx ‹true = _› ‹IInfo.clif _ = some (.binary .ishl _ _ _)› ‹_› ‹_› hb
    obtain ⟨d, ms, rfl, hadd⟩ := amode_add_ok hp ctx hc hR (by omega) (hvb _ _ (by assumption)) h577
    obtain ⟨hs, am, ham, hsc⟩ := amode_reg_scaled_okT hp ctx hc hctx (by int_posT hctx) (by omega) h576
    obtain ⟨y', hav, hvr', -⟩ := hsc.idx
    simp only at hs
    subst hs
    exact ⟨ms, am, ham, amOk_add hadd hsc.vregs hav (hvb _ _ hvr')
      (sem_right ‹ctx.defClif? x = some _› (idx_scaled hsc hav ‹_› ‹_› hlog))⟩
  · -- 4093: `x + (ishl y c)`
    intro hb
    mem_invdT hp hctx at hm he
    mem_vregsT hctx
    have h577 := ‹ApplyInternal _ _ _ _ 27 577 _ _ _ _›
    have h576 := ‹ApplyInternal _ _ _ _ 89 576 _ _ _ _›
    have hlog := scale_logT hctx ‹true = _› ‹IInfo.clif _ = some (.binary .ishl _ _ _)› ‹_› ‹_› hb
    obtain ⟨d, ms, rfl, hadd⟩ := amode_add_ok hp ctx hc hR (by omega) (hvb _ _ (by assumption)) h577
    obtain ⟨hs, am, ham, hsc⟩ := amode_reg_scaled_okT hp ctx hc hctx (by int_posT hctx) (by omega) h576
    obtain ⟨y', hav, hvr', -⟩ := hsc.idx
    simp only at hs
    subst hs
    exact ⟨ms, am, ham, amOk_add hadd hsc.vregs hav (hvb _ _ hvr')
      (sem_left ‹ctx.defClif? x = some _› (idx_scaled hsc hav ‹_› ‹_› hlog))⟩
  · -- 4081: `uextend x + y`
    intro hb
    mem_invdT hp hctx at hm he
    mem_vregsT hctx
    have h577 := ‹ApplyInternal _ _ _ _ 27 577 _ _ _ _›
    obtain ⟨d, ms, rfl, hadd⟩ := amode_add_ok hp ctx hc hR (by omega) (hvb _ _ (by assumption)) h577
    exact ⟨ms, _, rfl, amOk_add hadd (amVregs_int (by simp [AMode.regs])) (amVregs_ext _ _ _)
      (hvb _ _ (by assumption)) (sem_right ‹ctx.defClif? x = some _› (idx_ext (op := .uextend) rfl (.inl rfl) ‹_› ‹_›))⟩
  · -- 4083: `sextend x + y`
    intro hb
    mem_invdT hp hctx at hm he
    mem_vregsT hctx
    have h577 := ‹ApplyInternal _ _ _ _ 27 577 _ _ _ _›
    obtain ⟨d, ms, rfl, hadd⟩ := amode_add_ok hp ctx hc hR (by omega) (hvb _ _ (by assumption)) h577
    exact ⟨ms, _, rfl, amOk_add hadd (amVregs_int (by simp [AMode.regs])) (amVregs_ext _ _ _)
      (hvb _ _ (by assumption)) (sem_right ‹ctx.defClif? x = some _› (idx_ext (op := .sextend) rfl (.inr rfl) ‹_› ‹_›))⟩
  · -- 4077: `x + uextend y`
    intro hb
    mem_invdT hp hctx at hm he
    mem_vregsT hctx
    have h577 := ‹ApplyInternal _ _ _ _ 27 577 _ _ _ _›
    obtain ⟨d, ms, rfl, hadd⟩ := amode_add_ok hp ctx hc hR (by omega) (hvb _ _ (by assumption)) h577
    exact ⟨ms, _, rfl, amOk_add hadd (amVregs_int (by simp [AMode.regs])) (amVregs_ext _ _ _)
      (hvb _ _ (by assumption)) (sem_left ‹ctx.defClif? x = some _› (idx_ext (op := .uextend) rfl (.inl rfl) ‹_› ‹_›))⟩
  · -- 4079: `x + sextend y`
    intro hb
    mem_invdT hp hctx at hm he
    mem_vregsT hctx
    have h577 := ‹ApplyInternal _ _ _ _ 27 577 _ _ _ _›
    obtain ⟨d, ms, rfl, hadd⟩ := amode_add_ok hp ctx hc hR (by omega) (hvb _ _ (by assumption)) h577
    exact ⟨ms, _, rfl, amOk_add hadd (amVregs_int (by simp [AMode.regs])) (amVregs_ext _ _ _)
      (hvb _ _ (by assumption)) (sem_left ‹ctx.defClif? x = some _› (idx_ext (op := .sextend) rfl (.inr rfl) ‹_› ‹_›))⟩
  · -- 4075: `x + y`
    intro hb
    mem_invdT hp hctx at hm he
    mem_vregsT hctx
    have h577 := ‹ApplyInternal _ _ _ _ 27 577 _ _ _ _›
    obtain ⟨d, ms, rfl, hadd⟩ := amode_add_ok hp ctx hc hR (by omega) (hvb _ _ (by assumption)) h577
    exact ⟨ms, _, rfl, amOk_add hadd (amVregs_int (by simp [AMode.regs])) (amVregs_pair _ _)
      (hvb _ _ (by assumption)) (sem_left ‹_› idx_reg)⟩
  · -- 4064: scaled `uimm12`
    intro hb
    mem_invdT hp hctx at hm he
    mem_vregsT hctx
    exact ⟨[], _, rfl, amOk_nil (amVregs_int (by simp [AMode.regs])) (amVregs_one_uoff _ _)
      (uoff_sem ‹_› ‹_› ‹_›)⟩
  · -- 4061: `simm9`
    intro hb
    mem_invdT hp hctx at hm he
    mem_vregsT hctx
    exact ⟨[], _, rfl, amOk_nil (amVregs_int (by simp [AMode.regs])) (amVregs_one_unscaled _ _)
      (simm9_sem ‹_› ‹_›)⟩
  · -- 4056: `RegReg x (imm off)`
    intro hb
    mem_invdT hp hctx at hm he
    mem_vregsT hctx
    have h553 := ‹ApplyInternal _ _ _ _ 27 553 _ _ _ _›
    obtain ⟨ms, d, rfl, hsh, hrun⟩ := imm64_inv hp ctx hc hR (by omega) h553
    exact ⟨ms, _, rfl, amOk_imm (hvb x _ ‹_›) hsh fun ρ => by
      obtain ⟨ρ', X, h1, h2, h3, -⟩ := hrun ρ; exact ⟨ρ', X, h1, h2, h3⟩⟩

set_option maxHeartbeats 2000000 in
include hp hc in
/-- **`amode ty x off`** over `CtxInvT` (all four rules), the address in an integer position. -/
theorem amode_okT (hR : Refines F isem) {f : Clif.Function} (hctx : CtxInvT f ctx) {n : Nat}
    (hn : 300 ≤ n) {x : Nat} (hx : IntPos ctx x) {t : CTy} {off : Int} {st : LState}
    {tr : Array RuleId} {s' : LState × Array RuleId} {v : V} (hvb : ValsBelow ctx st)
    (hb : t.bytes = 1 ∨ t.bytes = 2 ∨ t.bytes = 4 ∨ t.bytes = 8)
    (h : ApplyInternal p (sem ctx) cfg n 89 574 [.ty t, .value x, .int off] (st, tr) v s') :
    ∃ ms am, v.amode? = some am ∧ AmOk F isem sb ctx st s'.1 ms am t.bytes x off := by
  revert hb
  mem_split hp hc h 574
  · -- 4047: `stack_addr`
    intro hb
    mem_invdT hp hctx at hm he
    repeat (simp only [ctor_i32_to_offset32', ctor_abi_stackslot_offset_iff, ctor_i32_into_i64']
      at * <;> isel_destruct <;> subst_vars)
    exact ⟨[], _, rfl, amOk_slot ‹_› ‹_›⟩
  · -- 4043: `iadd (iconst c) y`
    intro hb
    mem_invdT hp hctx at hm he
    have h575 := ‹ApplyInternal _ _ _ _ 89 575 _ _ _ _›
    obtain ⟨ms, am, ham, hok⟩ :=
      amode_nmi_okT hp ctx hc hR hctx (by omega) (by int_posT hctx) hvb hb h575
    exact ⟨ms, am, ham, amOk_rebase hok (fold_val true ‹_› ‹_›)⟩
  · -- 4040: `iadd x (iconst c)`
    intro hb
    mem_invdT hp hctx at hm he
    have h575 := ‹ApplyInternal _ _ _ _ 89 575 _ _ _ _›
    obtain ⟨ms, am, ham, hok⟩ :=
      amode_nmi_okT hp ctx hc hR hctx (by omega) (by int_posT hctx) hvb hb h575
    exact ⟨ms, am, ham, amOk_rebase hok (fold_val false ‹_› ‹_›)⟩
  · -- 4038: `amode_no_more_iconst`
    intro hb
    mem_invdT hp hctx at hm he
    have h575 := ‹ApplyInternal _ _ _ _ 89 575 _ _ _ _›
    exact amode_nmi_okT hp ctx hc hR hctx (by omega) hx hvb hb h575

end Amode

/-! ## The FP access instructions -/

theorem ofV_fpuLoad32' (rd : Reg) (amv : V) (fl : Clif.MemFlags) :
    MInst.ofV (.data 58 59 [.reg rd, amv, .op (.memFlags fl)]) =
      amv.amode?.bind fun am => some (.fpuLoad .size32 rd am fl) := rfl
theorem ofV_fpuLoad64' (rd : Reg) (amv : V) (fl : Clif.MemFlags) :
    MInst.ofV (.data 58 61 [.reg rd, amv, .op (.memFlags fl)]) =
      amv.amode?.bind fun am => some (.fpuLoad .size64 rd am fl) := rfl
theorem ofV_fpuStore32' (rd : Reg) (amv : V) (fl : Clif.MemFlags) :
    MInst.ofV (.data 58 60 [.reg rd, amv, .op (.memFlags fl)]) =
      amv.amode?.bind fun am => some (.fpuStore .size32 rd am fl) := rfl
theorem ofV_fpuStore64' (rd : Reg) (amv : V) (fl : Clif.MemFlags) :
    MInst.ofV (.data 58 62 [.reg rd, amv, .op (.memFlags fl)]) =
      amv.amode?.bind fun am => some (.fpuStore .size64 rd am fl) := rfl

/-- Operand view of `ldr s/d` into float vreg `d`. -/
theorem fpuLoad_ops (sz : ScalarSize) (d : Nat) {am : AMode} (h : AmVregs am) (fl : Clif.MemFlags) :
    DefAmOps (.fpuLoad sz (.vreg d .float) am fl) d am := by
  rcases am_operands_cases h with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, e, rfl⟩ | ⟨a, b, e, rfl⟩ |
    ⟨a, i, rfl⟩ | ⟨a, i, rfl⟩ | ⟨a, i, rfl⟩ | hnil
  all_goals first
    | exact ⟨⟨_, rfl, fun ρ => rfl, rfl, fun ρ x => rfl⟩, rfl, rfl⟩
    | (cases am <;> simp [AMode.regs] at hnil <;>
        exact ⟨⟨_, rfl, fun ρ => rfl, rfl, fun ρ x => rfl⟩, rfl, rfl⟩)

/-- Operand view of `str s/d` of float vreg `v`. -/
theorem fpuStore_ops (sz : ScalarSize) (v : Nat) {am : AMode} (h : AmVregs am) (fl : Clif.MemFlags) :
    StoreAmOps (.fpuStore sz (.vreg v .float) am fl) v am := by
  rcases am_operands_cases h with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, e, rfl⟩ | ⟨a, b, e, rfl⟩ |
    ⟨a, i, rfl⟩ | ⟨a, i, rfl⟩ | ⟨a, i, rfl⟩ | hnil
  all_goals first
    | exact ⟨⟨_, rfl, fun ρ => rfl, rfl, fun ρ => rfl⟩, rfl, rfl⟩
    | (cases am <;> simp [AMode.regs] at hnil <;>
        exact ⟨⟨_, rfl, fun ρ => rfl, rfl, fun ρ => rfl⟩, rfl, rfl⟩)

theorem fresh_fst_f (st : LState) : (st.fresh .float).1 = .vreg st.nextVreg .float := by
  simp [LState.fresh]

theorem frag_one_f (st : LState) (m : MInst) (hd : vdefs m = [st.nextVreg]) :
    Frag st ((st.fresh .float).2.emit m) [m] := by
  refine ⟨?_, ?_, ?_⟩
  · show st.emitted.push m = _
    rw [Array.push_eq_append]
  · simp [LState.emit, LState.fresh]
  intro m' hm d hd'
  simp only [List.mem_singleton] at hm; subst hm
  rw [hd] at hd'; simp at hd'; subst hd'; simp [LState.emit, LState.fresh]

section Helpers
variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

include hp hc in
/-- **`aarch64_fpuload32`**: a fresh float destination and `ldr s`. -/
theorem fpuload32_helper_ok {n : Nat} (hn : 40 ≤ n) {amv flv : V} {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 27 537 [amv, flv] s v s') :
    ∃ m, MInst.ofV (.data 58 59 [.reg (s.1.fresh .float).1, amv, flv]) = some m ∧
      v = .reg (s.1.fresh .float).1 ∧ s'.1 = (s.1.fresh .float).2.emit m := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 537
  mem_inv hp [ctor_temp_writable_reg_f64_iff] at hm he
  first | exact ⟨_, ‹_›, rfl, rfl⟩ | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›⟩

include hp hc in
/-- **`aarch64_fpuload64`**: a fresh float destination and `ldr d`. -/
theorem fpuload64_helper_ok {n : Nat} (hn : 40 ≤ n) {amv flv : V} {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 27 538 [amv, flv] s v s') :
    ∃ m, MInst.ofV (.data 58 61 [.reg (s.1.fresh .float).1, amv, flv]) = some m ∧
      v = .reg (s.1.fresh .float).1 ∧ s'.1 = (s.1.fresh .float).2.emit m := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 538
  mem_inv hp [ctor_temp_writable_reg_f64_iff] at hm he
  first | exact ⟨_, ‹_›, rfl, rfl⟩ | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›⟩

include hp hc in
/-- **`aarch64_fpustore32`**: `str s` as a side effect. -/
theorem fpustore32_helper_ok {n : Nat} (hn : 40 ≤ n) {amv flv r : V} {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 46 546 [amv, flv, r] s v s') :
    v = .data 46 0 [.data 58 60 [r, amv, flv]] ∧ s'.1 = s.1 := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 546
  mem_inv hp [] at hm he

include hp hc in
/-- **`aarch64_fpustore64`**: `str d` as a side effect. -/
theorem fpustore64_helper_ok {n : Nat} (hn : 40 ≤ n) {amv flv r : V} {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 46 547 [amv, flv, r] s v s') :
    v = .data 46 0 [.data 58 62 [r, amv, flv]] ∧ s'.1 = s.1 := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 547
  mem_inv hp [] at hm he

end Helpers

/-! ## `LowerInstOkR` of the FP accesses -/

theorem rtOk_ofT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {F : BitVec 64 → Prop}
    {sb : Nat} {syms : String → Option Nat} {MR : MemRelT} (hMRo : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState} (hf : fr.func = ctx.func)
    (hv : ValsHeld fr ρ) (hdfg : DFGCons ctx fr) (hmr : MR fr.slots cm w) :
    RtOk ctx sb fr ρ w := by
  refine ⟨hf, hv, hdfg, fun id b hb => ?_⟩
  obtain ⟨off, ho, hb'⟩ := hMRo.slots _ _ _ id b hmr hb
  exact ⟨off, by rw [hctx.slotOff]; exact ho, hb'⟩

/-- The float access sizes: `ldr/str s` for `f32`, `ldr/str d` for `f64`. -/
def FSz (sz : ScalarSize) (ty : Clif.Ty) : Prop :=
  (sz = .size32 ∧ ty = .f32) ∨ (sz = .size64 ∧ ty = .f64)

theorem FSz.bytes {sz : ScalarSize} {ty : Clif.Ty} (h : FSz sz ty) : sz.bytes = ty.bytes := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem FSz.sz {sz : ScalarSize} {ty : Clif.Ty} (h : FSz sz ty) : sz = .size32 ∨ sz = .size64 := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact .inl rfl
  · exact .inr rfl

theorem FSz.width {sz : ScalarSize} {ty : Clif.Ty} (h : FSz sz ty) : ty.bytes * 8 = ty.width := by
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl

/-- The register an FP load leaves holds the CLIF load's value. -/
theorem fload_holds {ty : Clif.Ty} {n : Nat} (hw : ty.width ≤ 64)
    {raw : BitVec (8 * n)} {R : BitVec (n * 8)} (hbits : ∀ j, raw.getLsbD j = R.getLsbD j) :
    VHolds ⟨ty, raw.zeroExtend ty.width⟩ (R.setWidth 128) := by
  simp only [VHolds]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.zeroExtend_eq_setWidth, hbits]
  have : i < 128 := by omega
  simp [hi, this]

section Builders
variable {Rd : BitVec 64 → Prop} {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
  {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} {f : Clif.Function} {ctx : Ctx}

/-- **An FP load through an addressing mode** (`AmOk`): the mode's code, then `ldr s/d` into a
fresh float register. -/
theorem fpu_load_lower_ok (hMR : MRStable F MR) (hFP : MemRefinesFP Rd F sb isem)
    (hctx : CtxInvT f ctx) (hMRo : MemRelOk F sb syms f MR) {st st2 : LState} {ms : List MInst}
    {am : AMode} {sz : ScalarSize} {ty : Clif.Ty} {fl : Clif.MemFlags} {p : Nat}
    {off : Int} {results : List Nat}
    (hok : AmOk F isem sb ctx st st2 ms am sz.bytes p off) (hsz : FSz sz ty)
    (hfl : fl.endianness ≠ some .big) (hp64 : ctx.valueType? p = some (.int 64)) :
    LowerInstOkR Rd isem MR env cp ctx (.load .load ty fl p off) results st [[(st2.fresh .float).1]]
      ((st2.fresh .float).2.emit (.fpuLoad sz (st2.fresh .float).1 am fl))
      (ms ++ [.fpuLoad sz (st2.fresh .float).1 am fl]) := by
  rw [fresh_fst_f]
  have hops := fpuLoad_ops sz st2.nextVreg hok.vregs fl
  have hfr := hok.frag.append (frag_one_f st2 _ hops.defs)
  refine ⟨hfr.mono, hfr.defs, ?_⟩
  intro fr cm ρ w hf hv hdfg hmr hRd
  rw [instOutcome_load]
  cases he : Clif.evalInst fr cm (.load .load ty fl p off) with
  | trap c => intro h; simp [explicitTrapInst] at h
  | stuck _ => trivial
  | ok r =>
  obtain ⟨vals, cm'⟩ := r
  obtain ⟨pv, raw, hpv, hle, hvalid, hread, rfl, rfl⟩ := evalInst_load_inv hfl he
  dsimp only
  have hrt := rtOk_ofT hctx hMRo hf hv hdfg hmr
  obtain ⟨hU, hAv, ρ1, w1, hr1, hw1, haddr⟩ := hok.run fr ρ w pv hrt hpv (pv_i64 hdfg hp64 hpv)
  have hmr1 := hMR _ _ _ _ hw1 hmr
  rw [effAddr_ofInt] at haddr
  generalize Clif.effAddr pv off = A at haddr hvalid hread
  have hbt : sz.bytes = Clif.LoadOp.size ty .load := by rw [hsz.bytes]; rfl
  obtain ⟨hA64, hF⟩ := hMRo.valid _ _ _ _ _ hmr1 hvalid
  have havoid : Avoids F sz.bytes (BitVec.ofNat 64 A) := by
    intro k hk
    rw [← BitVec.ofNat_add]
    exact hF k (by omega)
  have hrd : ∀ k < sz.bytes, Rd (BitVec.ofNat 64 A + BitVec.ofNat 64 k) := by
    intro k hk
    rw [← BitVec.ofNat_add]
    have hk' : k < Clif.LoadOp.size ty .load := by rw [← hbt]; exact hk
    exact hRd _ (valid_sub hvalid hk') ((readBits_spec hread).1 k hk')
  obtain ⟨w2, hs, hsw⟩ := hFP.1 sz st2.nextVreg am fl _ w1 _ hsz.sz haddr havoid hrd
  obtain ⟨ops, hopsE, hvu, hlen, hupd⟩ := hops.ops
  rw [← hvu] at hs
  have hr2 := seqRun_isem_one hopsE hs (by rw [hlen]; rfl)
  refine ⟨?_, _, w2, seqRun_append_fall' isem hr1 hr2, .inr ⟨rfl, ?_⟩,
    hMR _ _ _ _ hsw.toNF hmr1⟩
  · refine UsesLo.append hU fun m hm u hu => ?_
    simp only [List.mem_singleton] at hm; subst hm
    rw [hops.uses] at hu
    exact hAv u hu
  · intro j rs v hrs hv'
    cases j with
    | succ j => simp at hrs
    | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hrs hv'
    subst hrs hv'
    refine ⟨st2.nextVreg, .float, rfl, .inl hok.frag.mono, ?_⟩
    rw [hupd, upd_same]
    have hbits := readBits_getLsbD_eq (s := w1) hread (by omega)
      (fun i hi b hb => hMRo.bytes _ _ _ _ b hmr1 (valid_sub hvalid hi) hb)
    simp only [Clif.LoadOp.signed, Bool.false_eq_true, ↓reduceIte]
    rw [hbt]
    exact fload_holds (by rcases hsz with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide) hbits

/-- **An FP store through an addressing mode** (`AmOk`): the mode's code, then `str s/d` of the
value's float register. -/
theorem fpu_store_lower_ok (hMR : MRStable F MR) (hFP : MemRefinesFP Rd F sb isem)
    (hctx : CtxInvT f ctx) (hMRo : MemRelOk F sb syms f MR) {st st2 : LState} {ms : List MInst}
    {am : AMode} {sz : ScalarSize} {ty : Clif.Ty} {fl : Clif.MemFlags}
    {x p : Nat} {off : Int} {results : List Nat}
    (hok : AmOk F isem sb ctx st st2 ms am sz.bytes p off)
    (hsz : ∀ (fr : Clif.Frame) (a : BitVec ty.width), DFGCons ctx fr → fr.getAs x ty = .ok a →
      FSz sz ty)
    (hfl : fl.endianness ≠ some .big) (hp64 : ctx.valueType? p = some (.int 64))
    (hx : x < st.nextVreg) :
    LowerInstOk isem MR env cp ctx (.store .store ty fl x p off) results st []
      (st2.emit (.fpuStore sz (.vreg x .float) am fl)) (ms ++ [.fpuStore sz (.vreg x .float) am fl]) := by
  have hops := fpuStore_ops sz x hok.vregs fl
  have hfr := hok.frag.append (frag_emit0 st2 _ hops.defs)
  refine ⟨hfr.mono, hfr.defs, ?_⟩
  intro fr cm ρ w hf hv hdfg hmr
  rw [instOutcome_store]
  cases he : Clif.evalInst fr cm (.store .store ty fl x p off) with
  | trap c => intro h; simp [explicitTrapInst] at h
  | stuck _ => trivial
  | ok r =>
  obtain ⟨vals, cm'⟩ := r
  obtain ⟨a, pv, hax, hpv, hle, hvalid, rfl, rfl⟩ := evalInst_store_inv hfl he
  dsimp only
  have hsz := hsz fr a hdfg hax
  have hbt : sz.bytes = Clif.StoreOp.size ty .store := by rw [hsz.bytes]; rfl
  have hrt := rtOk_ofT hctx hMRo hf hv hdfg hmr
  obtain ⟨hU, hAv, ρ1, w1, hr1, hw1, haddr⟩ := hok.run fr ρ w pv hrt hpv (pv_i64 hdfg hp64 hpv)
  have hmr1 := hMR _ _ _ _ hw1 hmr
  rw [effAddr_ofInt] at haddr
  generalize Clif.effAddr pv off = A at haddr hvalid
  rw [← hbt] at hvalid hle ⊢
  obtain ⟨hA64, hF⟩ := hMRo.valid _ _ _ _ _ hmr1 hvalid
  have havoid : Avoids F sz.bytes (BitVec.ofNat 64 A) := by
    intro k hk
    rw [← BitVec.ofNat_add]
    exact hF k (by omega)
  obtain ⟨w2, hs, hsw⟩ := hFP.2 sz x am fl (ρ1 x) _ w1 _ hsz.sz haddr havoid
  obtain ⟨ops, hopsE, hvu, hlen, hupd⟩ := hops.ops
  rw [← hvu] at hs
  have hr2 := seqRun_isem_one hopsE hs (by rw [hlen]; rfl)
  have hxv := getAs_ok hax
  have hx1 : ρ1 x = ρ x := hok.frag.frame hr1 hx
  have hle8 : sz.bytes * 8 = ty.width := by rw [hsz.bytes]; exact hsz.width
  refine ⟨?_, _, w2, seqRun_append_fall' isem hr1 hr2, .inr ⟨rfl, fun j rs v h => by simp at h⟩, ?_⟩
  · refine UsesLo.append hU fun m hm u hu => ?_
    simp only [List.mem_singleton] at hm; subst hm
    rw [hops.uses] at hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact .inr (by rw [hxv]; rfl)
    · exact hAv u hu
  · refine hMR _ _ _ _ hsw.toNF ?_
    have hval : a.setWidth (sz.bytes * 8) = (ρ1 x).setWidth (sz.bytes * 8) := by
      rw [hx1]
      have hh : (ρ x).setWidth ty.width = a := hv x _ hxv
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth]
      rw [← hh, BitVec.toNat_setWidth, hle8, Nat.mod_mod]
    rw [writeBits_setWidth A sz.bytes a (by omega), hval]
    exact hMRo.store _ _ _ _ _ _ hmr1 hvalid

end Builders

/-! ## The four roots -/

/-- `mem_rootT hctx hi hic`: `mem_root` over `CtxInvT` (`hIP`: the instruction's integer
positions). -/
macro "mem_rootT " hctx:ident hi:ident hic:ident : tactic => `(tactic| (
  have hdat0 := CtxInvT.data $hctx _ _ _ $hi $hic
  have $(Lean.mkIdent `hA64) := fun x => CtxInvT.addr64 $hctx _ _ _ x $hi $hic
  have $(Lean.mkIdent `hRT) := CtxInvT.resTys $hctx _ _ _ $hi $hic
  have $(Lean.mkIdent `hIP) := CtxInvT.intOps $hctx _ _ _ $hi $hic
  simp only [$hi:ident, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hdat := data_trans hdat0 ‹_›
  first
    | have := inv_load_root hdat
    | have := inv_store_root hdat
  isel_destruct; subst_vars
  repeat (mem_inv_simp [] at * <;> isel_destruct <;> subst_vars)))

/-- A value whose type is a float is in a float register. -/
theorem CtxInvT.valueReg_float {f : Clif.Function} {ctx : Ctx} (h : CtxInvT f ctx) {x w : Nat}
    {r : Reg} (ht : ctx.valueType? x = some (.float w)) (hr : ctx.valueReg? x = some r) :
    r = .vreg x .float := by
  rw [h.typedReg x _ ht] at hr
  cases hr
  rfl

/-- `store` of an `f32`/`f64` value `x`: the store's type is `x`'s. -/
theorem cond_fstore {ctx : Ctx} {x w : Nat} {ty : Clif.Ty} {sz : ScalarSize}
    (hvt : ctx.valueType? x = some (.float w)) (hw : (w = 32 ∧ sz = .size32) ∨ (w = 64 ∧ sz = .size64)) :
    ∀ (fr : Clif.Frame) (a : BitVec ty.width), DFGCons ctx fr → fr.getAs x ty = .ok a → FSz sz ty := by
  intro fr a hd hax
  have h : CTy.ofClif ty = .float w := hd.2 x _ _ hvt (getAs_ok hax)
  rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .inl ⟨rfl, by cases ty <;> simp_all [CTy.ofClif]⟩
  · exact .inr ⟨rfl, by cases ty <;> simp_all [CTy.ofClif]⟩

section Ext
variable (ctx : Ctx) (st : LState)

theorem ext_ty_32_iff (ty : CTy) (fs : List V) :
    externExtract ctx T.ty_32 (.ty ty) st = .ok fs ↔ (ty.bits == 32) = true ∧ fs = [.ty ty] := by
  have : externExtract ctx T.ty_32 (.ty ty) st =
    if (ty.bits == 32) = true then .ok [.ty ty] else .fail := rfl
  rw [this]; clear this
  split
  · rename_i h; simp only [h, ExtResult.ok.injEq, true_and]; exact eq_comm
  · rename_i h; simp only [h, reduceCtorEq, false_iff, not_and, Bool.false_eq_true]; intro h'; exact h'.elim

theorem ext_ty_64_iff (ty : CTy) (fs : List V) :
    externExtract ctx T.ty_64 (.ty ty) st = .ok fs ↔ (ty.bits == 64) = true ∧ fs = [.ty ty] := by
  have : externExtract ctx T.ty_64 (.ty ty) st =
    if (ty.bits == 64) = true then .ok [.ty ty] else .fail := rfl
  rw [this]; clear this
  split
  · rename_i h; simp only [h, ExtResult.ok.injEq, true_and]; exact eq_comm
  · rename_i h; simp only [h, reduceCtorEq, false_iff, not_and, Bool.false_eq_true]; intro h'; exact h'.elim

end Ext

/-- A float-or-vector type of `w` bits among the value types (`f32`/`f64`, `valTyOk`). -/
theorem fty_of_bits {ty : Clif.Ty} {w : Nat} {sz : ScalarSize}
    (hsz : (w = 32 ∧ sz = .size32) ∨ (w = 64 ∧ sz = .size64)) (hv : valTyOk ty = true)
    (h1 : ((CTy.ofClif ty).isFloat || (CTy.ofClif ty).isVector) = true)
    (h2 : ((CTy.ofClif ty).bits == w) = true) : FSz sz ty := by
  rcases hsz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases ty <;>
    simp_all [valTyOk, CTy.ofClif, CTy.isFloat, CTy.isVector, CTy.bits, FSz]

/-- The access size of a float `load` whose result type matched `ty_float_or_vec` and `ty_w`. -/
theorem fsz_of_res {g sd : Nat → Option Clif.Signature} {ty : Clif.Ty} {fl : Clif.MemFlags}
    {x : Nat} {off : Int} {info : IInfo} {tys : List Clif.Ty} {w : Nat} {sz : ScalarSize}
    (hsz : (w = 32 ∧ sz = .size32) ∨ (w = 64 ∧ sz = .size64))
    (h1 : ((info.resTys.head?.getD .invalid).isFloat || (info.resTys.head?.getD .invalid).isVector) = true)
    (h2 : ((info.resTys.head?.getD .invalid).bits == w) = true)
    (h3 : info.resTys = tys.map CTy.ofClif)
    (h4 : Clif.Inst.resultTypes g sd (.load .load ty fl x off) = some tys)
    (hv : valTyOk ty = true) : FSz sz ty := by
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at h4
  subst h4
  rw [h3] at h1 h2
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some] at h1 h2
  exact fty_of_bits hsz hv h1 h2

/-- A `store`'s address is in an integer position. -/
theorem addr_mem_intArgs_store (op : Clif.StoreOp) (ty : Clif.Ty) (fl : Clif.MemFlags) (x y : Nat)
    (off : Int) : y ∈ intArgs (.store op ty fl x y off) := by
  simp only [intArgs]; split <;> simp

/-- A value type that matched `ty_float_or_vec` and `ty_w` is `f32`/`f64`. -/
theorem fvt_of_bits {t : CTy} {w : Nat} (hm : t ∈ mCTys) (h1 : (t.isFloat || t.isVector) = true)
    (h2 : (t.bits == w) = true) : t = .float w := by
  rcases mCTys_cases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [CTy.isFloat, CTy.isVector, CTy.bits]

section Roots
variable {p : Program} (hp : Data p) {Rd : BitVec 64 → Prop} {F : BitVec 64 → Prop} {sb : Nat}
  {syms : String → Option Nat} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}

include hp in
theorem fload_root_finish (hR : Refines F isem) (hMR : MRStable F MR)
    (hFP : MemRefinesFP Rd F sb isem) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (hMRo : MemRelOk F sb syms f MR) {cfg : Config} (hc : cfg.checkOverlap = false) {n1 n2 : Nat}
    (hn1 : 300 ≤ n1) (hn2 : 20 ≤ n2) {st st' : LState} {tr tr' : Array RuleId}
    (hvb : ValsBelow ctx st) {ty : Clif.Ty} {fl : Clif.MemFlags} {x : Nat} {off : Int}
    {results : List Nat} (hfl : fl.endianness ≠ some .big)
    (hp64 : ctx.valueType? x = some (.int 64)) (hx : IntPos ctx x) {t : CTy} {sz : ScalarSize}
    {kidx : Nat} (htb : t.bytes = sz.bytes) (hsz : FSz sz ty)
    (hofV : ∀ rd amv am, amv.amode? = some am →
      MInst.ofV (.data 58 kidx [.reg rd, amv, .op (.memFlags fl)]) = some (.fpuLoad sz rd am fl))
    {amv rv out : V} {s2 s3 : LState × Array RuleId}
    (hA : ApplyInternal p (sem ctx) cfg n1 89 574 [.ty t, .value x, .int off] (st, tr) amv s2)
    (hH : ∃ m, MInst.ofV (.data 58 kidx [.reg (s2.1.fresh .float).1, amv, .op (.memFlags fl)]) = some m ∧
      rv = .reg (s2.1.fresh .float).1 ∧ s3.1 = (s2.1.fresh .float).2.emit m)
    (hO : ApplyInternal p (sem ctx) cfg n2 25 172 [rv] s3 out (st', tr')) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧ ∃ rss, out = .regsVec rss ∧
      LowerInstOkR Rd isem MR env cp ctx (.load .load ty fl x off) results st rss st' ms := by
  have hb : t.bytes = 1 ∨ t.bytes = 2 ∨ t.bytes = 4 ∨ t.bytes = 8 := by
    rw [htb]; rcases hsz.sz with rfl | rfl
    · exact .inr (.inr (.inl rfl))
    · exact .inr (.inr (.inr rfl))
  obtain ⟨ms, am, ham, hok⟩ := amode_okT hp ctx hc hR hctx hn1 hx hvb hb hA (sb := sb)
  obtain ⟨mi, hmi, rfl, hs3⟩ := hH
  rw [hofV _ _ _ ham, Option.some.injEq] at hmi
  subst hmi
  obtain ⟨rfl, hs'⟩ := output_reg_inv hp ctx hc hn2 hO
  simp only at hs'
  rw [hs3] at hs'
  subst hs'
  rw [htb] at hok
  have hL := fpu_load_lower_ok (env := env) (cp := cp) (results := results) hMR hFP hctx hMRo hok
    hsz hfl hp64
  refine ⟨_, ?_, _, rfl, hL⟩
  have hfr := hok.frag.append (frag_one_f s2.1 _ (fpuLoad_ops sz s2.1.nextVreg hok.vregs fl).defs)
  rw [fresh_fst_f]
  exact hfr.emitted

include hp in
theorem fstore_root_finish (hR : Refines F isem) (hMR : MRStable F MR)
    (hFP : MemRefinesFP Rd F sb isem) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (hMRo : MemRelOk F sb syms f MR) {cfg : Config} (hc : cfg.checkOverlap = false) {n1 n3 : Nat}
    (hn1 : 300 ≤ n1) (hn3 : 60 ≤ n3) {st st' : LState} {tr tr' : Array RuleId}
    (hvb : ValsBelow ctx st) {ty : Clif.Ty} {fl : Clif.MemFlags} {x y : Nat} {off : Int}
    {results : List Nat} (hfl : fl.endianness ≠ some .big)
    (hp64 : ctx.valueType? y = some (.int 64)) (hy : IntPos ctx y)
    (hxr : ctx.valueReg? x = some (.vreg x .float)) {t : CTy} {sz : ScalarSize} {kidx : Nat}
    (htb : t.bytes = sz.bytes) (hsz32 : sz = .size32 ∨ sz = .size64)
    (hsz : ∀ (fr : Clif.Frame) (a : BitVec ty.width), DFGCons ctx fr → fr.getAs x ty = .ok a →
      FSz sz ty)
    (hofV : ∀ rd amv am, amv.amode? = some am →
      MInst.ofV (.data 58 kidx [.reg rd, amv, .op (.memFlags fl)]) = some (.fpuStore sz rd am fl))
    {amv sv out : V} {s2 s4 : LState × Array RuleId}
    (hA : ApplyInternal p (sem ctx) cfg n1 89 574 [.ty t, .value y, .int off] (st, tr) amv s2)
    (hH : sv = .data 46 0 [.data 58 kidx [.reg (.vreg x .float), amv, .op (.memFlags fl)]] ∧
      s4.1 = s2.1)
    (hS : ApplyInternal p (sem ctx) cfg n3 25 243 [sv] s4 out (st', tr')) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧ ∃ rss, out = .regsVec rss ∧
      LowerInstOkR Rd isem MR env cp ctx (.store .store ty fl x y off) results st rss st' ms := by
  have hb : t.bytes = 1 ∨ t.bytes = 2 ∨ t.bytes = 4 ∨ t.bytes = 8 := by
    rw [htb]; rcases hsz32 with rfl | rfl
    · exact .inr (.inr (.inl rfl))
    · exact .inr (.inr (.inr rfl))
  obtain ⟨ms, am, ham, hok⟩ := amode_okT hp ctx hc hR hctx hn1 hy hvb hb hA (sb := sb)
  obtain ⟨rfl, hs4⟩ := hH
  obtain ⟨mi, hmi, hs', rfl⟩ := side_effect_inst_ok hp hc (ctx := ctx) hn3 hS
  rw [hofV _ _ _ ham, Option.some.injEq] at hmi
  subst hmi
  simp only at hs'
  rw [hs4] at hs'
  subst hs'
  rw [htb] at hok
  have hL := fpu_store_lower_ok (env := env) (cp := cp) (results := results) hMR hFP hctx hMRo hok
    hsz hfl hp64 (hvb x _ hxr)
  refine ⟨_, ?_, _, rfl, hL.toR⟩
  exact (hok.frag.append (frag_emit0 s2.1 _ (fpuStore_ops sz x hok.vregs fl).defs)).emitted

set_option maxHeartbeats 4000000 in
include hp in
/-- **`load.f32`** (`rule_lower_2625`, `lower.isle:2625`): `ldr s` through `amode`. -/
theorem load_f32_okT (hR : Refines F isem) (hMR : MRStable F MR)
    (hFP : MemRefinesFP Rd F sb isem) : MemRuleOkRT Rd F sb syms isem MR env cp p rule_lower_2625 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [ext_ty_float_or_vec_iff] at hmatch heval
  mem_rootT hctx hi hic
  obtain rfl := load_op_of (k := 29) (cop := .load) rfl (by assumption)
  have h32 := ((ext_ty_32_iff ctx _ _ _).mp ‹externExtract ctx T.ty_32 _ _ = _›).1
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 537 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact fload_root_finish hp hR hMR hFP hctx hMRo hco (by omega) (by omega) hvb ‹_› (hA64 _ rfl)
    (hIP _ (by simp [intArgs])) (t := .float 32) (sz := .size32) rfl
    (fsz_of_res (.inl ⟨rfl, rfl⟩) ‹_› h32 ‹_› ‹_› ‹_›)
    (fun rd amv am h => by rw [ofV_fpuLoad32', h]; rfl) hA (fpuload32_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 4000000 in
include hp in
/-- **`load.f64`** (`rule_lower_2628`, `lower.isle:2628`): `ldr d` through `amode`. -/
theorem load_f64_okT (hR : Refines F isem) (hMR : MRStable F MR)
    (hFP : MemRefinesFP Rd F sb isem) : MemRuleOkRT Rd F sb syms isem MR env cp p rule_lower_2628 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [ext_ty_float_or_vec_iff] at hmatch heval
  mem_rootT hctx hi hic
  obtain rfl := load_op_of (k := 29) (cop := .load) rfl (by assumption)
  have h64 := ((ext_ty_64_iff ctx _ _ _).mp ‹externExtract ctx T.ty_64 _ _ = _›).1
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 27 538 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  exact fload_root_finish hp hR hMR hFP hctx hMRo hco (by omega) (by omega) hvb ‹_› (hA64 _ rfl)
    (hIP _ (by simp [intArgs])) (t := .float 64) (sz := .size64) rfl
    (fsz_of_res (.inr ⟨rfl, rfl⟩) ‹_› h64 ‹_› ‹_› ‹_›)
    (fun rd amv am h => by rw [ofV_fpuLoad64', h]; rfl) hA (fpuload64_helper_ok hp ctx hco (by omega) hH) hO

set_option maxHeartbeats 4000000 in
include hp in
/-- **`store` of an `f32`** (`rule_lower_2746`, `lower.isle:2746`): `str s` through `amode`. -/
theorem store_f32_okT (hR : Refines F isem) (hMR : MRStable F MR)
    (hFP : MemRefinesFP Rd F sb isem) : MemRuleOkRT Rd F sb syms isem MR env cp p rule_lower_2746 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [ext_ty_float_or_vec_iff] at hmatch heval
  mem_rootT hctx hi hic
  obtain rfl := store_op_of (k := 30) (cop := .store) rfl (by assumption)
  obtain ⟨hfv, hfs⟩ := (ext_ty_float_or_vec_iff ctx _ _ _).mp
    ‹externExtract ctx T.ty_float_or_vec _ _ = _›
  simp only [List.cons.injEq, and_true] at hfs
  subst hfs
  have h32 := ((ext_ty_32_iff ctx _ _ _).mp ‹externExtract ctx T.ty_32 _ _ = _›).1
  obtain ⟨hvt⟩ : Nonempty (ctx.valueType? _ = some _) := ⟨‹_›⟩
  obtain rfl := fvt_of_bits (hctx.valTyM _ _ hvt) hfv h32
  obtain rfl := hctx.valueReg_float hvt ‹ctx.valueReg? _ = some _›
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 46 546 _ _ _ _›
  have hS := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  exact fstore_root_finish hp hR hMR hFP hctx hMRo hco (by omega) (by omega) hvb ‹_› (hA64 _ rfl)
    (hIP _ (addr_mem_intArgs_store ..)) ‹_› (t := .float 32) (sz := .size32) rfl (.inl rfl)
    (cond_fstore hvt (.inl ⟨rfl, rfl⟩))
    (fun rd amv am h => by rw [ofV_fpuStore32', h]; rfl) hA (fpustore32_helper_ok hp ctx hco (by omega) hH) hS

set_option maxHeartbeats 4000000 in
include hp in
/-- **`store` of an `f64`** (`rule_lower_2750`, `lower.isle:2750`): `str d` through `amode`. -/
theorem store_f64_okT (hR : Refines F isem) (hMR : MRStable F MR)
    (hFP : MemRefinesFP Rd F sb isem) : MemRuleOkRT Rd F sb syms isem MR env cp p rule_lower_2750 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [ext_ty_float_or_vec_iff] at hmatch heval
  mem_rootT hctx hi hic
  obtain rfl := store_op_of (k := 30) (cop := .store) rfl (by assumption)
  obtain ⟨hfv, hfs⟩ := (ext_ty_float_or_vec_iff ctx _ _ _).mp
    ‹externExtract ctx T.ty_float_or_vec _ _ = _›
  simp only [List.cons.injEq, and_true] at hfs
  subst hfs
  have h64 := ((ext_ty_64_iff ctx _ _ _).mp ‹externExtract ctx T.ty_64 _ _ = _›).1
  obtain ⟨hvt⟩ : Nonempty (ctx.valueType? _ = some _) := ⟨‹_›⟩
  obtain rfl := fvt_of_bits (hctx.valTyM _ _ hvt) hfv h64
  obtain rfl := hctx.valueReg_float hvt ‹ctx.valueReg? _ = some _›
  have hA := ‹ApplyInternal _ _ _ _ 89 574 _ _ _ _›
  have hH := ‹ApplyInternal _ _ _ _ 46 547 _ _ _ _›
  have hS := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  exact fstore_root_finish hp hR hMR hFP hctx hMRo hco (by omega) (by omega) hvb ‹_› (hA64 _ rfl)
    (hIP _ (addr_mem_intArgs_store ..)) ‹_› (t := .float 64) (sz := .size64) rfl (.inr rfl)
    (cond_fstore hvt (.inr ⟨rfl, rfl⟩))
    (fun rd amv am h => by rw [ofV_fpuStore64', h]; rfl) hA (fpustore64_helper_ok hp ctx hco (by omega) hH) hS

end Roots

/-! ## `MemRulesCorrectRT program` -/

/-- The float memory root rules of `lower`, in order. -/
theorem lower_floatMemRoot_filter : (program.rulesOf TId.lower).filter floatMemRootRule =
    [rule_lower_2625, rule_lower_2746, rule_lower_2628, rule_lower_2750] := by
  rw [program_rulesOf_686]
  rfl

/-- **S11e4's target (float loads and stores)**: over float-capable contexts (`CtxInvT`), under
`MemRefinesR Rd` and the FP accesses' `MemRefinesFP Rd`, the float memory roots of `lower` are
correct. -/
theorem memRulesCorrectRT_program : MemRulesCorrectRT program := by
  intro Rd F sb syms isem MR env cp hR hMR _ hFP r hr hmem
  have hsub : r ∈ (program.rulesOf TId.lower).filter floatMemRootRule := List.mem_filter.2 ⟨hr, hmem⟩
  rw [lower_floatMemRoot_filter] at hsub
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsub
  rcases hsub with rfl | rfl | rfl | rfl
  · exact load_f32_okT data_program hR hMR hFP
  · exact store_f32_okT data_program hR hMR hFP
  · exact load_f64_okT data_program hR hMR hFP
  · exact store_f64_okT data_program hR hMR hFP

end Backend.Proof
