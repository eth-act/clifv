import FV.Backend.Proof.IselMemAmode
import FV.Backend.Proof.IselFamALUAExt
import FV.Backend.Proof.IselFamAluBIconst

/-!
# Memory family (M4Mem2): `amode_reg_scaled`

DFG look-through helpers (the data of a defining instruction is its `instData`) and the
contract of `amode_reg_scaled` (`inst.isle:4108`, 3 rules): `RegScaled base index`, or
`RegScaledExtended base x {U,S}XTW` when `index` is an extend of the 32-bit value `x`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## CLIF side -/

theorem getAs_of_regs {fr : Clif.Frame} {x : Nat} {ty : Clif.Ty} {b : BitVec ty.width}
    (h : fr.regs x = some ⟨ty, b⟩) : fr.getAs x ty = .ok b := by
  unfold Clif.Frame.getAs Clif.Frame.get
  rw [h]
  simp [Clif.Res.ofOption]

/-- The data of a value's defining instruction is `instData` of its CLIF instruction. -/
theorem def_data {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {y j : Nat} {info : IInfo}
    (hj : ctx.defInst? y = some j) (hi : ctx.insts[j]? = some info) :
    ∃ cl, ctx.defClif? y = some cl ∧ info.clif = some cl ∧ instData f cl = .ok info.data := by
  have hs := hctx.defClif y j info hj hi
  obtain ⟨cl, hcl⟩ := Option.isSome_iff_exists.mp hs
  refine ⟨cl, ?_, hcl, hctx.data j info cl hi hcl⟩
  unfold Ctx.defClif?
  rw [hj]
  show (ctx.insts[j]? >>= fun d => d.clif) = some cl
  rw [hi]; exact hcl

theorem def_data' {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {y j : Nat} {info : IInfo}
    {v : V} (hj : ctx.defInst? y = some j) (hi : ctx.insts[j]? = some info) (hd : v = info.data) :
    ∃ cl, ctx.defClif? y = some cl ∧ info.clif = some cl ∧ instData f cl = .ok v := by
  subst hd; exact def_data hctx hj hi

theorem mem_variantNames_Unary : (variantNames 152)[29]? = some "Unary" := rfl
theorem mem_variantNames_Uextend : (variantNames 151)[141]? = some "Uextend" := rfl
theorem mem_variantNames_Sextend : (variantNames 151)[142]? = some "Sextend" := rfl

/-- An instruction with `Unary`/`Uextend` or `Sextend` data is an extend. -/
theorem instData_extend_inv {f : Clif.Function} {cl : Clif.Inst} {k : Nat} {w : V}
    (h : instData f cl = .ok (.data 152 29 [.data 151 k [], w])) (hk : k = 141 ∨ k = 142) :
    ∃ ty x, cl = .extend (if k = 141 then .uextend else .sextend) ty x ∧ w = .value x ∧
      eTy ty = true := by
  obtain ⟨hf, ho⟩ := instData_inv_names h
  rw [mem_variantNames_Unary] at hf
  have ho' : (instNames cl).2 = (if k = 141 then "Uextend" else "Sextend") := by
    rcases hk with rfl | rfl
    · rw [mem_variantNames_Uextend] at ho; simpa using ho.symm
    · rw [mem_variantNames_Sextend] at ho; simpa using ho.symm
  cases cl <;> simp only [instNames, Option.some.injEq] at hf ho'
  all_goals try (simp at hf; done)
  all_goals first
    | (rename_i op _ _; rcases hk with rfl | rfl <;> cases op <;> simp [unaryOpcode] at ho'; done)
    | (rcases hk with rfl | rfl <;> simp at ho'; done)
    | skip
  rename_i op ty x
  simp only [instData] at h
  split at h
  · rename_i he
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
    simp only [List.cons.injEq, and_true] at h3
    refine ⟨ty, x, ?_, h3.2, he⟩
    rcases hk with rfl | rfl <;> cases op <;> simp_all
  · cases h

/-! ## Inverting the data of looked-through instructions -/

theorem instData_names_eq {f : Clif.Function} {cl : Clif.Inst} {kf ko : Nat} {fs : List V}
    {a b : String} (h : instData f cl = .ok (.data 152 kf (.data 151 ko [] :: fs)))
    (ha : (variantNames 152)[kf]? = some a) (hb : (variantNames 151)[ko]? = some b) :
    instNames cl = (a, b) := by
  obtain ⟨hf, ho⟩ := instData_inv_names h
  rw [ha] at hf; rw [hb] at ho
  exact Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm

theorem instData_binary_fields {f : Clif.Function} {op : Clif.BinaryOp} {ty : Clif.Ty} {a b : Nat}
    {kf ko : Nat} {fs : List V}
    (h : instData f (.binary op ty a b) = .ok (.data 152 kf (.data 151 ko [] :: fs))) :
    fs = [.values [a, b]] ∧ eTy ty = true := by
  simp only [instData] at h
  split at h
  · split at h
    · rename_i he
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
      simp only [List.cons.injEq] at h3
      exact ⟨h3.2, he⟩
    · cases h
  · cases h

theorem mem_variantNames_Binary : (variantNames 152)[2]? = some "Binary" := rfl
theorem mem_variantNames_Iadd : (variantNames 151)[73]? = some "Iadd" := rfl
theorem mem_variantNames_Ishl : (variantNames 151)[103]? = some "Ishl" := rfl
theorem mem_variantNames_StackAddr : (variantNames 152)[21]? = some "StackAddr" := rfl
theorem mem_variantNames_StackAddrOp : (variantNames 151)[47]? = some "StackAddr" := rfl

theorem inv_iadd {f : Clif.Function} {cl : Clif.Inst} {w : V}
    (h : instData f cl = .ok (.data 152 2 [.data 151 73 [], w])) :
    ∃ ty a b, cl = .binary .iadd ty a b ∧ w = .values [a, b] ∧ eTy ty = true := by
  have hn := instData_names_eq h mem_variantNames_Binary mem_variantNames_Iadd
  cases cl <;> simp only [instNames, Prod.mk.injEq] at hn
  all_goals try (simp at hn; done)
  · rename_i op ty a b
    cases op <;> simp [binaryOpcode] at hn
    obtain ⟨h1, h2⟩ := instData_binary_fields h
    simp only [List.cons.injEq, and_true] at h1
    exact ⟨ty, a, b, rfl, h1, h2⟩
  · rename_i op _ _ _
    cases op <;> simp [divOpcode] at hn

theorem inv_ishl {f : Clif.Function} {cl : Clif.Inst} {w : V}
    (h : instData f cl = .ok (.data 152 2 [.data 151 103 [], w])) :
    ∃ ty a b, cl = .binary .ishl ty a b ∧ w = .values [a, b] ∧ eTy ty = true := by
  have hn := instData_names_eq h mem_variantNames_Binary mem_variantNames_Ishl
  cases cl <;> simp only [instNames, Prod.mk.injEq] at hn
  all_goals try (simp at hn; done)
  · rename_i op ty a b
    cases op <;> simp [binaryOpcode] at hn
    obtain ⟨h1, h2⟩ := instData_binary_fields h
    simp only [List.cons.injEq, and_true] at h1
    exact ⟨ty, a, b, rfl, h1, h2⟩
  · rename_i op _ _ _
    cases op <;> simp [divOpcode] at hn

theorem inv_iconst {f : Clif.Function} {cl : Clif.Inst} {w : V}
    (h : instData f cl = .ok (.data 152 35 [.data 151 57 [], w])) :
    ∃ ty imm, cl = .iconst ty imm ∧ w = .int (imm64OfIconst ty imm) ∧ eTy ty = true := by
  have hn := instData_names_eq h fb_variantNames_UnaryImm fb_variantNames_Iconst
  obtain ⟨ty, imm, rfl⟩ := fb_instNames_iconst hn
  obtain ⟨he, hw⟩ := fb_instData_iconst h
  simp only [List.cons.injEq, and_true] at hw
  exact ⟨ty, imm, rfl, hw, he⟩

theorem inv_uextend {f : Clif.Function} {cl : Clif.Inst} {w : V}
    (h : instData f cl = .ok (.data 152 29 [.data 151 141 [], w])) :
    ∃ ty x, cl = .extend .uextend ty x ∧ w = .value x ∧ eTy ty = true :=
  instData_extend_inv h (.inl rfl)

theorem inv_sextend {f : Clif.Function} {cl : Clif.Inst} {w : V}
    (h : instData f cl = .ok (.data 152 29 [.data 151 142 [], w])) :
    ∃ ty x, cl = .extend .sextend ty x ∧ w = .value x ∧ eTy ty = true :=
  instData_extend_inv h (.inr rfl)

theorem inv_stackAddr {f : Clif.Function} {cl : Clif.Inst} {w1 w2 : V}
    (h : instData f cl = .ok (.data 152 21 [.data 151 47 [], w1, w2])) :
    ∃ ty sl o, cl = .stackAddr ty sl o ∧ w1 = .op (.stackSlot sl) ∧ w2 = .int o := by
  have hn := instData_names_eq h mem_variantNames_StackAddr mem_variantNames_StackAddrOp
  cases cl <;> simp only [instNames, Prod.mk.injEq] at hn
  all_goals try (simp at hn; done)
  all_goals try (rename_i op _ _ _; cases op <;> simp [binaryOpcode, divOpcode] at hn; done)
  all_goals try (rename_i op _ _; cases op <;> simp [unaryOpcode] at hn; done)
  all_goals try (rename_i op _ _ _ _ _; cases op <;> simp [loadOpcode] at hn; done)
  all_goals try (rename_i op _ _ _ _ _ _; cases op <;> simp [storeOpcode] at hn; done)
  all_goals try (split at hn <;> simp at hn; done)
  rename_i ty sl o
  simp only [instData, pure, Except.pure, Except.ok.injEq] at h
  obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
  simp only [List.cons.injEq, and_true] at h3
  exact ⟨ty, sl, o, rfl, h3.2.1, h3.2.2⟩

open Lean Elab Tactic Meta in
/-- `mem_dfg hctx`: for a hypothesis `V.data 152 … = info.data` of an instruction `j` defining a
value (`ctx.defInst? y = some j`, `ctx.insts[j]? = some info`), replace it by the CLIF
instruction (`def_data'`, `ctx.defClif? y = some cl`) and invert its data (`inv_*`). Fails when
there is no such hypothesis. -/
elab "mem_dfg " hctx:ident : tactic => withMainContext do
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
    let e ← mkAppM ``Backend.Proof.def_data' #[(← getLocalDeclFromUserName hctx.getId).toExpr,
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
  throwError "mem_dfg: no instruction data to invert"

/-- `mem_invd hp hctx at h…`: `mem_inv`, then `mem_dfg` and the inverse-evaluation simp set to a
fixpoint (inverting the data of every looked-through instruction). -/
macro "mem_invd " hp:ident hctx:ident " at " h1:ident h2:ident : tactic =>
  `(tactic| ((mem_inv $hp [] at $h1 $h2); (repeat ((mem_dfg $hctx); (repeat (mem_inv_simp [] at * <;> isel_destruct <;> subst_vars))))))

/-! ## `amode_reg_scaled` -/

/-- What `amode_reg_scaled (vreg d) y` produced: an addressing mode `d + (index << log2 bytes)`
whose index register `y'` is a value's vreg (defined when `y` is) and holds the value of `y`
(`y` itself, or the 32-bit operand of the extend defining `y`). -/
structure ScaledOk (ctx : Ctx) (d y : Nat) (am : AMode) : Prop where
  vregs : AmVregs am
  idx : ∃ y', amVregs am = [d, y'] ∧ ctx.valueReg? y' = some (.vreg y' .int) ∧
    ∀ (sb : Nat) (fr : Clif.Frame) (ρ : Nat → CV), DFGCons ctx fr → ValsHeld fr ρ →
      ∀ yv, fr.regs y = some yv → yv.ty = .i64 →
      (fr.regs y').isSome ∧ ∀ (a : CV) (w : Arm.ArmState) (bytes : Nat),
        amodeAddr sb am bytes [a, ρ y'] w = some (lo64 a + (BitVec.ofNat 64 yv.toNat <<< log2 bytes))

theorem ofNat_toNat64 (b : BitVec 64) : BitVec.ofNat 64 b.toNat = b := by simp

/-- The index of a scaled-extended mode: the extend of the 32-bit `x` defining `y`. -/
theorem scaled_ext_ok {ctx : Ctx} {d y x : Nat}
    {op : Clif.ExtendOp} {ty : Clif.Ty} {e : ExtendOp} (he : extOpOf op 32 = some e)
    (hdc : ctx.defClif? y = some (.extend op ty x)) (hvt : ctx.valueType? x = some (.int 32))
    (hr : ctx.valueReg? x = some (.vreg x .int)) (hue : e = .uxtw ∨ e = .sxtw) :
    ScaledOk ctx d y (.regScaledExtended (.vreg d .int) (.vreg x .int) e) := by
  refine ⟨fun r hr' => ?_, x, rfl, hr, ?_⟩
  · simp only [AMode.regs, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl <;> exact ⟨_, rfl⟩
  intro sb fr ρ hdfg hv yv hy ht
  obtain ⟨tyy, bits⟩ := yv
  simp only at ht; subst ht
  obtain ⟨a, ha, haw, hbits⟩ := extend_value hdfg hdc hvt (getAs_of_regs hy)
  refine ⟨by rw [ha]; rfl, fun c w bytes => ?_⟩
  have hx := extendVal_holds he haw (hv x a ha) (Nat.le_refl 64)
  rw [BitVec.setWidth_eq] at hx
  simp only [amodeAddr, hue, ite_true, Clif.Val.toNat]
  rw [hx]
  subst hbits
  show _ = some (lo64 c + BitVec.ofNat 64 (extVal op 64 a.bits).toNat <<< log2 bytes)
  rw [ofNat_toNat64]

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

include hp hc in
/-- **`amode_reg_scaled base index`** (all three rules). -/
theorem amode_reg_scaled_ok {f : Clif.Function} (hctx : CtxInv f ctx) {n : Nat} (hn : 40 ≤ n)
    {d y : Nat} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 89 576 [.reg (.vreg d .int), .value y] s v s') :
    s'.1 = s.1 ∧ ∃ am, v.amode? = some am ∧ ScaledOk ctx d y am := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 576
  · mem_inv hp [] at hm he
    obtain ⟨cl, hdc, -, hdat⟩ := def_data' hctx ‹_› ‹_› ‹_›
    obtain ⟨ty, x, rfl, rfl, -⟩ := instData_extend_inv hdat (.inl rfl)
    simp only [ext_value_type_iff, ctor_put_in_reg_iff, V.ty.injEq, List.cons.injEq, and_true] at *
    isel_destruct; subst_vars
    obtain rfl := hctx.valueReg x _ ‹_›
    exact ⟨rfl, _, rfl, scaled_ext_ok (op := .uextend) rfl hdc ‹_› ‹_› (.inl rfl)⟩
  · mem_inv hp [] at hm he
    obtain ⟨cl, hdc, -, hdat⟩ := def_data' hctx ‹_› ‹_› ‹_›
    obtain ⟨ty, x, rfl, rfl, -⟩ := instData_extend_inv hdat (.inr rfl)
    simp only [ext_value_type_iff, ctor_put_in_reg_iff, V.ty.injEq, List.cons.injEq, and_true] at *
    isel_destruct; subst_vars
    obtain rfl := hctx.valueReg x _ ‹_›
    exact ⟨rfl, _, rfl, scaled_ext_ok (op := .sextend) rfl hdc ‹_› ‹_› (.inr rfl)⟩
  · mem_inv hp [] at hm he
    obtain rfl := hctx.valueReg y _ ‹_›
    refine ⟨_, rfl, fun r hr => ?_, y, rfl, ‹_›, ?_⟩
    · simp only [AMode.regs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, rfl⟩
    intro sb fr ρ hdfg hv yv hy ht
    refine ⟨by rw [hy]; rfl, fun a w bytes => ?_⟩
    simp only [amodeAddr]
    rw [lo64_of_holds (hv y yv hy) ht]

end Backend.Proof
