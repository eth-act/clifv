import FV.Backend.Proof.IselTermsALUAExt
import FV.Backend.Proof.IselFamALUAMul

/-!
# Extended-register root rules of family A: `LowerRuleOk`

`iadd_extend_right` (108), `iadd_extend_left` (111), `isub_extend` (816): the operand defined
by `uextend`/`sextend ty' x'` with `x'` of 8/16/32 bits (`ext_extended_inv`) is read as the
extended register `x'` (`extendVal`). Its value (`extend_value`: `DFGCons` for the extend,
`FrameTyped` for the width of `x'`) is what `extendVal` computes on the low bits
(`extendVal_holds`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-! ## CLIF side: the extend's value -/

/-- The value of `extend op` at width `v`. -/
def extVal (op : Clif.ExtendOp) (v : Nat) {w : Nat} (x : BitVec w) : BitVec v :=
  match op with
  | .uextend => Clif.Sem.uextend v x
  | .sextend => Clif.Sem.sextend v x

theorem evalInst_extend_inv {fr : Clif.Frame} {cm cm' : Clif.Mem} {op : Clif.ExtendOp}
    {ty : Clif.Ty} {x : Nat} {vals : List Clif.Val}
    (h : Clif.evalInst fr cm (.extend op ty x) = .ok (vals, cm')) :
    ∃ a, fr.get x = .ok a ∧ vals = [⟨ty, extVal op ty.width a.bits⟩] := by
  simp only [Clif.evalInst] at h
  cases hx : fr.get x with
  | trap c => rw [hx] at h; cases h
  | stuck m => rw [hx] at h; cases h
  | ok a =>
  rw [hx] at h
  simp only [Clif.Res.ok_bind] at h
  by_cases hlt : a.ty.width < ty.width
  · simp only [hlt, decide_true, Clif.Res.check_true, Clif.Res.ok_bind] at h
    cases op <;> simp only [Clif.Res.pure_eq] at h <;> injection h with h <;>
      injection h with h1 h2 <;> exact ⟨a, rfl, h1.symm⟩
  · simp only [hlt, decide_false, Clif.Res.check_false] at h
    cases h

theorem defClif_inv {ctx : Ctx} {y : Nat} {cl : Clif.Inst} (h : ctx.defClif? y = some cl) :
    ∃ j info, ctx.defInst? y = some j ∧ ctx.insts[j]? = some info ∧ info.clif = some cl := by
  unfold Ctx.defClif? at h
  cases hj : ctx.defInst? y with
  | none => rw [hj] at h; cases h
  | some j =>
  rw [hj] at h
  have h' : (ctx.insts[j]? >>= fun d => d.clif) = some cl := h
  cases hi : ctx.insts[j]? with
  | none => rw [hi] at h'; cases h'
  | some info =>
  rw [hi] at h'
  exact ⟨j, info, rfl, hi, h'⟩

/-- **The value of a looked-through extend** `extend op ty' x'` read at the instruction's type:
the extension of `x'`'s value, whose width is the context's type of `x'`. -/
theorem extend_value {ctx : Ctx} {fr : Clif.Frame} (hdfg : DFGCons ctx fr) {y x' b : Nat}
    {op : Clif.ExtendOp} {ty' ty : Clif.Ty} {v : BitVec ty.width}
    (hdc : ctx.defClif? y = some (.extend op ty' x')) (hvt : ctx.valueType? x' = some (.int b))
    (hy : fr.getAs y ty = .ok v) :
    ∃ a, fr.regs x' = some a ∧ a.ty.width = b ∧ v = extVal op ty.width a.bits := by
  obtain ⟨j, info, hj, hij, hcl⟩ := defClif_inv hdc
  obtain ⟨vals, hev, hl⟩ := hdfg.1 y j info _ _ hj hij hcl rfl (getAs_ok hy)
  obtain ⟨a, ha, rfl⟩ := evalInst_extend_inv (hev default)
  have hv := lookup_zip_single hl
  cases hv
  have hta := hdfg.2 x' (.int b) a hvt (get_ok ha)
  rw [ofClif_int_width] at hta
  injection hta with hta
  exact ⟨a, get_ok ha, hta, rfl⟩

/-! ## Arm side: the extended operand -/

theorem setWidth_signExtend_of_le {w n m : Nat} (x : BitVec w) (h : m ≤ n) :
    (x.signExtend n).setWidth m = x.signExtend m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi, decide_true, Bool.true_and]
  have : i < n := by omega
  simp [this]

/-- **Width lemma of the extended-register operand**: `extendVal e n c` truncated to `m ≤ n` is
the CLIF extension of the `b`-bit value `c` holds. -/
theorem extendVal_holds {op : Clif.ExtendOp} {b : Nat} {e : ExtendOp} (he : extOpOf op b = some e)
    {tya : Clif.Ty} (hb : tya.width = b) {bits : BitVec tya.width} {c : CV}
    (hc : c.setWidth tya.width = bits) {n m : Nat} (hm : m ≤ n) :
    (extendVal e n c).setWidth m = extVal op m bits := by
  cases tya <;> simp only [Clif.Ty.width] at hb hc <;> subst hb <;> cases op <;>
    simp only [extOpOf, Option.some.injEq, reduceCtorEq] at he <;> subst he <;>
    simp only [extendVal, extVal, lo64, Clif.Sem.uextend, Clif.Sem.sextend,
      BitVec.zeroExtend_eq_setWidth] <;>
    simp only [BitVec.setWidth_setWidth_of_le, Nat.reduceLeDiff, hc] <;>
    first | exact BitVec.setWidth_setWidth_of_le _ hm | exact setWidth_signExtend_of_le _ hm

theorem operands_aluRRRExtend (op : ALUOp) (sz : OperandSize) (d x y : Nat) (e : ExtendOp) :
    (MInst.aluRRRExtend op sz (.vreg d .int) (.vreg x .int) (.vreg y .int) e).operands =
      .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨x, .int, .use, .early, .reg⟩,
        ⟨y, .int, .use, .early, .reg⟩] := rfl

theorem vuseNums_aluRRRExtend (op : ALUOp) (sz : OperandSize) (d x y : Nat) (e : ExtendOp) :
    vuseNums (.aluRRRExtend op sz (.vreg d .int) (.vreg x .int) (.vreg y .int) e) = [x, y] := rfl

theorem ispec_aluRRRExtend {op : ALUOp} {sz : OperandSize} {d : Nat} {rn rm : Reg} {e : ExtendOp}
    {a b : CV} {w : Arm.ArmState} {r : BitVec sz.bits} (hop : op = .add ∨ op = .sub)
    (hv : aluVal op (opnd sz a) (extendVal e sz.bits b) = some r) :
    ispec (.aluRRRExtend op sz (.vreg d .int) rn rm e) [a, b] w = some ([resX sz r], w, .next) := by
  rcases hop with rfl | rfl <;>
    simp only [ispec, true_or, or_true, ↓reduceIte, hv, Option.map_some] <;> rfl

/-! ## The rules -/

/-- **`iadd_extend_right`** (`lower.isle:108`, `iadd x (extend y)` → `add x, y, {u,s}xt*`), i8..i64. -/
theorem iadd_extend_right_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_108 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
    hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 60 := ⟨n - 60, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 9) (cop := .iadd) rfl hp.t2357 term_2357_kind
      variantNames_Iadd rfl hmatch
  obtain ⟨e2, -, hpy⟩ := values2_match_inv hp ctx hrest
  obtain ⟨fs, hx0, -⟩ := matchPat_extract_inv hp.t345 term_345_kind rfl hpy
  rw [sem_extract] at hx0
  obtain ⟨op, ty', x', b, e, hdc, hvt, he, rfl⟩ := ext_extended_inv ctx _ hx0
  rw [match_108 hp ctx st tr m' hi hhead hw hd hdc hvt he] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_108_none hp ctx hco st tr n' (.inl hrx) _ _)
  | some rx =>
  cases hrx' : ctx.valueReg? x' with
  | none => exact absurd heval (rhs_108_none hp ctx hco st tr n' (.inr hrx') _ _)
  | some rx' =>
  obtain rfl := hctx.valueReg x rx hrx
  obtain rfl := hctx.valueReg x' rx' hrx'
  obtain ⟨tr'', he'⟩ := rhs_108 hp ctx hco st tr n' hrx hrx' hw
  rw [he'] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  obtain ⟨a, ha, hab, rfl⟩ := extend_value hdfg hdc hvt hy
  have hB := extendVal_holds he hab (hvals x' a ha) (n := (szOf ty.width).bits) (szOf_bits hw)
  obtain ⟨r, hr, hh⟩ := aluVal_holds_B (op := .add) (cop := .iadd) (by simp) (szOf_bits hw)
    (hvals x _ (getAs_ok hx)) hB
  refine ⟨fun z hz => ?_, _, ispec_aluRRRExtend (.inl rfl) hr, hh⟩
  rw [vuseNums_aluRRRExtend] at hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl
  · exact getAs_isSome hx
  · simp [ha]

/-- **`iadd_extend_left`** (`lower.isle:111`, `iadd (extend x) y` → `add y, x, {u,s}xt*`), i8..i64. -/
theorem iadd_extend_left_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_111 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
    hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 60 := ⟨n - 60, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 9) (cop := .iadd) rfl hp.t2357 term_2357_kind
      variantNames_Iadd rfl hmatch
  obtain ⟨e2, hpx, -⟩ := values2_match_inv hp ctx hrest
  obtain ⟨fs, hx0, -⟩ := matchPat_extract_inv hp.t345 term_345_kind rfl hpx
  rw [sem_extract] at hx0
  obtain ⟨op, ty', x', b, e, hdc, hvt, he, rfl⟩ := ext_extended_inv ctx _ hx0
  rw [match_111 hp ctx st tr m' hi hhead hw hd hdc hvt he] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hry : ctx.valueReg? y with
  | none => exact absurd heval (rhs_111_none hp ctx hco st tr n' (.inl hry) _ _)
  | some ry =>
  cases hrx' : ctx.valueReg? x' with
  | none => exact absurd heval (rhs_111_none hp ctx hco st tr n' (.inr hrx') _ _)
  | some rx' =>
  obtain rfl := hctx.valueReg y ry hry
  obtain rfl := hctx.valueReg x' rx' hrx'
  obtain ⟨tr'', he'⟩ := rhs_111 hp ctx hco st tr n' hry hrx' hw
  rw [he'] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  obtain ⟨a, ha, hab, rfl⟩ := extend_value hdfg hdc hvt hx
  have hB := extendVal_holds he hab (hvals x' a ha) (n := (szOf ty.width).bits) (szOf_bits hw)
  obtain ⟨r, hr, hh⟩ := aluVal_holds_B (op := .add) (cop := .iadd) (by simp) (szOf_bits hw)
    (hvals y _ (getAs_ok hy)) hB
  refine ⟨fun z hz => ?_, _, ispec_aluRRRExtend (.inl rfl) hr, ?_⟩
  · rw [vuseNums_aluRRRExtend] at hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl
    · exact getAs_isSome hy
    · simp [ha]
  · show VHolds ⟨ty, _ + _⟩ _
    rw [BitVec.add_comm]
    exact hh

/-- **`isub_extend`** (`lower.isle:816`, `isub x (extend y)` → `sub x, y, {u,s}xt*`), i8..i64. -/
theorem isub_extend_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_816 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb _hfirst
    hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 60 := ⟨n - 60, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 9) (cop := .isub) rfl hp.t2358 term_2358_kind
      variantNames_Isub rfl hmatch
  obtain ⟨e2, -, hpy⟩ := values2_match_inv hp ctx hrest
  obtain ⟨fs, hx0, -⟩ := matchPat_extract_inv hp.t345 term_345_kind rfl hpy
  rw [sem_extract] at hx0
  obtain ⟨op, ty', x', b, e, hdc, hvt, he, rfl⟩ := ext_extended_inv ctx _ hx0
  rw [match_816 hp ctx st tr m' hi hhead hw hd hdc hvt he] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_816_none hp ctx hco st tr n' (.inl hrx) _ _)
  | some rx =>
  cases hrx' : ctx.valueReg? x' with
  | none => exact absurd heval (rhs_816_none hp ctx hco st tr n' (.inr hrx') _ _)
  | some rx' =>
  obtain rfl := hctx.valueReg x rx hrx
  obtain rfl := hctx.valueReg x' rx' hrx'
  obtain ⟨tr'', he'⟩ := rhs_816 hp ctx hco st tr n' hrx hrx' hw
  rw [he'] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨_, _, emitted_fresh_emit _ _, by rw [fresh_fst], ?_⟩
  rw [fresh_fst]
  refine lowerInstOk_one hR hMR rfl rfl rfl fun fr ρ w hvals hdfg u v hx hy => ?_
  obtain ⟨a, ha, hab, rfl⟩ := extend_value hdfg hdc hvt hy
  have hB := extendVal_holds he hab (hvals x' a ha) (n := (szOf ty.width).bits) (szOf_bits hw)
  obtain ⟨r, hr, hh⟩ := aluVal_holds_B (op := .sub) (cop := .isub) (by simp) (szOf_bits hw)
    (hvals x _ (getAs_ok hx)) hB
  refine ⟨fun z hz => ?_, _, ispec_aluRRRExtend (.inr rfl) hr, hh⟩
  rw [vuseNums_aluRRRExtend] at hz
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl
  · exact getAs_isSome hx
  · simp [ha]

end Backend.Proof
