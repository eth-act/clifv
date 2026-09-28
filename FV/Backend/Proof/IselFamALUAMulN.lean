import FV.Backend.Proof.IselTermsALUAMulN
import FV.Backend.Proof.IselFamALUAExtr

/-!
# Narrow `smulhi`/`umulhi` root rules (1059, 1071): `LowerRuleOk` at i8/i16/i32

`smulhi x y` at a type of at most 32 bits → `sxt` both operands to 64 bits
(`put_in_reg_sext64`), `madd` them into 64 bits (`xzr` addend), `asr` by the width;
`umulhi` the same with `uxt` and `lsr`. The operand parts are abstracted as `PartOk` (code, fresh
defs, uses, and the 64-bit extension it leaves in its result register); the `I64` arm of
`put_in_reg_*ext64` is impossible at a narrow type by `FrameTyped` (its `PartOk` is vacuous).
The straight-line run is composed with `seqRun_append_fall_fa`; `mulhi_narrow_s/u` are the width
lemmas (the high half of the `2w`-bit product sits in bits `w..2w-1` of the 64-bit product).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-! ## Interpreter inversion for `let` right-hand sides -/

section LetInv
variable {p : Program} {σ : Type} {sem' : Isle.Sem V σ} {cfg : Config}

theorem evalExpr_let_inv {n : Nat} {ty : TypeId} {bs : List (VarId × TypeId × Expr)} {body : Expr}
    {env : Interp.Env V} {s s' : σ × Array RuleId} {out : V}
    (h : (evalExpr p sem' cfg (n + 1) (.let ty bs body) env).run s = .ok (some out, s')) :
    ∃ env' s1, (evalBinds p sem' cfg n bs env).run s = .ok (some env', s1) ∧
      (evalExpr p sem' cfg n body env').run s1 = .ok (some out, s') := by
  rw [evalExpr.eq_6] at h
  simp only [M.run_bind] at h
  cases hb : (evalBinds p sem' cfg n bs env).run s with
  | error e => rw [hb] at h; cases h
  | ok q =>
    obtain ⟨o, s1⟩ := q
    rw [hb] at h
    cases o with
    | none => simp at h
    | some env' => exact ⟨env', s1, rfl, h⟩

theorem evalBinds_cons_inv {n : Nat} {x : VarId} {ty : TypeId} {e : Expr}
    {bs : List (VarId × TypeId × Expr)} {env env' : Interp.Env V} {s s' : σ × Array RuleId}
    (h : (evalBinds p sem' cfg (n + 1) ((x, ty, e) :: bs) env).run s = .ok (some env', s')) :
    ∃ v s1, (evalExpr p sem' cfg n e env).run s = .ok (some v, s1) ∧ x < env.size ∧
      (evalBinds p sem' cfg n bs (env.set! x (some v))).run s1 = .ok (some env', s') := by
  rw [evalBinds.eq_3] at h
  simp only [M.run_bind] at h
  cases he : (evalExpr p sem' cfg n e env).run s with
  | error e => rw [he] at h; cases h
  | ok q =>
    obtain ⟨o, s1⟩ := q
    rw [he] at h
    cases o with
    | none => simp at h
    | some v =>
      simp only [M.except_ok_bind] at h
      split at h
      · rename_i hlt
        exact ⟨v, s1, rfl, hlt, h⟩
      · cases h

theorem evalArgs_var1 {n : Nat} {ty : TypeId} {i : VarId} {env : Interp.Env V} {v : V}
    (hv : env[i]? = some (some v)) (s : σ × Array RuleId) :
    (evalArgs p sem' cfg (n + 2) [.var ty i] env).run s = .ok (some [v], s) := by
  rw [evalArgs.eq_3]
  simp only [M.run_bind]
  rw [evalExpr.eq_2]
  simp only [hv]
  rfl

end LetInv

/-! ## Straight-line code -/

theorem seqRun_append_fall_fa {isem : Sem} :
    ∀ {ms1 ms2 : List MInst} {ρ ρ1 ρ2 : Nat → CV} {w w1 w2 : Arm.ArmState},
      seqRun isem ms1 ρ w = some (.fall ρ1 w1) → seqRun isem ms2 ρ1 w1 = some (.fall ρ2 w2) →
      seqRun isem (ms1 ++ ms2) ρ w = some (.fall ρ2 w2)
  | [], _, ρ, ρ1, ρ2, w, w1, w2, h1, h2 => by
    simp only [seqRun, Option.some.injEq, SeqEnd.fall.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    exact h2
  | i :: ms, ms2, ρ, ρ1, ρ2, w, w1, w2, h1, h2 => by
    rw [List.cons_append]
    simp only [seqRun] at h1 ⊢
    cases hops : i.operands with
    | error e => simp [hops] at h1
    | ok ops =>
    simp only [hops] at h1 ⊢
    cases hs : isem i (vuses ops ρ) w with
    | none => simp [hs] at h1
    | some q =>
    obtain ⟨outs, w', ctl⟩ := q
    simp only [hs] at h1 ⊢
    by_cases hlen : outs.length = (ops.toList.filter Operand.isDef).length
    · simp only [hlen, ↓reduceIte] at h1 ⊢
      cases ctl with
      | next =>
        simp only at h1 ⊢
        cases hr : seqRun isem ms (vdefUpd ops outs ρ) w' with
        | none => rw [hr] at h1; cases h1
        | some e =>
          rw [hr] at h1
          cases e with
          | fall ρ' w'' =>
            simp only [Option.map_some, SeqEnd.succ, Option.some.injEq, SeqEnd.fall.injEq] at h1
            obtain ⟨rfl, rfl⟩ := h1
            rw [seqRun_append_fall_fa hr h2]
            rfl
          | stop _ _ _ _ _ _ _ _ => simp [SeqEnd.succ] at h1
      | _ => simp at h1
    · simp only [hlen, ↓reduceIte] at h1
      cases h1

/-! ## Instruction forms -/

theorem operands_extend_fa (d x : Nat) (sg : Bool) (a b : Nat) :
    (MInst.extend (.vreg d .int) (.vreg x .int) sg a b).operands =
      .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨x, .int, .use, .early, .reg⟩] := rfl

theorem vuseNums_extend (d x : Nat) (sg : Bool) (a b : Nat) :
    vuseNums (MInst.extend (.vreg d .int) (.vreg x .int) sg a b) = [x] := rfl

theorem vdefs_extend (d x : Nat) (sg : Bool) (a b : Nat) :
    vdefs (MInst.extend (.vreg d .int) (.vreg x .int) sg a b) = [d] := rfl

/-- The 64-bit extension of a `w`-bit value (`sg`: signed). -/
def extW (sg : Bool) {w : Nat} (u : BitVec w) : BitVec 64 :=
  if sg then u.signExtend 64 else u.setWidth 64

theorem ispec_extend64 {d : Nat} {rn : Reg} {sg : Bool} {b : Nat} {a : CV} {w : Arm.ArmState}
    (hb : b = 8 ∨ b = 16 ∨ b = 32) :
    ispec (.extend (.vreg d .int) rn sg b 64) [a] w =
      some ([ofX (extW sg ((lo64 a).setWidth b))], w, .next) := by
  rcases hb with rfl | rfl | rfl <;> cases sg <;>
    simp [ispec, extW, BitVec.setWidth_eq, defOut]

theorem operands_aluRRImmShift (op : ALUOp) (sz : OperandSize) (d x s : Nat) :
    (MInst.aluRRImmShift op sz (.vreg d .int) (.vreg x .int) s).operands =
      .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨x, .int, .use, .early, .reg⟩] := rfl

theorem ispec_aluRRImmShift {op : ALUOp} {sz : OperandSize} {d : Nat} {rn : Reg} {s : Nat} {a : CV}
    {w : Arm.ArmState} {r : BitVec sz.bits} (hs : s < sz.bits)
    (hv : shiftVal op (opnd sz a) s = some r) :
    ispec (.aluRRImmShift op sz (.vreg d .int) rn s) [a] w = some ([resX sz r], w, .next) := by
  simp only [ispec, hs, ↓reduceIte, hv, Option.map_some]
  rfl

/-! ## Width lemmas -/

theorem lo64_ofX (r : BitVec 64) : lo64 (ofX r) = r := by
  simp only [lo64, ofX, BitVec.setWidth_setWidth_of_le _ (show 64 ≤ 128 by decide),
    BitVec.setWidth_eq]

theorem opnd64_lo (a : CV) : opnd .size64 a = lo64 a := by
  show (lo64 a).setWidth 64 = lo64 a
  exact BitVec.setWidth_eq _

theorem lo64_resX64_mulN (r : BitVec 64) : lo64 (resX .size64 r) = r := by
  show lo64 (ofX (r.setWidth 64)) = r
  rw [lo64_ofX, BitVec.setWidth_eq]

theorem opnd_resX64 (M : BitVec (OperandSize.bits .size64)) : opnd .size64 (resX .size64 M) = M := by
  have aux : ∀ M : BitVec 64, (((M.setWidth 64).setWidth 128).setWidth 64).setWidth 64 = M := by
    intro M
    simp [BitVec.setWidth_setWidth_of_le]
  exact aux M

theorem resX64_setWidth_le {k : Nat} (hk : k ≤ 64) (R : BitVec 64) :
    (resX .size64 R).setWidth k = R.setWidth k := by
  show ((R.setWidth 64).setWidth 128).setWidth k = R.setWidth k
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]

theorem extW_holds {sg : Bool} {ty : Clif.Ty} (hw : ty.width ≤ 64) {a : CV} {u : BitVec ty.width}
    (ha : VHolds ⟨ty, u⟩ a) : extW sg ((lo64 a).setWidth ty.width) = extW sg u := by
  simp only [VHolds] at ha
  simp only [lo64, BitVec.setWidth_setWidth_of_le _ hw, ha]

theorem high_half {w : Nat} (hw : w + w ≤ 64) (P : BitVec 64) :
    (P >>> w).setWidth w = (P.setWidth (w + w)).extractLsb' w w ∧
      (P.sshiftRight w).setWidth w = (P.setWidth (w + w)).extractLsb' w w := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_sshiftRight,
      BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and] <;>
    · have h1 : w + i < 64 := by omega
      have h2 : w + i < w + w := by omega
      simp [h1, h2, show ¬ 64 ≤ i by omega]

theorem mulhi_narrow_s {w : Nat} (hw : w ≤ 32) (u v : BitVec w) :
    ((0 + extW true u * extW true v).sshiftRight w).setWidth w = Clif.Sem.smulhi u v := by
  have hz : ∀ x : BitVec 64, 0 + x = x := fun x => by simp
  simp only [extW, ↓reduceIte, hz]
  rw [(high_half (by omega) _).2, BitVec.setWidth_mul _ _ (by omega),
    setWidth_signExtend_of_le _ (by omega), setWidth_signExtend_of_le _ (by omega)]
  rfl

theorem mulhi_narrow_u {w : Nat} (hw : w ≤ 32) (u v : BitVec w) :
    ((0 + extW false u * extW false v) >>> w).setWidth w = Clif.Sem.umulhi u v := by
  have hz : ∀ x : BitVec 64, 0 + x = x := fun x => by simp
  simp only [extW, Bool.false_eq_true, ↓reduceIte, hz]
  rw [(high_half (by omega) _).1, BitVec.setWidth_mul _ _ (by omega),
    BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_setWidth_of_le _ (by omega)]
  rfl

/-! ## The operand parts -/

/-- **An operand part**: code `ms` run from lowering state `st` to `st2` (fresh defs, uses only
`x`) leaving the 64-bit extension (`sg`) of `x`'s value in vreg `r`, and keeping every vreg
below `st.nextVreg` — whenever `x` has a narrow type. -/
def PartOk (F : BitVec 64 → Prop) (isem : Sem) (ctx : Ctx) (st st2 : LState) (x : Nat) (sg : Bool)
    (r : Nat) (ms : List MInst) : Prop :=
  st.nextVreg ≤ st2.nextVreg ∧ st2.emitted = st.emitted ++ ms.toArray ∧
  (∀ m ∈ ms, ∀ d ∈ vdefs m, st.nextVreg ≤ d ∧ d < st2.nextVreg) ∧
  (∀ m ∈ ms, ∀ q ∈ vuseNums m, q = x) ∧ r < st2.nextVreg ∧ (r = x ∨ st.nextVreg ≤ r) ∧
  ∀ (fr : Clif.Frame) (ρ : Nat → CV) (w : Arm.ArmState) (ty : Clif.Ty) (u : BitVec ty.width),
    DFGCons ctx fr → fr.getAs x ty = .ok u → ty.width ≤ 32 → VHolds ⟨ty, u⟩ (ρ x) →
    ∃ ρ' w', seqRun isem ms ρ w = some (.fall ρ' w') ∧ SameWorld F w' w ∧
      (∀ q, q < st.nextVreg → ρ' q = ρ q) ∧ lo64 (ρ' r) = extW sg u

theorem partOk_narrow {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {ctx : Ctx}
    {st : LState} {x : Nat} {t : CTy} {sg : Bool} (hvt : ctx.valueType? x = some t) :
    PartOk F isem ctx st ((st.fresh .int).2.emit (.extend (st.fresh .int).1 (.vreg x .int) sg t.bits 64))
      x sg st.nextVreg [.extend (st.fresh .int).1 (.vreg x .int) sg t.bits 64] := by
  rw [fresh_fst]
  refine ⟨by rw [nextVreg_fresh_emit]; omega, emitted_fresh_emit _ _, ?_, ?_,
    by rw [nextVreg_fresh_emit]; omega, .inr (Nat.le_refl _), ?_⟩
  · intro m hm d hd
    simp only [List.mem_singleton] at hm
    subst hm
    rw [vdefs_extend, List.mem_singleton] at hd
    subst hd
    rw [nextVreg_fresh_emit]
    omega
  · intro m hm q hq
    simp only [List.mem_singleton] at hm
    subst hm
    rw [vuseNums_extend, List.mem_singleton] at hq
    exact hq
  · intro fr ρ w ty u hdfg hx hw hv
    have ht := hdfg.2 x t _ hvt (getAs_ok hx)
    simp only [ofClif_int_width] at ht
    subst ht
    have hb : (CTy.int ty.width).bits = 8 ∨ (CTy.int ty.width).bits = 16 ∨
        (CTy.int ty.width).bits = 32 := by
      cases ty <;> simp [Clif.Ty.width, CTy.bits] at hw ⊢
    obtain ⟨w', hrun, hsw⟩ := seqRun_one hR (operands_extend_fa _ _ _ _ _) rfl
      (ispec_extend64 (d := st.nextVreg) (rn := .vreg x .int) (sg := sg) (a := ρ x) (w := w) hb)
    refine ⟨_, w', hrun, hsw, fun q hq => ?_, ?_⟩
    · simp only [upd, show ¬ (q = st.nextVreg) by omega, ↓reduceIte]
    · simp only [upd, ↓reduceIte, lo64_ofX]
      exact extW_holds (by omega) hv

theorem partOk_i64 {F : BitVec 64 → Prop} {isem : Sem} {ctx : Ctx} {st : LState} {x : Nat}
    {sg : Bool} (hxb : x < st.nextVreg) (hvt : ctx.valueType? x = some (.int 64)) :
    PartOk F isem ctx st st x sg x [] := by
  refine ⟨Nat.le_refl _, by simp, by simp, by simp, hxb, .inl rfl, ?_⟩
  intro fr ρ w ty u hdfg hx hw _
  have ht := hdfg.2 x _ _ hvt (getAs_ok hx)
  simp only [ofClif_int_width, CTy.int.injEq] at ht
  omega

/-- The two outcomes of `put_in_reg_*ext64` as one operand part. -/
theorem partOk_of {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {ctx : Ctx}
    {st st2 : LState} {x : Nat} {t : CTy} {sg : Bool} {a : V} (hxb : x < st.nextVreg)
    (hvt : ctx.valueType? x = some t)
    (h : (t.bits ≤ 32 ∧ a = .reg (st.fresh .int).1 ∧
          st2 = (st.fresh .int).2.emit (.extend (st.fresh .int).1 (.vreg x .int) sg t.bits 64)) ∨
        (t = .int 64 ∧ a = .reg (.vreg x .int) ∧ st2 = st)) :
    ∃ r ms, a = .reg (.vreg r .int) ∧ PartOk F isem ctx st st2 x sg r ms := by
  rcases h with ⟨-, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact ⟨_, _, by rw [fresh_fst], partOk_narrow hR hvt⟩
  · exact ⟨_, _, rfl, partOk_i64 hxb hvt⟩

/-! ## The back half: `madd` and the shift, and `LowerInstOk` -/

theorem fresh2_fst (s : LState) (m : MInst) :
    (((s.fresh .int).2.emit m).fresh .int).1 = .vreg (s.nextVreg + 1) .int := by
  simp [LState.fresh, LState.emit]

theorem nextVreg_fresh2 (s : LState) (m m' : MInst) :
    ((((s.fresh .int).2.emit m).fresh .int).2.emit m').nextVreg = s.nextVreg + 2 := by
  simp [LState.fresh, LState.emit]

theorem vdefs_aluRRRR_xzr (op : ALUOp3) (sz : OperandSize) (d x y : Nat) :
    vdefs (.aluRRRR op sz (.vreg d .int) (.vreg x .int) (.vreg y .int) .xzr) = [d] := rfl

theorem vdefs_aluRRImmShift (op : ALUOp) (sz : OperandSize) (d x s : Nat) :
    vdefs (.aluRRImmShift op sz (.vreg d .int) (.vreg x .int) s) = [d] := rfl

theorem vuseNums_aluRRImmShift (op : ALUOp) (sz : OperandSize) (d x s : Nat) :
    vuseNums (.aluRRImmShift op sz (.vreg d .int) (.vreg x .int) s) = [x] := rfl

/-- **`LowerInstOk` of the narrow multiply-high sequence** `ms1 ++ ms2 ++ [madd, shift]`. -/
theorem mulhiN_lowerInstOk {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {ctx : Ctx} (hR : Refines F isem) (hMR : MRStable F MR)
    {cop : Clif.BinaryOp} (hshift : cop.isShift = false) {sg : Bool} {sop : ALUOp}
    (hval : ∀ {w : Nat}, w ≤ 32 → ∀ (u v : BitVec w), ∃ R : BitVec 64,
      shiftVal sop (0 + extW sg u * extW sg v) w = some R ∧ R.setWidth w = Clif.Sem.binary cop u v)
    {st sx sy : LState} {x y r1 r2 : Nat} {ms1 ms2 : List MInst} {results : List Nat}
    (P1 : PartOk F isem ctx st sx x sg r1 ms1) (P2 : PartOk F isem ctx sx sy y sg r2 ms2)
    (hyb : y < st.nextVreg) {ty : Clif.Ty} (hw : ty.width ≤ 32) :
    LowerInstOk isem MR env cp ctx (.binary cop ty x y) results st [[.vreg (sy.nextVreg + 1) .int]]
      ((((sy.fresh .int).2.emit (.aluRRRR .mAdd .size64 (.vreg sy.nextVreg .int) (.vreg r1 .int)
        (.vreg r2 .int) .xzr)).fresh .int).2.emit (.aluRRImmShift sop .size64
          (.vreg (sy.nextVreg + 1) .int) (.vreg sy.nextVreg .int) ty.width))
      (ms1 ++ ms2 ++ [.aluRRRR .mAdd .size64 (.vreg sy.nextVreg .int) (.vreg r1 .int)
        (.vreg r2 .int) .xzr, .aluRRImmShift sop .size64 (.vreg (sy.nextVreg + 1) .int)
          (.vreg sy.nextVreg .int) ty.width]) := by
  obtain ⟨m1, -, d1, u1, lt1, or1, sem1⟩ := P1
  obtain ⟨m2, -, d2, u2, lt2, or2, sem2⟩ := P2
  apply lowerInstOk_binary hMR hshift (by rw [nextVreg_fresh2]; omega) ?_ (by omega)
  · intro fr ρ w _ hvals hdfg u v hx hy
    obtain ⟨ρ1, w1, hr1, hsw1, hag1, hlo1⟩ := sem1 fr ρ w ty u hdfg hx hw (hvals x _ (getAs_ok hx))
    have hy1 : VHolds ⟨ty, v⟩ (ρ1 y) := by rw [hag1 y hyb]; exact hvals y _ (getAs_ok hy)
    obtain ⟨ρ2, w2, hr2, hsw2, hag2, hlo2⟩ := sem2 fr ρ1 w1 ty v hdfg hy hw hy1
    have e1 : opnd .size64 (ρ2 r1) = extW sg u := by rw [opnd64_lo, hag2 r1 lt1, hlo1]
    have e2 : opnd .size64 (ρ2 r2) = extW sg v := by rw [opnd64_lo, hlo2]
    obtain ⟨R, hsv, hRv⟩ := hval hw u v
    obtain ⟨w3, hw3, hstep⟩ := seqRun_step hR
      (ms := [.aluRRImmShift sop .size64 (.vreg (sy.nextVreg + 1) .int) (.vreg sy.nextVreg .int) ty.width])
      (ρ := ρ2) (w := w2) (operands_aluRRRR_xzr .mAdd .size64 sy.nextVreg r1 r2) rfl
      (ispec_aluRRRR_xzr (op := .mAdd) (r := 0 + opnd .size64 (ρ2 r1) * opnd .size64 (ρ2 r2)) rfl)
    have hsv' : shiftVal sop (opnd .size64 (upd ρ2 sy.nextVreg
        (resX .size64 (0 + opnd .size64 (ρ2 r1) * opnd .size64 (ρ2 r2))) sy.nextVreg)) ty.width =
        some R := by
      simp only [upd, ↓reduceIte]
      rw [opnd_resX64, e1, e2]
      exact hsv
    obtain ⟨w4, hr4, hsw4⟩ := seqRun_one hR (operands_aluRRImmShift _ _ _ _ _) rfl
      (ispec_aluRRImmShift (d := sy.nextVreg + 1) (rn := .vreg sy.nextVreg .int) (w := w3)
        (show ty.width < OperandSize.bits .size64 by simp [OperandSize.bits]; omega) hsv')
    refine ⟨?_, _, w4, seqRun_append_fall_fa (seqRun_append_fall_fa hr1 hr2) (by rw [hstep, hr4]; rfl),
      hsw4.trans' (hw3.trans' (hsw2.trans' hsw1)), ?_⟩
    · intro m hm q hq
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hm
      rcases hm with (hm | hm) | rfl | rfl
      · rw [u1 m hm q hq]; exact .inr (getAs_isSome hx)
      · rw [u2 m hm q hq]; exact .inr (getAs_isSome hy)
      · rw [vuseNums_aluRRRR_xzr] at hq
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl
        · rcases or1 with rfl | h
          · exact .inr (getAs_isSome hx)
          · exact .inl h
        · rcases or2 with rfl | h
          · exact .inr (getAs_isSome hy)
          · exact .inl (by omega)
      · rw [vuseNums_aluRRImmShift, List.mem_singleton] at hq
        subst hq
        exact .inl (by omega)
    · simp only [VHolds, upd, ↓reduceIte]
      rw [resX64_setWidth_le (by omega)]
      exact hRv
  · intro m hm d hd
    rw [nextVreg_fresh2]
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with (hm | hm) | rfl | rfl
    · have := d1 m hm d hd; omega
    · have := d2 m hm d hd; omega
    · rw [vdefs_aluRRRR_xzr, List.mem_singleton] at hd; omega
    · rw [vdefs_aluRRImmShift, List.mem_singleton] at hd; omega


set_option maxRecDepth 20000 in
/-- **`smulhi_fits_in_32`** (`lower.isle:1059`, `smulhi` at i8/i16/i32 → `sxt`, `sxt`, `madd`, `asr`). -/
theorem smulhi_fits_in_32_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_1059 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn hvb _hfirst
    hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 100 := ⟨n - 100, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, -, -, -⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 1) (cop := .smulhi) rfl hp.t2363 term_2363_kind
      variantNames_Smulhi rfl hmatch
  cases Classical.em (ty.width ≤ 32) with
  | inr hnw => rw [match_1059_ty hp ctx st tr m' hi hhead hnw hd] at hmatch; cases hmatch
  | inl hw =>
  rw [match_1059 hp ctx st tr m' hi hhead hw hd] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  obtain ⟨envB, sB, hbinds, -⟩ := evalExpr_let_inv (n := N + 99) heval
  obtain ⟨v1, sx, hv1, -, hbinds'⟩ := evalBinds_cons_inv hbinds
  obtain ⟨v2, sy, hv2, -, -⟩ := evalBinds_cons_inv hbinds'
  obtain ⟨vs1, sa, ha1, happ1⟩ := evalExpr_term_inv hv1
  rw [evalArgs_var1 (n := N + 95) (v := .value x) (by simp)] at ha1
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at ha1
  obtain ⟨rfl, rfl⟩ := ha1
  obtain ⟨sxs, sxt⟩ := sx
  obtain ⟨t1, hvt1, hrx, hc1⟩ := sext64_inv hp ctx hco hctx st tr (N + 37) happ1
  have hxb : x < st.nextVreg := hvb x _ hrx
  obtain ⟨r1, ms1, rfl, P1⟩ := partOk_of (F := F) (isem := isem) hR hxb hvt1 hc1
  obtain ⟨vs2, sb, ha2, happ2⟩ := evalExpr_term_inv hv2
  rw [evalArgs_var1 (n := N + 94) (v := .value y) (by simp)] at ha2
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at ha2
  obtain ⟨rfl, rfl⟩ := ha2
  obtain ⟨sys, syt⟩ := sy
  obtain ⟨t2, hvt2, hry, hc2⟩ := sext64_inv hp ctx hco hctx sxs sxt (N + 36) happ2
  have hyb : y < st.nextVreg := hvb y _ hry
  obtain ⟨r2, ms2, rfl, P2⟩ := partOk_of (F := F) (isem := isem) hR
    (Nat.lt_of_lt_of_le hyb P1.1) hvt2 hc2
  obtain ⟨tr'', he⟩ := rhs_1059 hp ctx hco st tr N hw happ1 happ2
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  simp only [fresh_fst]
  refine ⟨ms1 ++ ms2 ++ [_, _], _, ?_, rfl,
    mulhiN_lowerInstOk hR hMR (cop := .smulhi) rfl (sg := true) (sop := .asr)
      (fun hw u v => ⟨_, rfl, mulhi_narrow_s hw u v⟩) P1 P2 hyb hw⟩
  simp only [LState.emit, LState.fresh]
  rw [P2.2.1, P1.2.1]
  simp [Array.append_assoc]

set_option maxRecDepth 20000 in
/-- **`umulhi_fits_in_32`** (`lower.isle:1071`, `umulhi` at i8/i16/i32 → `uxt`, `uxt`, `madd`, `lsr`). -/
theorem umulhi_fits_in_32_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_1071 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn hvb _hfirst
    hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 100 := ⟨n - 100, by omega⟩
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, -, -, -⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 1) (cop := .umulhi) rfl hp.t2362 term_2362_kind
      variantNames_Umulhi rfl hmatch
  cases Classical.em (ty.width ≤ 32) with
  | inr hnw => rw [match_1071_ty hp ctx st tr m' hi hhead hnw hd] at hmatch; cases hmatch
  | inl hw =>
  rw [match_1071 hp ctx st tr m' hi hhead hw hd] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  obtain ⟨envB, sB, hbinds, -⟩ := evalExpr_let_inv (n := N + 99) heval
  obtain ⟨v1, sx, hv1, -, hbinds'⟩ := evalBinds_cons_inv hbinds
  obtain ⟨v2, sy, hv2, -, -⟩ := evalBinds_cons_inv hbinds'
  obtain ⟨vs1, sa, ha1, happ1⟩ := evalExpr_term_inv hv1
  rw [evalArgs_var1 (n := N + 95) (v := .value x) (by simp)] at ha1
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at ha1
  obtain ⟨rfl, rfl⟩ := ha1
  obtain ⟨sxs, sxt⟩ := sx
  obtain ⟨t1, hvt1, hrx, hc1⟩ := zext64_inv hp ctx hco hctx st tr (N + 37) happ1
  have hxb : x < st.nextVreg := hvb x _ hrx
  obtain ⟨r1, ms1, rfl, P1⟩ := partOk_of (F := F) (isem := isem) hR hxb hvt1 hc1
  obtain ⟨vs2, sb, ha2, happ2⟩ := evalExpr_term_inv hv2
  rw [evalArgs_var1 (n := N + 94) (v := .value y) (by simp)] at ha2
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at ha2
  obtain ⟨rfl, rfl⟩ := ha2
  obtain ⟨sys, syt⟩ := sy
  obtain ⟨t2, hvt2, hry, hc2⟩ := zext64_inv hp ctx hco hctx sxs sxt (N + 36) happ2
  have hyb : y < st.nextVreg := hvb y _ hry
  obtain ⟨r2, ms2, rfl, P2⟩ := partOk_of (F := F) (isem := isem) hR
    (Nat.lt_of_lt_of_le hyb P1.1) hvt2 hc2
  obtain ⟨tr'', he⟩ := rhs_1071 hp ctx hco st tr N hw happ1 happ2
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  simp only [fresh_fst]
  refine ⟨ms1 ++ ms2 ++ [_, _], _, ?_, rfl,
    mulhiN_lowerInstOk hR hMR (cop := .umulhi) rfl (sg := false) (sop := .lsr)
      (fun hw u v => ⟨_, rfl, mulhi_narrow_u hw u v⟩) P1 P2 hyb hw⟩
  simp only [LState.emit, LState.fresh]
  rw [P2.2.1, P1.2.1]
  simp [Array.append_assoc]

end Backend.Proof
