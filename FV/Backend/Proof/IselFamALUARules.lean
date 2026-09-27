import FV.Backend.Proof.IselRulesALUA
import FV.Backend.Proof.IselFamilyALU

/-!
# Family A root rules: `LowerRuleOk` at every width i8..i64

Each theorem: match inversion (`binary_root_inv`, `values2_match_inv`, `defInst_match_inv`)
names the instruction and the looked-through definitions; the forward lemmas
(`IselRulesALUA`) fix the environment and the emitted code; `lowerInstOk_binary` reduces the
obligation to the value-level meaning of the code, which `DFGCons` (the looked-through values)
and the width lemmas (`IselFamALUA`) discharge.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

theorem vuseNums_aluRRImm12 (op : ALUOp) (sz : OperandSize) (d x : Nat) (i : Imm12) :
    vuseNums (.aluRRImm12 op sz (.vreg d .int) (.vreg x .int) i) = [x] := rfl

theorem vdefs_aluRRImm12 (op : ALUOp) (sz : OperandSize) (d x : Nat) (i : Imm12) :
    vdefs (.aluRRImm12 op sz (.vreg d .int) (.vreg x .int) i) = [d] := rfl

theorem emitted_push (st : LState) (m : MInst) :
    ((st.fresh .int).2.emit m).emitted = st.emitted ++ [m].toArray := by
  show st.emitted.push m = _
  rw [Array.push_eq_append]

theorem nextVreg_fresh_emit (st : LState) (m : MInst) :
    ((st.fresh .int).2.emit m).nextVreg = st.nextVreg + 1 := by
  simp [LState.emit, LState.fresh]

theorem fresh_fst (st : LState) : (st.fresh .int).1 = .vreg st.nextVreg .int := by
  simp [LState.fresh]

/-- **`iadd_imm12_right`** (`lower.isle:90`, `(iadd x (iconst k))` with `k` an `Imm12` →
`add x, #k`), i8..i64. -/
theorem iadd_imm12_right_ok {p : Program} (hp : Data p) (F : BitVec 64 → Prop) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) : LowerRuleOk isem MR env cp p rule_lower_90 := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn _hvb hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  -- the instruction and the looked-through `iconst`
  obtain ⟨ty, x, y, e0, e1, rfl, hd, hhead, hw, hrest, -⟩ :=
    binary_root_inv hp hctx hi hc (m := m' + 1) (cop := .iadd) rfl hp.t2357 term_2357_kind variantNames_Iadd rfl
      hmatch
  obtain ⟨e2, -, hpy⟩ := values2_match_inv hp ctx hrest
  obtain ⟨j, infoj, fs, e3, hj, hij, hdj, hfs⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hpy
  obtain ⟨cl, hcl, hdat⟩ := ctxInv_clif hctx hj hij
  rw [hdj] at hdat
  obtain ⟨ty', c, rfl, rfl⟩ := instData_iconst_inv hdat
  obtain ⟨imm, himm, -⟩ := imm12_args_inv hp ctx hfs
  -- determinism: environment and code
  rw [match_90 hp ctx hi hhead hw hd hj hij hdj himm st tr m'] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (rhs_90_none hp ctx hrx st tr n' out (st', tr'))
  | some rx =>
  have ex := hctx.valueReg x rx hrx
  subst ex
  obtain ⟨tr'', he⟩ := rhs_90 hp ctx hco hrx hw st tr n'
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  rw [fresh_fst]
  refine ⟨[.aluRRImm12 .add (szOf ty.width) (.vreg st.nextVreg .int) (.vreg x .int) imm],
    [[.vreg st.nextVreg .int]], ?_, rfl, ?_⟩
  · rw [← fresh_fst, emitted_push]
  apply lowerInstOk_binary hMR rfl (by rw [nextVreg_fresh_emit]; omega) ?_ (Nat.le_refl _)
  · intro fr ρ w _ hvals hdfg u v hx hy
    have hxv := getAs_ok hx
    have hyv := getAs_ok hy
    -- the `iconst`'s value
    have hval := dfg_single hdfg hj hij hcl rfl hyv (a := ⟨ty', c⟩)
      (fun vals cm cm' h => by rw [evalInst_iconst] at h; cases h; rfl)
    cases hval
    have hk := u64_imm64OfIconst hw v
    rw [hk] at himm
    obtain ⟨hiv, hib⟩ := imm12_ofNat_value himm (Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by omega) hw))
    refine ⟨?_, ?_⟩
    · intro mi hmi a ha
      simp only [List.mem_singleton] at hmi
      subst hmi
      rw [vuseNums_aluRRImm12, List.mem_singleton] at ha
      subst ha
      exact .inr (by simp [hxv])
    · obtain ⟨w', hrun, hsw⟩ := seqRun_one (d := st.nextVreg) (ρ := ρ) (w := w) hR
        (operands_aluRRImm12 _ _ _ _ _) rfl (ispec_aluRRImm12_add hib)
      refine ⟨_, w', hrun, hsw, ?_⟩
      simp only [upd, ↓reduceIte]
      rw [hiv]
      exact holds_add_imm (szOf_bits hw) (hvals x _ hxv)
  · intro mi hmi d hdm
    simp only [List.mem_singleton] at hmi
    subst hmi
    rw [vdefs_aluRRImm12, List.mem_singleton] at hdm
    subst hdm
    rw [nextVreg_fresh_emit]
    omega

end Backend.Proof
