import FV.Backend.Proof.IselFamily
import FV.Backend.Proof.IselBaseTI

/-!
# `IselFamily` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselFamily`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
/-- **Template: a two-register ALU root rule.** A root rule whose pattern is
`(inst_data_value tyPat (Binary (O) (x y)))` for the opcode of `cop`, whose match phase and
right-hand side evaluate as `hmatch` / `hrhs` / `hnone` say (emit one `AluRRR aop` of the
operand size of the type, result in a fresh vreg), satisfies `LowerRuleOkTI` whenever `aop` is
`cop` on the low bits (`aluVal_holds`). A rule of this family costs its three forward
lemmas (`IselRulesALU`). -/
theorem aluRR_ruleOkTI {p : Program} (hp : Data p) {r : Rule} {cop : Clif.BinaryOp} {aop : ALUOp}
    {n : String} {opT : TermId} {to : Term} {ko : Nat} {tyPat : Pattern} {rest : List Pattern}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2449 (.term 151 opT [] :: rest)]])
    (hto : termOf p opT = .ok to) (hko : to.kind = .enumVariant ko)
    (hname : (variantNames 151)[ko]? = some n) (hcop : binaryOpcode cop = some n)
    (hshift : cop.isShift = false)
    (hop : (aop, cop) = (.add, .iadd) ∨ (aop, cop) = (.sub, .isub) ∨ (aop, cop) = (.and, .band) ∨
      (aop, cop) = (.orr, .bor) ∨ (aop, cop) = (.eor, .bxor))
    (hmatch : ∀ (ctx : Ctx) (cfg : Config) ii (info : IInfo) w x y st tr m,
      ctx.insts[ii]? = some info → info.resTys.head? = some (.int w) → w ≤ 64 →
      info.data = .data 152 2 [.data 151 ko [], .values [x, y]] →
      (matchRule p (sem ctx) cfg (m + 2) r [.inst ii]).run (st, tr) =
        .ok (some (env3 (.ty (.int w)) (.value x) (.value y)), (st, tr)))
    (hrhs : ∀ (ctx : Ctx) (cfg : Config) x y w (rx ry : Reg) (st : LState) tr n,
      cfg.checkOverlap = false → ctx.valueReg? x = some rx → ctx.valueReg? y = some ry → w ≤ 64 →
      ∃ tr', (evalExpr p (sem ctx) cfg (n + 40) r.rhs (env3 (.ty (.int w)) (.value x) (.value y))).run
          (st, tr) =
        .ok (some (.regsVec [[(st.fresh .int).1]]),
          ((st.fresh .int).2.emit (.aluRRR aop (if w ≤ 32 then .size32 else .size64)
            (st.fresh .int).1 rx ry), tr')))
    (hnone : ∀ (ctx : Ctx) (cfg : Config) x y w st tr n v s',
      (ctx.valueReg? x = none ∨ ctx.valueReg? y = none) →
      (evalExpr p (sem ctx) cfg (n + 40) r.rhs (env3 (.ty (.int w)) (.value x) (.value y))).run
        (st, tr) ≠ .ok (some v, s')) :
    ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program),
      Refines F isem → MRStable F MR → LowerRuleOkTI isem MR env cp p r := by
  intro F isem MR env cp hR hMR f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out
      st' tr' hm hn _hvb _hfirst hmatch' heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  -- 1. the instruction
  obtain ⟨info', fs, hi', hd⟩ := root_match_data hp ctx hargs hp.t2449 term_2449_kind hto hko
    (m := m' + 1) hmatch'
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hc
  rw [hd] at hdat
  obtain ⟨hf, ho⟩ := instData_inv_names hdat
  rw [variantNames_Binary] at hf
  rw [hname] at ho
  have hnm : instNames inst = ("Binary", n) :=
    Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm
  obtain ⟨ty, x, y, rfl⟩ := instNames_binary hcop hnm
  obtain ⟨hety, hfs⟩ := instData_binary_data hcop hdat
  subst hfs
  have hw := eTy_width hety
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii info _ hi hc
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  have hhead : info.resTys.head? = some (.int ty.width) := by
    rw [hres]; simp [ofClif_int_width (isInt_of_eTy hety)]
  -- 2. determinism: the environment and the emitted code
  rw [hmatch ctx cfg ii info ty.width x y st tr m' hi hhead hw hd] at hmatch'
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch'
  obtain ⟨rfl, rfl⟩ := hmatch'
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (hnone ctx cfg x y ty.width st tr n' out (st', tr') (.inl hrx))
  | some rx =>
  cases hry : ctx.valueReg? y with
  | none => exact absurd heval (hnone ctx cfg x y ty.width st tr n' out (st', tr') (.inr hry))
  | some ry =>
  have ex := hctx.valueRegI x rx hrx
  have ey := hctx.valueRegI y ry hry
  subst ex ey
  obtain ⟨tr'', he⟩ := hrhs ctx cfg x y ty.width _ _ st tr n' hco hrx hry hw
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  -- 3. the meaning
  let sz : OperandSize := if ty.width ≤ 32 then .size32 else .size64
  have hsz : ty.width ≤ sz.bits := by
    by_cases h32 : ty.width ≤ 32 <;> simp [sz, h32, OperandSize.bits] <;> omega
  refine ⟨[.aluRRR aop sz (.vreg st.nextVreg .int) (.vreg x .int) (.vreg y .int)],
    [[.vreg st.nextVreg .int]], ?_, rfl, ?_⟩
  · show st.emitted.push _ = st.emitted ++ [_].toArray
    rw [Array.push_eq_append]
    rfl
  refine ⟨by simp [LState.emit, LState.fresh], ?_, ?_⟩
  · intro mi hmi d hdm
    simp only [List.mem_singleton] at hmi
    subst hmi
    have : d = st.nextVreg := by simpa [vdefs, operands_aluRRR, Operand.isDef] using hdm
    subst this
    simp [LState.emit, LState.fresh]
  intro fr cm ρ w _ hvals _ hmr
  have hout : instOutcome env cp fr cm (.binary cop ty x y) = Clif.evalInst fr cm (.binary cop ty x y) := rfl
  rw [hout]
  simp only [Clif.evalInst, hshift, Bool.false_eq_true, ↓reduceIte]
  cases hx : fr.getAs x ty with
  | trap c => simp [bind, Clif.Res.bind, explicitTrapInst]
  | stuck msg => simp [bind, Clif.Res.bind, explicitTrapInst]
  | ok u =>
  cases hy : fr.getAs y ty with
  | trap c => simp [bind, Clif.Res.bind, explicitTrapInst]
  | stuck msg => simp [bind, Clif.Res.bind, explicitTrapInst]
  | ok v =>
  simp only [bind, Clif.Res.bind, pure]
  have hxv := getAs_ok hx
  have hyv := getAs_ok hy
  obtain ⟨res, hres, hheld⟩ := aluVal_holds hop hsz (hvals x _ hxv) (hvals y _ hyv)
  obtain ⟨w', hrun, hsame⟩ := seqRun_aluRRR hR (d := st.nextVreg) (w := w) hres
  refine ⟨?_, _, w', hrun, .inr ⟨rfl, ?_⟩, hMR _ _ _ _ hsame.nf hmr⟩
  · intro mi hmi u hu
    simp only [List.mem_singleton] at hmi
    subst hmi
    have : u = x ∨ u = y := by simpa [vuseNums, operands_aluRRR, Operand.isUse] using hu
    rcases this with rfl | rfl
    · exact .inr (by simp [hxv])
    · exact .inr (by simp [hyv])
  · intro j rs val hrs hval
    match j, hrs, hval with
    | 0, hrs, hval =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hrs hval
      subst hrs; subst hval
      exact ⟨st.nextVreg, .int, rfl, .inl (Nat.le_refl _), by simpa [upd] using hheld⟩
    | _ + 1, hrs, _ => simp at hrs

end Backend.Proof
