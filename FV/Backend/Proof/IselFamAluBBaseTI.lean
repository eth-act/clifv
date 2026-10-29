module

public import FV.Backend.Proof.IselFamAluBBase
public import FV.Backend.Proof.IselBaseTI

@[expose] public section

/-!
# `IselFamAluBBase` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselFamAluBBase`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
section Run
variable {F : BitVec 64 → Prop} {isem : Sem}
end Run
/-- **Front end of a unary root rule** `(inst_data_value tyPat (Unary (O) x))`: the matched
instruction is the unary operation `cop` of the opcode `O`, at a type `ty` (not `i128`, not
`bswap.i8`), with data `Unary O x` and result type `ty`. -/
theorem unary_frontTI {p : Program} (hp : Data p) {r : Rule} {cop : Clif.UnaryOp} {n : String}
    {opT : TermId} {to : Term} {ko : Nat} {tyPat : Pattern} {rest : List Pattern}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2476 (.term 151 opT [] :: rest)]])
    (hto : termOf p opT = .ok to) (hko : to.kind = .enumVariant ko)
    (hname : (variantNames 151)[ko]? = some n) (hcop : unaryOpcode cop = some n)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {cfg : Config} {m : Nat} {s s1 : LState × Array RuleId} {env : Interp.Env V}
    (h : (matchRule p (sem ctx) cfg (m + 1) r [.inst ii]).run s = .ok (some env, s1)) :
    ∃ ty x, inst = .unary cop ty x ∧ eTy ty = true ∧ (cop = .bswap → ty ≠ .i8) ∧
      info.data = .data 152 29 [.data 151 ko [], .value x] ∧
      info.resTys.head? = some (.int ty.width) := by
  obtain ⟨info', fs, hi', hd⟩ := root_match_data hp ctx hargs hp.t2476 term_2476_kind hto hko h
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hc
  rw [hd] at hdat
  obtain ⟨hf, ho⟩ := instData_inv_names hdat
  rw [variantNames_Unary] at hf
  rw [hname] at ho
  have hnm : instNames inst = ("Unary", n) :=
    Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm
  obtain ⟨ty, x, rfl⟩ := instNames_unary hcop hnm
  obtain ⟨hety, hb, hfs⟩ := instData_unary_data hcop hdat
  subst hfs
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii info _ hi hc
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  exact ⟨ty, x, rfl, hety, hb, hd, by rw [hres]; simp [ofClif_int_width (isInt_of_eTy hety)]⟩

section Facts
variable (op : ALUOp) (bop : BitOp) (sz : OperandSize) (d x y : Nat)
end Facts
/-- **Template: a unary root rule.** Rule `r` with pattern `(inst_data_value tyPat (Unary (O)
x))` for the opcode of `cop`: when it matches, the type's width satisfies `P` (`hmatch`); its
right-hand side emits `code w b x` (`b` = the first fresh vreg) allocating `k` fresh vregs and
returns the fresh vreg `res w b` (`hrhs`), or fails when `x` has no register (`hnone`). The
code defines only its fresh vregs and reads `x` and fresh vregs; `hsem` is its meaning. -/
theorem unary_ruleOkTI {p : Program} (hp : Data p) {r : Rule} {cop : Clif.UnaryOp} {n : String}
    {opT : TermId} {to : Term} {ko : Nat} {tyPat : Pattern} {rest : List Pattern}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2476 (.term 151 opT [] :: rest)]])
    (hto : termOf p opT = .ok to) (hko : to.kind = .enumVariant ko)
    (hname : (variantNames 151)[ko]? = some n) (hcop : unaryOpcode cop = some n)
    (E : Nat → Nat → Interp.Env V) (P : Nat → Prop) (Q : Nat → Option CTy → Prop)
    (k : Nat → Option CTy → Nat) (code : Nat → Option CTy → Nat → Nat → List MInst)
    (res : Nat → Option CTy → Nat → Nat)
    (hmatch : ∀ (ctx : Ctx) (cfg : Config) ii (info : IInfo) w x st tr m env' s1,
      ctx.insts[ii]? = some info → info.resTys.head? = some (.int w) → w ≤ 64 →
      info.data = .data 152 29 [.data 151 ko [], .value x] →
      (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
        ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s')) →
      (matchRule p (sem ctx) cfg (m + 2) r [.inst ii]).run (st, tr) = .ok (some env', s1) →
      env' = E w x ∧ s1 = (st, tr) ∧ P w)
    (hrhs : ∀ (ctx : Ctx) (cfg : Config) x w (st : LState) tr n,
      cfg.checkOverlap = false → ctx.valueReg? x = some (.vreg x .int) → w ≤ 64 → P w →
      Q w (ctx.valueType? x) →
      ∃ (tr' : Array RuleId) (st'' : LState), (evalExpr p (sem ctx) cfg (n + 40) r.rhs
          (E w x)).run (st, tr) =
        .ok (some (.regsVec [[.vreg (res w (ctx.valueType? x) st.nextVreg) .int]]), (st'', tr')) ∧
        st''.emitted = st.emitted ++ (code w (ctx.valueType? x) st.nextVreg x).toArray ∧
        st''.nextVreg = st.nextVreg + k w (ctx.valueType? x))
    (hnone : ∀ (ctx : Ctx) (cfg : Config) x w st tr n v s',
      (ctx.valueReg? x = none ∨ ¬ Q w (ctx.valueType? x)) →
      (evalExpr p (sem ctx) cfg (n + 40) r.rhs (E w x)).run (st, tr) ≠ .ok (some v, s'))
    (hres : ∀ w T b, b ≤ res w T b)
    (hdefs : ∀ w T b x, ∀ mi ∈ code w T b x, ∀ d ∈ vdefs mi, b ≤ d ∧ d < b + k w T)
    (huses : ∀ w T b x, ∀ mi ∈ code w T b x, ∀ u ∈ vuseNums mi, b ≤ u ∨ u = x)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (hMR : MRStable F MR)
    (hsem : ∀ (ty : Clif.Ty) (T : Option CTy) (b x : Nat) (ρ : Nat → CV) (u : BitVec ty.width),
      eTy ty = true → (cop = .bswap → ty ≠ .i8) → P ty.width → Q ty.width T →
      (T = none ∨ T = some (.int ty.width)) → x < b → VHolds ⟨ty, u⟩ (ρ x) →
      ∃ ρ', PRun F isem (code ty.width T b x) ρ ρ' ∧
        VHolds ⟨ty, Clif.Sem.unary cop u⟩ (ρ' (res ty.width T b))) :
    LowerRuleOkTI isem MR env cp p r := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb hfirst
      hmatch' heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 40 := ⟨n - 40, by omega⟩
  obtain ⟨ty, x, rfl, hety, hbs, hd, hhead⟩ :=
    unary_frontTI hp hargs hto hko hname hcop hctx hi hc (m := m' + 1) hmatch'
  have hw := eTy_width hety
  obtain ⟨rfl, rfl, hP⟩ :=
    hmatch ctx cfg ii info ty.width x st tr m' env' s1 hi hhead hw hd hfirst hmatch'
  cases hrx : ctx.valueReg? x with
  | none => exact absurd heval (hnone ctx cfg x ty.width st tr n' out (st', tr') (.inl hrx))
  | some rx =>
  have ex := hctx.valueRegI x rx hrx
  subst ex
  have hxlt := hvb x _ hrx
  by_cases hQ : Q ty.width (ctx.valueType? x)
  case neg => exact absurd heval (hnone ctx cfg x ty.width st tr n' out (st', tr') (.inr hQ))
  obtain ⟨tr'', st'', he, hem, hnx⟩ := hrhs ctx cfg x ty.width st tr n' hco hrx hw hP hQ
  rw [he] at heval
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
  obtain ⟨rfl, rfl, -⟩ := heval
  refine ⟨code ty.width (ctx.valueType? x) st.nextVreg x, _, hem, rfl, ?_⟩
  refine lowerInstOk_one_fb hMR (by omega) (fun mi hmi d hd => ?_) rfl ?_
  · have := hdefs _ _ _ _ mi hmi d hd; omega
  intro fr cm ρ vals cm' _ hvals hdfg ho
  obtain ⟨u, hu, rfl, rfl⟩ := evalInst_unary_ok ho
  have hxv := getAs_ok hu
  have hT : ctx.valueType? x = none ∨ ctx.valueType? x = some (.int ty.width) := by
    cases hT : ctx.valueType? x with
    | none => exact .inl rfl
    | some t =>
      have := hdfg.2 x t _ hT hxv
      exact .inr (by rw [← this, ofClif_int_width (isInt_of_eTy hety)])
  obtain ⟨ρ', hrun, hheld⟩ :=
    hsem ty (ctx.valueType? x) st.nextVreg x ρ u hety hbs hP hQ hT hxlt (hvals x _ hxv)
  refine ⟨rfl, usesOk_of [x] ?_ ?_, .inl (hres _ _ _), _, ρ', rfl, hrun, hheld⟩
  · intro mi hmi u hu
    rcases huses _ _ _ _ mi hmi u hu with h | h
    · exact .inl h
    · exact .inr (by simp [h])
  · intro y hy
    simp only [List.mem_singleton] at hy
    subst hy
    simp [hxv]

end Backend.Proof
namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
theorem unary_ruleOkTI' {p : Program} (hp : Data p) {r : Rule} {cop : Clif.UnaryOp} {n : String}
    {opT : TermId} {to : Term} {ko : Nat} {tyPat : Pattern} {rest : List Pattern}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2476 (.term 151 opT [] :: rest)]])
    (hto : termOf p opT = .ok to) (hko : to.kind = .enumVariant ko)
    (hname : (variantNames 151)[ko]? = some n) (hcop : unaryOpcode cop = some n)
    (E : Nat → Nat → Interp.Env V) (P : Nat → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (hMR : MRStable F MR)
    (hmatch : ∀ (ctx : Ctx) (cfg : Config) ii (info : IInfo) w x st tr m env' s1,
      ctx.insts[ii]? = some info → info.resTys.head? = some (.int w) → w ≤ 64 →
      info.data = .data 152 29 [.data 151 ko [], .value x] →
      (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
        ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s')) →
      (matchRule p (sem ctx) cfg (m + 2) r [.inst ii]).run (st, tr) = .ok (some env', s1) →
      env' = E w x ∧ s1 = (st, tr) ∧ P w)
    (hnone : ∀ (ctx : Ctx) (cfg : Config) x w st tr n v s', ctx.valueReg? x = none →
      ctx.valueType? x = none →
      (evalExpr p (sem ctx) cfg (n + 200) r.rhs (E w x)).run (st, tr) ≠ .ok (some v, s'))
    (hrhs : ∀ (ctx : Ctx) (cfg : Config) x w (st : LState) tr n v s',
      cfg.checkOverlap = false → ctx.valueReg? x = some (.vreg x .int) → x < st.nextVreg →
      w ≤ 64 → P w →
      (evalExpr p (sem ctx) cfg (n + 200) r.rhs (E w x)).run (st, tr) = .ok (some v, s') →
      ∃ ms d, v = .regsVec [[.vreg d .int]] ∧ CodeShape st s'.1 ms d x ∧
        ∀ (ty : Clif.Ty), ty.width = w → eTy ty = true → (cop = .bswap → ty ≠ .i8) →
        (ctx.valueType? x = none ∨ ctx.valueType? x = some (.int w)) →
        ∀ (ρ : Nat → CV) (u : BitVec ty.width), VHolds ⟨ty, u⟩ (ρ x) →
        ∃ ρ', PRun F isem ms ρ ρ' ∧ VHolds ⟨ty, Clif.Sem.unary cop u⟩ (ρ' d)) :
    LowerRuleOkTI isem MR env cp p r := by
  intro f ctx hctxT ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb hfirst
      hmatch' heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 200 := ⟨n - 200, by omega⟩
  obtain ⟨ty, x, rfl, hety, hbs, hd, hhead⟩ :=
    unary_frontTI hp hargs hto hko hname hcop hctx hi hc (m := m' + 1) hmatch'
  have hw := eTy_width hety
  obtain ⟨rfl, rfl, hP⟩ :=
    hmatch ctx cfg ii info ty.width x st tr m' env' s1 hi hhead hw hd hfirst hmatch'
  cases hrx : ctx.valueReg? x with
  | none =>
    have hT : ctx.valueType? x = none := by
      cases hT : ctx.valueType? x with
      | none => rfl
      | some t => rw [hctx.typedRegI x t hT] at hrx; cases hrx
    exact absurd heval (hnone ctx cfg x ty.width st tr n' out (st', tr') hrx hT)
  | some rx =>
  have ex := hctx.valueRegI x rx hrx
  subst ex
  have hxlt := hvb x _ hrx
  obtain ⟨ms, d, rfl, hsh, hsem⟩ :=
    hrhs ctx cfg x ty.width st tr n' out (st', tr') hco hrx hxlt hw hP heval
  refine ⟨ms, _, hsh.emitted, rfl, ?_⟩
  refine lowerInstOk_one_fb hMR hsh.mono hsh.defs rfl ?_
  intro fr cm ρ vals cm' _ hvals hdfg ho
  obtain ⟨u, hu, rfl, rfl⟩ := evalInst_unary_ok ho
  have hxv := getAs_ok hu
  have hT : ctx.valueType? x = none ∨ ctx.valueType? x = some (.int ty.width) := by
    cases hT : ctx.valueType? x with
    | none => exact .inl rfl
    | some t =>
      have := hdfg.2 x t _ hT hxv
      exact .inr (by rw [← this, ofClif_int_width (isInt_of_eTy hety)])
  obtain ⟨ρ', hrun, hheld⟩ := hsem ty rfl hety hbs hT ρ u (hvals x _ hxv)
  refine ⟨rfl, usesOk_of [x] ?_ ?_, .inl hsh.res, _, ρ', rfl, hrun, hheld⟩
  · intro mi hmi u hu
    rcases hsh.uses mi hmi u hu with h | h
    · exact .inl h
    · exact .inr (by simp [h])
  · intro y hy
    simp only [List.mem_singleton] at hy
    subst hy
    simp [hxv]

end Backend.Proof
