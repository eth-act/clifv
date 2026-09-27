import FV.Backend.Proof.IselTermsImm
import FV.Backend.Proof.IselFamAluBMisc

/-!
# Family B: template for the shift and rotate root rules

A shift/rotate root rule `(inst_data_value tyPat (Binary (O) (x y)))` emits straight-line code
whose meaning may depend on the operand's `value_type` (`put_in_reg_zext32`, …) and on the
definition of the amount (`do_shift_imm` looks through an `iconst`): `shift_ruleOk` takes, per
evaluation of the right-hand side, the emitted code's shape (`CodeShapeU`: fresh defs, reads
of fresh vregs, `x` or `y`) and its meaning in every frame the driver runs it in (with the
frame's `DFGCons`), and proves `LowerRuleOk`. The CLIF amount is the amount operand's value at
its own type (`Clif.Sem.shiftAmt`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-- Code `ms`, emitted from `st` to `st'`, defines only fresh vregs, reads fresh vregs or the
vregs `xs`, and its result `d` is fresh. -/
structure CodeShapeU (st st' : LState) (ms : List MInst) (d : Nat) (xs : List Nat) : Prop where
  emitted : st'.emitted = st.emitted ++ ms.toArray
  mono : st.nextVreg ≤ st'.nextVreg
  res : st.nextVreg ≤ d
  defs : ∀ mi ∈ ms, ∀ e ∈ vdefs mi, st.nextVreg ≤ e ∧ e < st'.nextVreg
  uses : ∀ mi ∈ ms, ∀ u ∈ vuseNums mi, st.nextVreg ≤ u ∨ u ∈ xs

theorem evalInst_shift_ok {fr : Clif.Frame} {cm cm' : Clif.Mem} {op : Clif.BinaryOp}
    (hsh : op.isShift = true) {ty : Clif.Ty} {x y : Nat} {vals : List Clif.Val}
    (h : Clif.evalInst fr cm (.binary op ty x y) = .ok (vals, cm')) :
    ∃ u yv r, fr.getAs x ty = .ok u ∧ fr.regs y = some yv ∧ Clif.Sem.shift op u yv.bits = some r ∧
      vals = [⟨ty, r⟩] ∧ cm' = cm := by
  simp only [Clif.evalInst, hsh, ↓reduceIte] at h
  cases hx : fr.getAs x ty with
  | trap c => rw [hx] at h; cases h
  | stuck m => rw [hx] at h; cases h
  | ok u =>
    rw [hx] at h
    simp only [bind, Clif.Res.bind] at h
    cases hy : fr.regs y with
    | none => simp [Clif.Frame.get, hy, Clif.Res.ofOption] at h
    | some yv =>
      simp only [Clif.Frame.get, hy, Clif.Res.ofOption] at h
      cases hr : Clif.Sem.shift op u yv.bits with
      | none => simp [hr] at h
      | some r =>
        simp only [hr, pure] at h
        cases h
        exact ⟨u, yv, r, rfl, rfl, hr, rfl, rfl⟩

/-- **Front end of a binary root rule**: the matched instruction is `cop ty x y`. -/
theorem binary_front {p : Program} (hp : Data p) {r : Rule} {cop : Clif.BinaryOp} {n : String}
    {opT : TermId} {to : Term} {ko : Nat} {tyPat : Pattern} {rest : List Pattern}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2449 (.term 151 opT [] :: rest)]])
    (hto : termOf p opT = .ok to) (hko : to.kind = .enumVariant ko)
    (hname : (variantNames 151)[ko]? = some n) (hcop : binaryOpcode cop = some n)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {cfg : Config} {m : Nat} {s s1 : LState × Array RuleId} {env : Interp.Env V}
    (h : (matchRule p (sem ctx) cfg (m + 1) r [.inst ii]).run s = .ok (some env, s1)) :
    ∃ ty x y, inst = .binary cop ty x y ∧ eTy ty = true ∧
      info.data = .data 152 2 [.data 151 ko [], .values [x, y]] ∧
      info.resTys.head? = some (.int ty.width) := by
  obtain ⟨info', fs, hi', hd⟩ := root_match_data hp ctx hargs hp.t2449 term_2449_kind hto hko h
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
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii info _ hi hc
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  exact ⟨ty, x, y, rfl, hety, hd, by rw [hres]; simp [ofClif_int_width]⟩

/-- **Template: a shift/rotate root rule.** -/
theorem shift_ruleOk {p : Program} (hp : Data p) {r : Rule} {cop : Clif.BinaryOp} {n : String}
    (hshift : cop.isShift = true)
    {opT : TermId} {to : Term} {ko : Nat} {tyPat : Pattern} {rest : List Pattern}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2449 (.term 151 opT [] :: rest)]])
    (hto : termOf p opT = .ok to) (hko : to.kind = .enumVariant ko)
    (hname : (variantNames 151)[ko]? = some n) (hcop : binaryOpcode cop = some n)
    (E : Nat → Nat → Nat → Interp.Env V) (P : Nat → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (hMR : MRStable F MR)
    (hmatch : ∀ (ctx : Ctx) (cfg : Config) ii (info : IInfo) w x y st tr m env' s1,
      ctx.insts[ii]? = some info → info.resTys.head? = some (.int w) → w ≤ 64 →
      info.data = .data 152 2 [.data 151 ko [], .values [x, y]] →
      (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
        ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s')) →
      (matchRule p (sem ctx) cfg (m + 10) r [.inst ii]).run (st, tr) = .ok (some env', s1) →
      env' = E w x y ∧ s1 = (st, tr) ∧ P w)
    (hrhs : ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx → ∀ (cfg : Config) x y w
      (st : LState) tr n v s', cfg.checkOverlap = false → ValsBelow ctx st → w ≤ 64 → P w →
      (evalExpr p (sem ctx) cfg (n + 200) r.rhs (E w x y)).run (st, tr) = .ok (some v, s') →
      ∃ ms d, v = .regsVec [[.vreg d .int]] ∧ CodeShapeU st s'.1 ms d [x, y] ∧
        ∀ (ty : Clif.Ty), ty.width = w → eTy ty = true →
        ∀ (fr : Clif.Frame) (ρ : Nat → CV) (u : BitVec ty.width) (yv : Clif.Val) (res : BitVec ty.width),
          fr.func = ctx.func → ValsHeld fr ρ → DFGCons ctx fr → fr.regs x = some ⟨ty, u⟩ →
          fr.regs y = some yv → Clif.Sem.shift cop u yv.bits = some res →
          ∃ ρ', PRun F isem ms ρ ρ' ∧ VHolds ⟨ty, res⟩ (ρ' d)) :
    LowerRuleOk isem MR env cp p r := by
  intro f ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr' hm hn hvb hfirst
    hmatch' heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 200 := ⟨n - 200, by omega⟩
  obtain ⟨ty, x, y, rfl, hety, hd, hhead⟩ :=
    binary_front hp hargs hto hko hname hcop hctx hi hc (m := m' + 9) hmatch'
  have hw := eTy_width hety
  obtain ⟨rfl, rfl, hP⟩ :=
    hmatch ctx cfg ii info ty.width x y st tr m' env' s1 hi hhead hw hd hfirst hmatch'
  obtain ⟨ms, d, rfl, hsh, hsem⟩ :=
    hrhs f ctx hctx cfg x y ty.width st tr n' out (st', tr') hco hvb hw hP heval
  refine ⟨ms, _, hsh.emitted, rfl, ?_⟩
  refine lowerInstOk_one hMR hsh.mono hsh.defs rfl ?_
  intro fr cm ρ vals cm' hf hvals hdfg ho
  obtain ⟨u, yv, res, hu, hy, hres, rfl, rfl⟩ := evalInst_shift_ok hshift ho
  have hxv := getAs_ok hu
  obtain ⟨ρ', hrun, hheld⟩ := hsem ty rfl hety fr ρ u yv res hf hvals hdfg hxv hy hres
  refine ⟨rfl, usesOk_of [x, y] ?_ ?_, .inl hsh.res, _, ρ', rfl, hrun, hheld⟩
  · intro mi hmi v hv
    exact hsh.uses mi hmi v hv
  · intro z hz
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl
    · simp [hxv]
    · simp [hy]

end Backend.Proof
