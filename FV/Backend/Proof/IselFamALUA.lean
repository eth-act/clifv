import FV.Backend.Proof.IselFamily

/-!
# Family A (binary ALU with operand look-through): generic lemmas

The root rules of `iadd`/`isub`/`imul`/`umulhi`/`smulhi`/`band`/`bor`/`bxor` beyond the
register-register base cases look through the definition of an operand (`iconst`, `ishl` by a
constant, `imul`, `uextend`/`sextend`, `bnot`, `ushr`) and emit one or a few instructions. This
file proves once what every such rule needs:

1. **Match inversion** (`root_match_inv`, `values2_match_inv`, `defInst_match_inv`): a
   successful match of the rule's pattern on `[.inst ii]` names the instruction's data and, for
   each look-through pattern `(def_inst (inst_data_value _ (Fmt (Op) …)))`, the defining
   instruction's data. `CtxInv` (`data`, `defClif`) and `instData` inversion
   (`instNames_*`, `instData_*_data`) turn these into CLIF instructions.
2. **Values** (`dfg_value`): `DFGCons` evaluates a looked-through definition in the frame.
3. **Code** (`seqRun_step`, `lowerInstOk_binary`): straight-line code of world-preserving
   `ispec` forms, one fresh def per instruction, run under any `isem` refining `ispec`, and the
   `LowerInstOk` obligation of a two-operand CLIF instruction from its value-level meaning.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-! ## 1. Match inversion -/

section Inversion
variable {p : Program} (hp : Data p) (ctx : Ctx)

theorem matchArgs_nil_nil {st : LState} {e e' : Interp.Env V}
    (h : matchArgs p (sem ctx) st [] [] e = .ok (some e')) : e' = e := by
  rw [matchArgs.eq_1] at h
  simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
  exact h.symm

theorem matchPat_bind_wild_inv {st : LState} {ty : TypeId} {x : VarId} {ty' : TypeId} {v : V}
    {env env' : Interp.Env V}
    (h : matchPat p (sem ctx) st (.bind ty x (.wildcard ty')) v env = .ok (some env')) :
    env' = env.set! x (some v) := by
  obtain ⟨-, h⟩ := matchPat_bind_inv h
  rw [matchPat.eq_6] at h
  simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
  exact h.symm

include hp in
/-- **The instruction a root rule matched, and the rest of its pattern**: the data has the
format and opcode the pattern names; the remaining argument patterns matched its fields, and
the if-lets matched from there. -/
theorem root_match_inv {cfg : Config} {m : Nat} {r : Rule} {ii : Nat}
    {s s1 : LState × Array RuleId} {env : Interp.Env V} {tyPat : Pattern} {fmtT opT : TermId}
    {rest : List Pattern} {tf to : Term} {kf ko : Nat}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 fmtT (.term 151 opT [] :: rest)]])
    (htf : termOf p fmtT = .ok tf) (hkf : tf.kind = .enumVariant kf)
    (hto : termOf p opT = .ok to) (hko : to.kind = .enumVariant ko)
    (h : (matchRule p (sem ctx) cfg (m + 1) r [.inst ii]).run s = .ok (some env, s1)) :
    ∃ info fs e0 e1, ctx.insts[ii]? = some info ∧
      info.data = .data 152 kf (.data 151 ko [] :: fs) ∧
      matchArgs p (sem ctx) s.1 rest fs e0 = .ok (some e1) ∧
      (matchIfLets p (sem ctx) cfg m r.iflets e1).run s = .ok (some env, s1) := by
  obtain ⟨env0, ha, hil⟩ := matchRule_some_inv h
  rw [hargs] at ha
  obtain ⟨e1, hp1, hn⟩ := matchArgs_cons_inv ha
  have := matchArgs_nil_nil ctx hn
  subst this
  obtain ⟨fs, hx, hm⟩ := matchPat_extract_inv hp.t209 term_209_kind rfl hp1
  rw [sem_extract] at hx
  obtain ⟨info, hi, rfl⟩ := ext_inst_data_value_inv hx
  obtain ⟨e2, -, hm2⟩ := matchArgs_cons_inv hm
  obtain ⟨e3, hp3, hn3⟩ := matchArgs_cons_inv hm2
  have := matchArgs_nil_nil ctx hn3
  subst this
  obtain ⟨fs', hu, hm3⟩ := matchPat_enum_inv htf hkf hp3
  have hd := sem_unData_inv hu
  cases fs' with
  | nil => exact (matchArgs_cons_nil hm3).elim
  | cons w ws =>
    obtain ⟨e4, hp4, hm4⟩ := matchArgs_cons_inv hm3
    obtain ⟨fs'', hu', hm5⟩ := matchPat_enum_inv hto hko hp4
    have hw := sem_unData_inv hu'
    have := matchArgs_nil_inv hm5
    subst this
    exact ⟨info, ws, e4, _, hi, by rw [hd, hw], hm4, hil⟩

include hp in
/-- The two-value field (`value_array_2`) of a `Binary`-format pattern. -/
theorem values2_match_inv {st : LState} {Px Py : Pattern} {x y : Nat} {env env' : Interp.Env V}
    (h : matchArgs p (sem ctx) st [.term 147 1614 [Px, Py]] [.values [x, y]] env =
      .ok (some env')) :
    ∃ e1, matchPat p (sem ctx) st Px (.value x) env = .ok (some e1) ∧
      matchPat p (sem ctx) st Py (.value y) e1 = .ok (some env') := by
  obtain ⟨e1, hp1, hn⟩ := matchArgs_cons_inv h
  have := matchArgs_nil_nil ctx hn
  subst this
  obtain ⟨fs, hx, hm⟩ := matchPat_extract_inv hp.t1614 term_1614_kind rfl hp1
  rw [sem_extract, ext_value_array_2] at hx
  cases hx
  obtain ⟨e2, h2, hm2⟩ := matchArgs_cons_inv hm
  obtain ⟨e3, h3, hm3⟩ := matchArgs_cons_inv hm2
  have := matchArgs_nil_nil ctx hm3
  subst this
  exact ⟨e2, h2, h3⟩

include hp in
/-- **A look-through pattern matched** `(def_inst (inst_data_value tyPat (Fmt (Op) rest…)))` on
value `y`: `y` is defined by instruction `j`, whose data has the named format and opcode, and
`rest` matched its fields. -/
theorem defInst_match_inv {st : LState} {y : Nat} {env env' : Interp.Env V} {tyPat : Pattern}
    {fmtT opT : TermId} {rest : List Pattern} {tf to : Term} {kf ko : Nat}
    (htf : termOf p fmtT = .ok tf) (hkf : tf.kind = .enumVariant kf)
    (hto : termOf p opT = .ok to) (hko : to.kind = .enumVariant ko)
    (h : matchPat p (sem ctx) st
      (.term 15 1 [.term 18 209 [tyPat, .term 152 fmtT (.term 151 opT [] :: rest)]]) (.value y) env =
      .ok (some env')) :
    ∃ j info fs e0, ctx.defInst? y = some j ∧ ctx.insts[j]? = some info ∧
      info.data = .data 152 kf (.data 151 ko [] :: fs) ∧
      matchArgs p (sem ctx) st rest fs e0 = .ok (some env') := by
  obtain ⟨fs0, hx0, hm0⟩ := matchPat_extract_inv hp.t1 term_1_kind rfl h
  rw [sem_extract, ext_def_inst] at hx0
  cases hj : ctx.defInst? y with
  | none => rw [hj] at hx0; cases hx0
  | some j =>
  rw [hj] at hx0
  cases hx0
  obtain ⟨e1, hp1, hn⟩ := matchArgs_cons_inv hm0
  have := matchArgs_nil_nil ctx hn
  subst this
  obtain ⟨fs, hx, hm⟩ := matchPat_extract_inv hp.t209 term_209_kind rfl hp1
  rw [sem_extract] at hx
  obtain ⟨info, hi, rfl⟩ := ext_inst_data_value_inv hx
  obtain ⟨e2, -, hm2⟩ := matchArgs_cons_inv hm
  obtain ⟨e3, hp3, hn3⟩ := matchArgs_cons_inv hm2
  have := matchArgs_nil_nil ctx hn3
  subst this
  obtain ⟨fs', hu, hm3⟩ := matchPat_enum_inv htf hkf hp3
  have hd := sem_unData_inv hu
  cases fs' with
  | nil => exact (matchArgs_cons_nil hm3).elim
  | cons w ws =>
    obtain ⟨e4, hp4, hm4⟩ := matchArgs_cons_inv hm3
    obtain ⟨fs'', hu', hm5⟩ := matchPat_enum_inv hto hko hp4
    have hw := sem_unData_inv hu'
    have := matchArgs_nil_inv hm5
    subst this
    exact ⟨j, info, ws, e4, rfl, hi, by rw [hd, hw], hm4⟩

end Inversion

/-! ## 2. From the matched data to CLIF instructions and their values -/

section Clif

set_option maxRecDepth 20000 in
theorem variantNames_UnaryImm : (variantNames 152)[35]? = some "UnaryImm" := rfl
set_option maxRecDepth 20000 in
theorem variantNames_Iconst : (variantNames 151)[57]? = some "Iconst" := rfl

theorem instNames_iconst {c : Clif.Inst} (h : instNames c = ("UnaryImm", "Iconst")) :
    ∃ ty imm, c = .iconst ty imm := by
  cases c <;> simp [instNames] at h ⊢

theorem instData_iconst_data {f : Clif.Function} {ty : Clif.Ty} {imm : BitVec ty.width}
    {k k' : Nat} {fs : List V}
    (h : instData f (.iconst ty imm) = .ok (.data 152 k (.data 151 k' [] :: fs))) :
    fs = [.int (imm64OfIconst ty imm)] := by
  simp only [instData] at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
    injection h3 with _ h4
  · cases h

/-- The instruction behind a matched data value (`CtxInv.data` needs `info.clif`; for a
value's definition `CtxInv.defClif` supplies it). -/
theorem ctxInv_clif {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {y j : Nat}
    {info : IInfo} (hj : ctx.defInst? y = some j) (hi : ctx.insts[j]? = some info) :
    ∃ cl, info.clif = some cl ∧ instData f cl = .ok info.data := by
  obtain ⟨cl, hcl⟩ := Option.isSome_iff_exists.mp (hctx.defClif y j info hj hi)
  exact ⟨cl, hcl, hctx.data j info cl hi hcl⟩

/-- A matched `UnaryImm (Iconst) k` is an `iconst`. -/
theorem instData_iconst_inv {f : Clif.Function} {cl : Clif.Inst} {fs : List V}
    (h : instData f cl = .ok (.data 152 35 (.data 151 57 [] :: fs))) :
    ∃ ty imm, cl = .iconst ty imm ∧ fs = [.int (imm64OfIconst ty imm)] := by
  obtain ⟨hf, ho⟩ := instData_inv_names h
  rw [variantNames_UnaryImm] at hf
  rw [variantNames_Iconst] at ho
  have : instNames cl = ("UnaryImm", "Iconst") :=
    Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm
  obtain ⟨ty, imm, rfl⟩ := instNames_iconst this
  exact ⟨ty, imm, rfl, instData_iconst_data h⟩

/-- A matched `Binary (O) (a b)` with `O` the opcode of `cop` is `cop`. -/
theorem instData_binary_inv {f : Clif.Function} {cl : Clif.Inst} {fs : List V} {ko : Nat}
    {cop : Clif.BinaryOp} {n : String} (hname : (variantNames 151)[ko]? = some n)
    (hcop : binaryOpcode cop = some n)
    (h : instData f cl = .ok (.data 152 2 (.data 151 ko [] :: fs))) :
    ∃ ty a b, cl = .binary cop ty a b ∧ eTy ty = true ∧ fs = [.values [a, b]] := by
  obtain ⟨hf, ho⟩ := instData_inv_names h
  rw [variantNames_Binary] at hf
  rw [hname] at ho
  have : instNames cl = ("Binary", n) :=
    Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm
  obtain ⟨ty, a, b, rfl⟩ := instNames_binary hcop this
  obtain ⟨he, hfs⟩ := instData_binary_data hcop h
  exact ⟨ty, a, b, rfl, he, hfs⟩

theorem lookup_zip_single {l : List Nat} {a v : Clif.Val} {x : Nat}
    (h : (l.zip [a]).lookup x = some v) : v = a := by
  cases l with
  | nil => simp at h
  | cons z zs =>
    simp only [List.zip_cons_cons, List.zip_nil_right, List.lookup] at h
    split at h
    · exact (Option.some.inj h).symm
    · cases h

/-- **The value of a looked-through definition** with one result `a` (`DFGCons`). -/
theorem dfg_single {ctx : Ctx} {fr : Clif.Frame} (hd : DFGCons ctx fr) {y j : Nat} {info : IInfo}
    {cl : Clif.Inst} {v : Clif.Val} (hj : ctx.defInst? y = some j) (hi : ctx.insts[j]? = some info)
    (hcl : info.clif = some cl) (hpure : pureInst cl = true) (hv : fr.regs y = some v)
    {a : Clif.Val} (hev : ∀ vals cm cm', Clif.evalInst fr cm cl = .ok (vals, cm') → vals = [a]) :
    v = a := by
  obtain ⟨vals, hev', hl⟩ := hd.1 y j info cl v hj hi hcl hpure hv
  have := hev _ _ _ (hev' default)
  subst this
  exact lookup_zip_single hl

theorem evalInst_iconst (fr : Clif.Frame) (cm : Clif.Mem) (ty : Clif.Ty) (imm : BitVec ty.width) :
    Clif.evalInst fr cm (.iconst ty imm) = .ok ([⟨ty, imm⟩], cm) := rfl

theorem evalInst_binary_inv {fr : Clif.Frame} {cm cm' : Clif.Mem} {op : Clif.BinaryOp}
    {ty : Clif.Ty} {a b : Nat} {vals : List Clif.Val} (hs : op.isShift = false)
    (h : Clif.evalInst fr cm (.binary op ty a b) = .ok (vals, cm')) :
    ∃ u w, fr.getAs a ty = .ok u ∧ fr.getAs b ty = .ok w ∧
      vals = [⟨ty, Clif.Sem.binary op u w⟩] := by
  simp only [Clif.evalInst, hs, Bool.false_eq_true, ↓reduceIte] at h
  cases ha : fr.getAs a ty with
  | trap c => rw [ha] at h; cases h
  | stuck m => rw [ha] at h; cases h
  | ok u =>
  cases hb : fr.getAs b ty with
  | trap c => rw [ha, hb] at h; cases h
  | stuck m => rw [ha, hb] at h; cases h
  | ok w =>
  rw [ha, hb] at h
  simp only [Clif.Res.ok_bind, Clif.Res.pure_eq] at h
  injection h with h
  injection h with h1 h2
  exact ⟨u, w, rfl, rfl, h1.symm⟩

theorem evalInst_shift_inv {fr : Clif.Frame} {cm cm' : Clif.Mem} {op : Clif.BinaryOp}
    {ty : Clif.Ty} {a b : Nat} {vals : List Clif.Val} (hs : op.isShift = true)
    (h : Clif.evalInst fr cm (.binary op ty a b) = .ok (vals, cm')) :
    ∃ u bv r, fr.getAs a ty = .ok u ∧ fr.get b = .ok bv ∧ Clif.Sem.shift op u bv.bits = some r ∧
      vals = [⟨ty, r⟩] := by
  simp only [Clif.evalInst, hs, ↓reduceIte] at h
  cases ha : fr.getAs a ty with
  | trap c => rw [ha] at h; cases h
  | stuck m => rw [ha] at h; cases h
  | ok u =>
  cases hb : fr.get b with
  | trap c => rw [ha, hb] at h; cases h
  | stuck m => rw [ha, hb] at h; cases h
  | ok bv =>
  rw [ha, hb] at h
  simp only [Clif.Res.ok_bind] at h
  cases hr : Clif.Sem.shift op u bv.bits with
  | none => rw [hr] at h; cases h
  | some r =>
  rw [hr] at h
  simp only [Clif.Res.ofOption_some, Clif.Res.ok_bind, Clif.Res.pure_eq] at h
  injection h with h
  injection h with h1 h2
  exact ⟨u, bv, r, rfl, rfl, hr, h1.symm⟩

theorem get_ok {fr : Clif.Frame} {x : Nat} {v : Clif.Val} (h : fr.get x = .ok v) :
    fr.regs x = some v := by
  unfold Clif.Frame.get at h
  cases hx : fr.regs x with
  | none => rw [hx] at h; cases h
  | some v' => rw [hx] at h; cases h; rfl

end Clif

/-! ### The root instruction of a `Binary`-format rule -/

section Root
variable {p : Program} (hp : Data p)

include hp in
/-- **Step 1 for a `Binary (O) (x y)` root rule**: the matched instruction is `cop ty x y`
(`O` the opcode of `cop`), with its data and result type, and the value-pair pattern matched
`[x, y]`. -/
theorem binary_root_inv {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {cfg : Config} {m : Nat} {r : Rule} {s s1 : LState × Array RuleId} {env : Interp.Env V}
    {tyPat : Pattern} {opT : TermId} {rest : List Pattern} {to : Term} {ko : Nat}
    {cop : Clif.BinaryOp} {n : String}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2449 (.term 151 opT [] :: rest)]])
    (hto : termOf p opT = .ok to) (hko : to.kind = .enumVariant ko)
    (hname : (variantNames 151)[ko]? = some n) (hcop : binaryOpcode cop = some n)
    (h : (matchRule p (sem ctx) cfg (m + 1) r [.inst ii]).run s = .ok (some env, s1)) :
    ∃ ty x y e0 e1, inst = .binary cop ty x y ∧
      info.data = .data 152 2 [.data 151 ko [], .values [x, y]] ∧
      info.resTys.head? = some (.int ty.width) ∧ ty.width ≤ 64 ∧
      matchArgs p (sem ctx) s.1 rest [.values [x, y]] e0 = .ok (some e1) ∧
      (matchIfLets p (sem ctx) cfg m r.iflets e1).run s = .ok (some env, s1) := by
  obtain ⟨info', fs, e0, e1, hi', hd, hrest, hil⟩ :=
    root_match_inv hp ctx hargs hp.t2449 term_2449_kind hto hko h
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hc
  rw [hd] at hdat
  obtain ⟨ty, x, y, rfl, hety, rfl⟩ := instData_binary_inv hname hcop hdat
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii info _ hi hc
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  refine ⟨ty, x, y, e0, e1, rfl, hd, ?_, eTy_width hety, hrest, hil⟩
  rw [hres]; simp [ofClif_int_width]

end Root

/-! ## 3. The emitted code and the per-instruction obligation -/

section Code

theorem SameWorld.trans' {F : BitVec 64 → Prop} {s t u : Arm.ArmState} (h1 : SameWorld F s t)
    (h2 : SameWorld F t u) : SameWorld F s u :=
  ⟨fun f hf => (h1.1 f hf).trans (h2.1 f hf), fun a ha => (h1.2.1 a ha).trans (h2.2.1 a ha),
    h1.2.2.trans h2.2.2⟩

/-- **One instruction** with a single late def `d`, whose `ispec` meaning `r` leaves the
world unchanged, run under any `isem` refining `ispec`. -/
theorem seqRun_step {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {m : MInst}
    {ops : Array Operand} {ms : List MInst} {ρ : Nat → CV} {w : Arm.ArmState} {d : Nat} {r : CV}
    (hops : m.operands = .ok ops)
    (hdefs : ops.toList.filter Operand.isDef = [⟨d, .int, .def, .late, .reg⟩])
    (hs : ispec m (vuses ops ρ) w = some ([r], w, .next)) :
    ∃ w1, SameWorld F w1 w ∧
      seqRun isem (m :: ms) ρ w = (seqRun isem ms (upd ρ d r) w1).map SeqEnd.succ := by
  obtain ⟨w1, hs1, hw⟩ := hR _ _ _ _ _ hs
  refine ⟨w1, hw, ?_⟩
  have hv : vdefUpd ops [r] ρ = upd ρ d r := by
    simp [vdefUpd, hdefs, writeV, Operand.isEarly, Operand.isLate]
  simp only [seqRun, hops, hs1, hdefs, List.length_cons, List.length_nil, ↓reduceIte, hv]

theorem seqRun_nil_fall (isem : Sem) (ρ : Nat → CV) (w : Arm.ArmState) :
    seqRun isem [] ρ w = some (.fall ρ w) := rfl

theorem map_succ_fall (ρ : Nat → CV) (w : Arm.ArmState) :
    (some (SeqEnd.fall ρ w) : Option (SeqEnd CV Arm.ArmState)).map SeqEnd.succ =
      some (.fall ρ w) := rfl

/-- **`LowerInstOk` of a two-operand instruction** (not a shift) from the value-level meaning
of its code: whenever both operands are defined, the code runs to the end, writing a result
that holds `cop u v` in the fresh vreg `dst`, and keeps the world outside the allocatable
registers. -/
theorem lowerInstOk_binary {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {ctx : Ctx} (hMR : MRStable F MR) {cop : Clif.BinaryOp} {ty : Clif.Ty}
    {x y : Nat} {results : List Nat} {st st' : LState} {ms : List MInst} {dst : Nat}
    (hshift : cop.isShift = false) (hmono : st.nextVreg ≤ st'.nextVreg)
    (hdefs : ∀ m ∈ ms, ∀ d ∈ vdefs m, st.nextVreg ≤ d ∧ d < st'.nextVreg)
    (hdst : st.nextVreg ≤ dst)
    (hrun : ∀ (fr : Clif.Frame) (ρ : Nat → CV) (w : Arm.ArmState), fr.func = ctx.func →
      ValsHeld fr ρ → DFGCons ctx fr → ∀ u v, fr.getAs x ty = .ok u → fr.getAs y ty = .ok v →
      UsesOk st fr ms ∧ ∃ ρ' w', seqRun isem ms ρ w = some (.fall ρ' w') ∧ SameWorld F w' w ∧
        VHolds ⟨ty, Clif.Sem.binary cop u v⟩ (ρ' dst)) :
    LowerInstOk isem MR env cp ctx (.binary cop ty x y) results st [[.vreg dst .int]] st' ms := by
  refine ⟨hmono, hdefs, ?_⟩
  intro fr cm ρ w hfn hvals hdfg hmr
  have hout : instOutcome env cp fr cm (.binary cop ty x y) =
    Clif.evalInst fr cm (.binary cop ty x y) := rfl
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
  obtain ⟨hu, ρ', w', hrun', hsw, hheld⟩ := hrun fr ρ w hfn hvals hdfg u v hx hy
  refine ⟨hu, ρ', w', hrun', .inr ⟨rfl, ?_⟩, hMR _ _ _ _ hsw.nf hmr⟩
  intro j rs val hrs hval
  match j, hrs, hval with
  | 0, hrs, hval =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hrs hval
    subst hrs; subst hval
    exact ⟨dst, .int, rfl, .inl hdst, hheld⟩
  | _ + 1, hrs, _ => simp at hrs

end Code

/-! ## 4. Instruction forms and width lemmas -/

section Forms

theorem seqRun_one {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {m : MInst}
    {ops : Array Operand} {ρ : Nat → CV} {w : Arm.ArmState} {d : Nat} {r : CV}
    (hops : m.operands = .ok ops)
    (hdefs : ops.toList.filter Operand.isDef = [⟨d, .int, .def, .late, .reg⟩])
    (hs : ispec m (vuses ops ρ) w = some ([r], w, .next)) :
    ∃ w', seqRun isem [m] ρ w = some (.fall (upd ρ d r) w') ∧ SameWorld F w' w := by
  obtain ⟨w1, hw, he⟩ := seqRun_step (ms := []) hR hops hdefs hs
  exact ⟨w1, by rw [he]; rfl, hw⟩

theorem operands_aluRRImm12 (op : ALUOp) (sz : OperandSize) (d x : Nat) (i : Imm12) :
    (MInst.aluRRImm12 op sz (.vreg d .int) (.vreg x .int) i).operands =
      .ok #[⟨d, .int, .def, .late, .reg⟩, ⟨x, .int, .use, .early, .reg⟩] := rfl

theorem ispec_aluRRImm12_add {sz : OperandSize} {d : Nat} {rn : Reg} {i : Imm12} {a : CV}
    {w : Arm.ArmState} (h : i.bits < 4096) :
    ispec (.aluRRImm12 .add sz (.vreg d .int) rn i) [a] w =
      some ([resX sz (opnd sz a + BitVec.ofNat _ i.value)], w, .next) := by
  simp only [ispec, h, ↓reduceIte]; rfl

theorem ispec_aluRRImm12_sub {sz : OperandSize} {d : Nat} {rn : Reg} {i : Imm12} {a : CV}
    {w : Arm.ArmState} (h : i.bits < 4096) :
    ispec (.aluRRImm12 .sub sz (.vreg d .int) rn i) [a] w =
      some ([resX sz (opnd sz a - BitVec.ofNat _ i.value)], w, .next) := by
  simp only [ispec, h, ↓reduceIte]; rfl

theorem u64_ofNat {m : Nat} (h : m < 2 ^ 64) : u64 (m : Int) = m := by
  unfold u64; omega

theorem u64_imm64OfIconst {ty : Clif.Ty} (hw : ty.width ≤ 64) (c : BitVec ty.width) :
    u64 (imm64OfIconst ty c) = c.toNat := by
  unfold imm64OfIconst
  have hlt := c.isLt
  split
  · exact u64_ofNat (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hw))
  · have h64 : ty.width = 64 := by omega
    unfold u64
    rw [BitVec.toInt_eq_toNat_cond]
    have h2 : (2 : Nat) ^ ty.width = 2 ^ 64 := by rw [h64]
    rw [h2] at hlt ⊢
    split <;> omega

theorem imm12_ofNat_value {v : Nat} {i : Imm12} (h : Imm12.ofNat? v = some i) (hv : v < 2 ^ 64) :
    i.value = v ∧ i.bits < 4096 := by
  unfold Imm12.ofNat? mask64 at h
  rw [Nat.mod_eq_of_lt hv] at h
  simp only at h
  split at h
  · cases h; exact ⟨rfl, by assumption⟩
  · split at h
    · cases h
      rename_i h1
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
      refine ⟨?_, by simp; omega⟩
      simp only [Imm12.value, ↓reduceIte]
      omega
    · cases h

theorem setWidth_ofNat_toNat {n w : Nat} (hw : w ≤ n) (c : BitVec w) :
    (BitVec.ofNat n c.toNat).setWidth w = c := by
  rw [BitVec.setWidth_ofNat_of_le hw]; simp

/-- Width lemma, register plus immediate. -/
theorem holds_add_imm {ty : Clif.Ty} {sz : OperandSize} (hw : ty.width ≤ sz.bits) {a : CV}
    {u c : BitVec ty.width} (ha : VHolds ⟨ty, u⟩ a) :
    VHolds ⟨ty, u + c⟩ (resX sz (opnd sz a + BitVec.ofNat _ c.toNat)) := by
  have h64 := opSize_bits_le sz
  simp only [VHolds] at ha ⊢
  rw [resX_setWidth hw h64, BitVec.setWidth_add _ _ hw, opnd_setWidth hw h64, ha,
    setWidth_ofNat_toNat hw]

/-- Width lemma, register minus immediate. -/
theorem holds_sub_imm {ty : Clif.Ty} {sz : OperandSize} (hw : ty.width ≤ sz.bits) {a : CV}
    {u c : BitVec ty.width} (ha : VHolds ⟨ty, u⟩ a) :
    VHolds ⟨ty, u - c⟩ (resX sz (opnd sz a - BitVec.ofNat _ c.toNat)) := by
  have h64 := opSize_bits_le sz
  simp only [VHolds] at ha ⊢
  rw [resX_setWidth hw h64, setWidth_sub_of_le hw, opnd_setWidth hw h64, ha,
    setWidth_ofNat_toNat hw]

end Forms

theorem u64_lt (i : Int) : u64 i < 2 ^ 64 := by unfold u64; omega

section Inversion2
variable {p : Program} (hp : Data p) (ctx : Ctx)

include hp in
/-- The `(u64_from_imm64 (imm12_from_u64 v))` field of a matched `iconst`. -/
theorem imm12_args_inv {st : LState} {k : Int} {v : VarId} {e e' : Interp.Env V}
    (h : matchArgs p (sem ctx) st [.term 134 144 [.term 4 325 [.bind 64 v (.wildcard 64)]]] [.int k] e =
      .ok (some e')) :
    ∃ imm, Imm12.ofNat? (u64 k) = some imm ∧ e' = e.set! v (some (.op (.imm12 imm))) := by
  obtain ⟨e1, hp1, hn⟩ := matchArgs_cons_inv h
  have := matchArgs_nil_nil ctx hn
  subst this
  obtain ⟨fs, hx, hm⟩ := matchPat_extract_inv hp.t144 term_144_kind rfl hp1
  rw [sem_extract, ext_u64_from_imm64] at hx
  cases hx
  obtain ⟨e2, hp2, hn2⟩ := matchArgs_cons_inv hm
  have := matchArgs_nil_nil ctx hn2
  subst this
  obtain ⟨fs2, hx2, hm2⟩ := matchPat_extract_inv hp.t325 term_325_kind rfl hp2
  rw [sem_extract, ext_imm12_from_u64, u64_ofNat (u64_lt k)] at hx2
  cases himm : Imm12.ofNat? (u64 k) with
  | none => rw [himm] at hx2; cases hx2
  | some imm =>
    rw [himm] at hx2
    cases hx2
    obtain ⟨e3, hp3, hn3⟩ := matchArgs_cons_inv hm2
    have := matchArgs_nil_nil ctx hn3
    subst this
    exact ⟨imm, rfl, matchPat_bind_wild_inv ctx hp3⟩

end Inversion2

end Backend.Proof
