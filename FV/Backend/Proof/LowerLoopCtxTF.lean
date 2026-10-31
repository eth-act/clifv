import FV.Backend.Proof.LowerLoopCtxT
import FV.Backend.Proof.InstScopeTF
import FV.Compile.SubsetTFIn

/-!
# The lowering's input conditions over the float scope (S11f, #35)

`LowerScopeTF f`: `LowerScopeT` with the float scope `Compile.functionETF` (the typed movement
scope with the S11f float operations, their integer positions `intOperandsF` and float positions
`floatOperands`) in place of `Compile.functionET`. `LowerScopeT` gives it (`LowerScopeT.toTF`).

On `buildCtx`'s context (`CtxSpec`):

* `ctxInvT_ofF`: it is a float-capable lowering context (`CtxInvT`, `ctxInvT_of`'s proof with the
  integer positions of `opsTypedTF`);
* `CtxSpec.intOpsF_of`: the operands in integer positions `intOperandsF` are integers;
* `CtxSpec.floatOps_of`: the operands in float positions `floatOperands` are `f32`/`f64`;
* `CtxSpec.instScopeTF`: the instructions are in the float scope (`InstScopeTF`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- **The other input conditions of the lowering over the float scope** (`LowerScopeT` with
`Compile.functionETF`). -/
structure LowerScopeTF (f : Clif.Function) : Prop where
  /-- the float scope -/
  subsetTF : Compile.functionETF f = true
  nonempty : f.blocks ≠ []
  noEntryPred : ∀ B ∈ f.blocks, ∀ b ∈ succIds B.term, blockIdx? f b ≠ some 0
  ctxFacts : ∀ ctx ranges st0, buildCtx f = .ok (ctx, ranges, st0) → brIdxOk f ctx = true ∧
    ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst) (x : Nat), ctx.insts[ii]? = some info →
      info.clif = some inst → memAddr? inst = some x → ctx.valueType? x = some (.int 64)
  tryRet : ∀ B ∈ f.blocks, ∀ et, IsTryWith B.term et → ∀ sig, f.sigDecls.lookup et.sig = some sig →
    ∀ i, Clif.TryArg.ret i ∈ et.normal.args → i < sig.returns.length
  stackLayout : (∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ fn args e, st.inst = .call fn args →
      f.extern? fn = some e → stackLayoutOk e.sig = true) ∧
    ∀ B ∈ f.blocks, ∀ fn args et e, B.term = .tryCall fn args et → f.extern? fn = some e →
      stackLayoutOk e.sig = true
  /-- the indirect callees' stack-argument layouts are well formed (S5) -/
  indStackLayout : ∀ s ∈ indSigs f, stackLayoutOk s = true

/-- The typed movement scope's input conditions are the float scope's. -/
theorem LowerScopeT.toTF {f : Clif.Function} (hs : LowerScopeT f) : LowerScopeTF f :=
  ⟨Compile.functionETF_of_functionET hs.subsetT, hs.nonempty, hs.noEntryPred, hs.ctxFacts,
    hs.tryRet, hs.stackLayout, hs.indStackLayout⟩

/-- The parts of `Compile.functionETF`. -/
theorem functionETF_parts {f : Clif.Function} (h : Compile.functionETF f = true) :
    Compile.sigET f.sig = true ∧ f.externs.all (Compile.sigE ·.2.sig) = true ∧
    (∀ B ∈ f.blocks, (B.params.all (Compile.tyM ·.2) && B.body.all (Compile.instETF ·.inst) &&
      Compile.termE B.term) = true) ∧ Compile.opsTypedTF f = true ∧
    Compile.edgeClassOk f = true ∧ Compile.floatOpsTyped f = true := by
  simp only [Compile.functionETF, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hs, -⟩, hx⟩, hb⟩, ho⟩, he⟩, hf⟩ := h
  exact ⟨hs, List.all_eq_true.mpr hx, fun B hB => by simpa using hb B hB, ho, he, hf⟩

/-- The externs of a float-scope function have integer signatures. -/
theorem LowerScopeTF.externsE {f : Clif.Function} (hs : LowerScopeTF f) :
    f.externs.all (Compile.sigE ·.2.sig) = true :=
  (functionETF_parts hs.subsetTF).2.1

/-- An integer position of `intOperands` is one of `intOperandsF`. -/
theorem mem_intOperandsF {i : Clif.Inst} {x : Nat} (h : x ∈ Compile.intOperands i) :
    x ∈ Compile.intOperandsF i := by
  cases i with
  | float op ty args => simp [Compile.intOperands] at h
  | _ => exact h

section
variable {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}

/-- The operands in integer positions `intOperandsF` of a float-scope function's instructions are
integers. -/
theorem CtxSpec.intOpsF_of (sp : CtxSpec f ctx ranges st0) (hT : Compile.functionETF f = true) :
    ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
      info.clif = some inst → ∀ x ∈ Compile.intOperandsF inst, IntPos ctx x := by
  intro ii info inst hi hc x hx t ht
  obtain ⟨B, hB, s, hs, -, rfl⟩ := sp.inst_of hi hc
  refine sp.eCTys_of_not_floatDef ht fun hfd => ?_
  have hO := (functionETF_parts hT).2.2.2.1
  simp only [Compile.opsTypedTF, Bool.and_eq_true, List.all_eq_true] at hO
  have := (hO B hB).1 s hs x hx
  simp [hfd] at this

/-- The operands in integer positions `intArgs` of a float-scope function's instructions are
integers. -/
theorem CtxSpec.intOps_ofF (sp : CtxSpec f ctx ranges st0) (hT : Compile.functionETF f = true) :
    ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
      info.clif = some inst → ∀ x ∈ intArgs inst, IntPos ctx x :=
  fun ii info inst hi hc x hx => sp.intOpsF_of hT ii info inst hi hc x
    (mem_intOperandsF (by rw [← intArgs_eq_intOperands]; exact hx))

/-- The instructions of `buildCtx`'s context of a float-scope function are in the scope. -/
theorem CtxSpec.instScopeTF (sp : CtxSpec f ctx ranges st0) (hT : Compile.functionETF f = true) :
    InstScopeTF ctx := by
  intro ii info inst hi hc
  obtain ⟨B, hB, s, hs, -, rfl⟩ := sp.inst_of hi hc
  have h := (functionETF_parts hT).2.2.1 B hB
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.2 s hs

/-- **`buildCtx` on the float scope gives a float-capable lowering context.** -/
theorem ctxInvT_ofF (hs : LowerScopeTF f) (hb : buildCtx f = .ok (ctx, ranges, st0)) :
    CtxInvT f ctx := by
  have sp := ctxSpec_of hb
  refine ⟨sp.func, ?_, ?_, ?_, ?_, ?_, ?_, sp.slotOff, ?_, ?_, (hs.ctxFacts ctx ranges st0 hb).2,
    sp.intOps_ofF hs.subsetTF⟩
  · intro ii info inst hi hc
    obtain ⟨B, hB, s, hs', rfl, rfl⟩ := sp.inst_of hi hc
    obtain ⟨⟨d, hd⟩, -, -⟩ := (sp.blockC B hB).2 s hs'
    simp [infoOf, dataOf, hd]
  · intro ii info inst hi hc
    obtain ⟨B, hB, s, hs', rfl, rfl⟩ := sp.inst_of hi hc
    obtain ⟨-, ⟨tys, hty, hlen⟩, -⟩ := (sp.blockC B hB).2 s hs'
    exact ⟨tys, hty, by simp [infoOf, tysOf, hty], by simp [infoOf, hlen]⟩
  · intro x r hr
    obtain ⟨t, ht, rfl⟩ := sp.regEq x r hr
    simp [valClassOf, ht]
  · intro x t ht
    have h1 := sp.regTy x
    rw [ht] at h1
    cases hr : ctx.valueReg? x with
    | none => rw [hr] at h1; cases h1
    | some r =>
      obtain ⟨t', ht', rfl⟩ := sp.regEq x r hr
      rw [ht] at ht'; cases ht'; rfl
  · intro x d hd
    obtain ⟨bi, B, j, stm, h1, h2, h3, rfl⟩ := sp.defOf x d hd
    obtain ⟨info, hi, -, hr⟩ := sp.facts.stmt bi B j stm h1 h2
    exact ⟨info, hi, by rw [hr]; exact h3⟩
  · intro x d info hd hi
    obtain ⟨bi, B, j, stm, h1, h2, -, rfl⟩ := sp.defOf x d hd
    obtain ⟨info', hi', hc, -⟩ := sp.facts.stmt bi B j stm h1 h2
    rw [hi] at hi'; cases hi'; simp [hc]
  · intro ii info hi t ht
    rcases sp.insts info (by rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? hi) with
      rfl | ⟨B, hB, s, hs', rfl⟩
    · simp [placeholder] at ht
    · simp only [infoOf, List.mem_map] at ht
      obtain ⟨ty, hty, rfl⟩ := ht
      exact mem_mCTys_of_valTyOk (((sp.blockC B hB).2 s hs').2.2 ty hty)
  · intro x t ht
    rcases sp.tyOf x t ht with ⟨B, hB, q, hq, -, rfl⟩ | ⟨B, hB, s, hs', m, ty, -, hty, rfl⟩
    · exact mem_mCTys_of_valTyOk ((sp.blockC B hB).1 q hq)
    · exact mem_mCTys_of_valTyOk (((sp.blockC B hB).2 s hs').2.2 ty (List.mem_of_getElem? hty))

/-- A type of `mCTys` of the float register class is `f32` or `f64`. -/
theorem float_of_mCTys {t : CTy} (hm : t ∈ mCTys) (hc : t.valClass = (CTy.ofClif .f32).valClass) :
    t = .float 32 ∨ t = .float 64 := by
  simp only [mCTys, eCTys, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [CTy.valClass, CTy.regClass?, CTy.ofClif]

/-- **The operands in float positions `floatOperands` of a float-scope function's statements are
`f32`/`f64` values** (`floatOpsTyped`: every definition of each is a float). -/
theorem CtxSpec.floatOps_of (sp : CtxSpec f ctx ranges st0) (hT : Compile.functionETF f = true)
    (hctx : CtxInvT f ctx) {B : Clif.Block} (hB : B ∈ f.blocks) {s : Clif.Stmt} (hs : s ∈ B.body)
    {x : Nat} (hx : x ∈ Compile.floatOperands s.inst) :
    ∀ t, ctx.valueType? x = some t → t = .float 32 ∨ t = .float 64 := by
  intro t ht
  have hF := (functionETF_parts hT).2.2.2.2.2
  simp only [Compile.floatOpsTyped, List.all_eq_true] at hF
  have hc := sp.class_of_argClassOk (hF B hB s hs x hx) (by decide) t ht
  exact float_of_mCTys (hctx.valTyM x t ht) hc

end

end Backend.Proof.Driver
