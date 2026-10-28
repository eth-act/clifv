import FV.Backend.Proof.IselPrgCtxT
import FV.Backend.Proof.LowerLoopCtxTF

/-!
# Progress of the ISLE lowering over the float scope: the driver's contexts (S11f, #35)

`PInvTF` for the contexts the driver lowers in, on the float scope (`Compile.functionETF`,
`LowerScopeTF`): `buildCtx f`'s (`pinv_buildTF`), a terminator's (`pinv_termCtxTF`) and a
`try_call`'s (`pinv_tryCtxTF`). `pinv_buildT`'s sources, with `ctxInvT_ofF` for `CtxInvT`, the
float scope's statements (`Compile.instETF`), its integer positions (`CtxSpec.intOpsF_of`) and
float positions (`CtxSpec.floatOps_of`).
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64

section
variable {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}

/-- **`PInvTF` of `buildCtx`'s context** on the float scope. -/
theorem pinv_buildTF (hdom : dominatedB f = true) (hs : LowerScopeTF f)
    (hw : extendsWidenB f = true) (hin : iselInB f = true)
    (hb : buildCtx f = .ok (ctx, ranges, st0)) : PInvTF f ctx := by
  have sp := ctxSpec_of hb
  have hd := dominated_of hdom
  obtain ⟨-, hX, hbl, hO, -, -⟩ := functionETF_parts hs.subsetTF
  have hctx : CtxInvT f ctx := ctxInvT_ofF hs hb
  have hclif : ∀ (j : Nat) (info : IInfo) (c : Clif.Inst), ctx.insts[j]? = some info →
      info.clif = some c → InstOf f c := by
    intro j info c hi hc
    rcases sp.insts info (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi)) with
      rfl | ⟨B, hB, s, hs, rfl⟩
    · simp [placeholder] at hc
    · simp only [infoOf, Option.some.injEq] at hc
      exact ⟨B, hB, s, hs, hc⟩
  have hinst : ∀ c, InstOf f c → ∃ (j : Nat) (info : IInfo), ctx.insts[j]? = some info ∧
      info.clif = some c := by
    intro c hc
    obtain ⟨bi, B, j, stm, hB, hj, rfl⟩ := instOf_idx hc
    obtain ⟨info, hinfo, hcl, -⟩ := sp.facts.stmt bi B j stm hB hj
    exact ⟨_, info, hinfo, hcl⟩
  have hF : ∀ c, InstOf f c → Compile.instETF c = true := by
    intro c hc
    obtain ⟨B, hB, s, hs, rfl⟩ := hc
    have h := hbl B hB
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    exact h.1.2 s hs
  refine { toPInvTB := ⟨hctx, hclif, hX, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    instETF := hF, intOpsFOf := ?_, floatOpsOf := ?_ }
  -- intArgsOf
  · intro c hc x hx
    obtain ⟨j, info, hi, hcl⟩ := hinst c hc
    exact hctx.intOps j info c hi hcl x hx
  -- argsTyped
  · intro c hc x hx
    obtain ⟨bi, B, j, stm, hB, hj, rfl⟩ := instOf_idx hc
    exact typed_of_def sp (availOf_defs ((hd.uses ctx ranges st0 hb bi B hB).1 j stm hj x hx))
  -- resTyped
  · intro j info hi r hr
    rcases sp.insts info (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi)) with
      rfl | ⟨B, hB, s, hs, rfl⟩
    · simp [placeholder] at hr
    · refine typed_of_def sp ?_
      simp only [valueDefs, List.mem_flatMap, List.mem_append]
      exact ⟨B, hB, .inr ⟨s, hs, hr⟩⟩
  -- noClifRes
  · intro j info hi hc
    rcases sp.insts info (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi)) with
      rfl | ⟨B, hB, s, hs, rfl⟩
    · rfl
    · simp [infoOf] at hc
  -- resE
  · intro j info c hi hc hE t ht
    have hM := hctx.resTysM j info hi t ht
    obtain ⟨tys, hrt, hres, -⟩ := hctx.resTys j info c hi hc
    rw [hres] at ht
    obtain ⟨ty, hty, rfl⟩ := List.mem_map.mp ht
    have hnf := resTy_not_floatX hX hE (hctx.data j info c hi hc) hrt hty
    revert hM hnf; cases ty <;> simp [mCTys, eCTys, CTy.ofClif, Clif.Ty.isFloat]
  -- termIntOf
  · intro B hB x hx t ht
    refine sp.eCTys_of_not_floatDef ht fun hfd => ?_
    simp only [Compile.opsTypedTF, Bool.and_eq_true, List.all_eq_true] at hO
    have := (hO B hB).2 x hx
    simp [hfd] at this
  -- slots
  · intro ty s off hc
    have h := stmtIsel_of hin hc
    simp only [stmtIselB] at h
    rw [sp.slotOff]; exact h
  -- callees
  · intro c fn hc hk
    have h := stmtIsel_of hin hc
    rcases hk with ⟨args, rfl⟩ | ⟨ty, rfl⟩ <;>
    · simp only [stmtIselB] at h
      cases he : f.extern? fn with
      | none => rw [he] at h; cases h
      | some e => rw [he] at h; exact ⟨e, rfl, sigOk_of h⟩
  -- indSigs
  · intro sig callee args s hc hs
    have h := stmtIsel_of hin hc
    simp only [stmtIselB, hs] at h
    exact sigOk_of h
  -- extNarrow
  · intro op ty x hc
    obtain ⟨j, info, hinfo, hcl⟩ := hinst _ hc
    obtain ⟨t, ht, hlt⟩ := extendsWiden_of hw hb _ info op ty x hinfo hcl
    have hte := hctx.intOps j info _ hinfo hcl x (by simp [intArgs]) t ht
    simp only [eCTys, List.mem_cons, List.not_mem_nil, or_false] at hte
    rcases hte with rfl | rfl | rfl | rfl
    · exact ⟨8, ht, .inl rfl⟩
    · exact ⟨16, ht, .inr (.inl rfl)⟩
    · exact ⟨32, ht, .inr (.inr rfl)⟩
    · exfalso
      have hI := hF _ hc
      cases ty <;> simp_all [Compile.instETF, Compile.instETA, Compile.fArithET, Compile.fCvtET,
        Compile.fCmpET, Compile.instET, Compile.instE, Compile.tyE, CTy.ofClif, CTy.bits]
  -- intOpsFOf
  · intro c hc x hx
    obtain ⟨j, info, hi, hcl⟩ := hinst c hc
    exact sp.intOpsF_of hs.subsetTF j info c hi hcl x hx
  -- floatOpsOf
  · intro c hc x hx
    obtain ⟨B, hB, s, hs', rfl⟩ := hc
    exact sp.floatOps_of hs.subsetTF hctx hB hs' hx

/-- `PInvTF` survives replacing a terminator's placeholder by an entry without CLIF instruction
or results. -/
theorem pinvTF_of_insts (hP : PInvTF f ctx) {ctx' : Ctx} (hinv : CtxInvT f ctx')
    (hvt : ctx'.valTy = ctx.valTy) (hso : ctx'.slotOff = ctx.slotOff)
    (hins : ∀ (j : Nat) (info : IInfo), ctx'.insts[j]? = some info →
      ctx.insts[j]? = some info ∨ (info.clif = none ∧ info.results = [] ∧ info.resTys = [])) :
    PInvTF f ctx' := by
  have hty : ∀ x, ctx'.valueType? x = ctx.valueType? x := fun x => by
    simp only [Ctx.valueType?, hvt]
  exact { toPInvTB := pinvTB_of_insts hP.toPInvTB hinv hvt hso hins, instETF := hP.instETF,
    intOpsFOf := fun c hc x hx t ht => hP.intOpsFOf c hc x hx t (by rw [← hty]; exact ht),
    floatOpsOf := fun c hc x hx t ht => hP.floatOpsOf c hc x hx t (by rw [← hty]; exact ht) }

/-- **`PInvTF` of a terminator's context** (`termCtx`). -/
theorem pinv_termCtxTF (hP : PInvTF f ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (data : V) :
    PInvTF f (termCtx ctx ti data) :=
  pinvTF_of_insts hP (ctxInvT_termCtx hP.ctxInv hph data) rfl rfl fun _ _ h =>
    termCtx_insts_casesT h

/-- **`PInvTF` of a `try_call`'s context** (`tryCtx`). -/
theorem pinv_tryCtxTF (hP : PInvTF f ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (data : V) (trs : List Reg × List Reg) :
    PInvTF f (tryCtx ctx ti data trs) :=
  pinvTF_of_insts hP { ctxInvT_termCtx hP.ctxInv hph data with } rfl rfl fun _ _ h =>
    termCtx_insts_casesT (ti := ti) (data := data) h

end

end Backend.Proof.Prg
