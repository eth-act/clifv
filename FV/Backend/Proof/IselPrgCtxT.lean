import FV.Backend.Proof.IselPrgCtx
import FV.Backend.Proof.IselPrgInvT
import FV.Backend.Proof.LowerLoopCtxT
import FV.Backend.Proof.IselTermFactsTy

/-!
# Progress of the ISLE lowering over the typed scope: the driver's contexts

`PInvT` for the contexts the driver lowers in, on the typed scope (`Compile.functionET`,
`LowerScopeT`): `buildCtx f`'s (`pinv_buildT`), a terminator's (`pinv_termCtxT`) and a
`try_call`'s (`pinv_tryCtxT`). Beyond `pinv_build`'s sources (`IselPrgCtx`):

* `CtxInvT`: `ctxInvT_of` (`LowerScopeT`);
* the statements are in the typed scope: `functionET`;
* integer positions: `CtxSpec.intOps_of` for statements and `CtxSpec.eCTys_of_not_floatDef` with
  `Compile.opsTypedT` for terminators;
* an E instruction's results are E integers (`resE_of`): its result types, the callee's integer
  returns (`Compile.sigE` of the externs), a `call_indirect`'s integer signature (`instData`'s
  `sigIntB`).
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64

/-- The result types of an E instruction of a typed-scope function are not floats. -/
theorem resTy_not_float {f : Clif.Function} (hET : Compile.functionET f = true) {c : Clif.Inst}
    (hE : Compile.instE c = true) {d : V} (hd : instData f c = .ok d) {tys : List Clif.Ty}
    (hrt : c.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) = some tys)
    {ty : Clif.Ty} (hty : ty ∈ tys) : ty.isFloat = false := by
  cases c
  case call fn args =>
    cases he : f.extern? fn with
    | none => simp [Clif.Inst.resultTypes, he] at hrt
    | some e =>
      simp only [Clif.Inst.resultTypes, he, Option.map_some, Option.some.injEq] at hrt
      subst hrt
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hty
      simp only [Compile.functionET, Bool.and_eq_true, List.all_eq_true] at hET
      have hl : f.externs.lookup fn = some e := he
      have hm : (fn, e) ∈ f.externs := by
        obtain ⟨l₁, l₂, h1, -⟩ := List.lookup_eq_some_iff.mp hl
        simp [h1]
      have hs := hET.1.1.1.2 (fn, e) hm
      simp only [Compile.sigE, Bool.and_eq_true, List.all_eq_true] at hs
      have := hs.2 p hp
      revert this; cases p.ty <;> simp [Compile.tyE, Clif.Ty.isInt, Clif.Ty.isFloat]
  case callIndirect sig callee args =>
    cases hl : f.sigDecls.lookup sig with
    | none => simp [Clif.Inst.resultTypes, hl] at hrt
    | some s =>
      simp only [Clif.Inst.resultTypes, hl, Option.map_some, Option.some.injEq] at hrt
      subst hrt
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hty
      have := List.all_eq_true.mp (sigIntB_iff.mp (instData_callIndirect_int hd hl)).2 p hp
      revert this; cases p.ty <;> decide
  case unary op ty x =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at hrt
    subst hrt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hty
    subst hty
    revert hE; cases op <;> cases ty <;> simp [Compile.instE, Compile.unaryTyE, Compile.unaryE,
      Compile.tyE, Clif.Ty.isInt, Clif.Ty.isFloat]
  all_goals first
    | (simp [Compile.instE] at hE; done)
    | (simp only [Clif.Inst.resultTypes, Option.some.injEq] at hrt
       subst hrt
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hty
       subst hty
       first
         | rfl
         | (revert hE; cases ty <;> simp [Compile.instE, Compile.tyE, Compile.unaryTyE,
             Compile.unaryE, Compile.binaryE, Clif.Ty.isInt, Clif.Ty.isFloat]))
    | (simp [Clif.Inst.resultTypes] at hrt; subst hrt; simp at hty)

section
variable {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}

/-- **`PInvT` of `buildCtx`'s context** on the typed scope. -/
theorem pinv_buildT (hdom : dominatedB f = true) (hs : LowerScopeT f)
    (hw : extendsWidenB f = true) (hin : iselInB f = true)
    (hb : buildCtx f = .ok (ctx, ranges, st0)) : PInvT f ctx := by
  have sp := ctxSpec_of hb
  have hd := dominated_of hdom
  have hET := hs.subsetT
  have hctx : CtxInvT f ctx := ctxInvT_of hs hb
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
  refine ⟨hctx, hclif, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- externsE
  · simp only [Compile.functionET, Bool.and_eq_true] at hET
    exact hET.1.1.1.2
  -- instET
  · intro c hc
    obtain ⟨B, hB, s, hs, rfl⟩ := hc
    simp only [Compile.functionET, Bool.and_eq_true, List.all_eq_true] at hET
    exact (hET.1.1.2 B hB).1.2 s hs
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
    have hnf := resTy_not_float hET hE (hctx.data j info c hi hc) hrt hty
    revert hM hnf; cases ty <;> simp [mCTys, eCTys, CTy.ofClif, Clif.Ty.isFloat]
  -- termIntOf
  · intro B hB x hx t ht
    refine sp.eCTys_of_not_floatDef ht fun hfd => ?_
    have hT := hET
    simp only [Compile.functionET, Compile.opsTypedT, Bool.and_eq_true, List.all_eq_true] at hT
    have := (hT.1.2 B hB).2 x hx
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
    have hET' := hclif j info _ hinfo hcl
    simp only [eCTys, List.mem_cons, List.not_mem_nil, or_false] at hte
    rcases hte with rfl | rfl | rfl | rfl
    · exact ⟨8, ht, .inl rfl⟩
    · exact ⟨16, ht, .inr (.inl rfl)⟩
    · exact ⟨32, ht, .inr (.inr rfl)⟩
    · exfalso
      have hI := (show Compile.instET (.extend op ty x) = true by
        obtain ⟨B, hB, s, hs, hs'⟩ := hET'
        simp only [Compile.functionET, Bool.and_eq_true, List.all_eq_true] at hET
        rw [← hs']; exact (hET.1.1.2 B hB).1.2 s hs)
      cases ty <;> simp_all [Compile.instET, Compile.instE, Compile.tyE, CTy.ofClif, CTy.bits]

/-- `PInvT` survives replacing a terminator's placeholder by an entry without CLIF instruction
or results. -/
theorem pinvT_of_insts (hP : PInvT f ctx) {ctx' : Ctx} (hinv : CtxInvT f ctx')
    (hvt : ctx'.valTy = ctx.valTy) (hso : ctx'.slotOff = ctx.slotOff)
    (hins : ∀ (j : Nat) (info : IInfo), ctx'.insts[j]? = some info →
      ctx.insts[j]? = some info ∨ (info.clif = none ∧ info.results = [] ∧ info.resTys = [])) :
    PInvT f ctx' := by
  have hty : ∀ x, ctx'.valueType? x = ctx.valueType? x := fun x => by
    simp only [Ctx.valueType?, hvt]
  have hip : ∀ x, IntPos ctx x → IntPos ctx' x := fun x h t ht => h t (by rw [← hty]; exact ht)
  refine ⟨hinv, fun j info c hi hc => ?_, hP.externsE, hP.instET, fun c hc x hx => hip x (hP.intArgsOf c hc x hx),
    fun c hc x hx => ?_, fun j info hi r hr => ?_, fun j info hi hc => ?_,
    fun j info c hi hc hE t ht => ?_, fun B hB x hx => hip x (hP.termIntOf B hB x hx),
    fun ty s off hc => ?_, hP.callees, hP.indSigs, fun op ty x hc => ?_⟩
  · rcases hins j info hi with h | ⟨h, -⟩
    · exact hP.clifOf j info c h hc
    · rw [h] at hc; cases hc
  · rw [hty]; exact hP.argsTyped c hc x hx
  · rw [hty]
    rcases hins j info hi with h | ⟨-, h, -⟩
    · exact hP.resTyped j info h r hr
    · rw [h] at hr; cases hr
  · rcases hins j info hi with h | ⟨-, -, h⟩
    · exact hP.noClifRes j info h hc
    · exact h
  · rcases hins j info hi with h | ⟨h, -⟩
    · exact hP.resE j info c h hc hE t ht
    · rw [h] at hc; cases hc
  · rw [hso]; exact hP.slots ty s off hc
  · rw [hty]; exact hP.extNarrow op ty x hc

theorem termCtx_insts_casesT {ti : Nat} {data : V} {j : Nat} {info : IInfo}
    (h : (termCtx ctx ti data).insts[j]? = some info) :
    ctx.insts[j]? = some info ∨ (info.clif = none ∧ info.results = [] ∧ info.resTys = []) := by
  by_cases hj : j = ti
  · subst hj
    by_cases hlt : j < ctx.insts.size
    · rw [termCtx_self hlt] at h
      cases h; exact .inr ⟨rfl, rfl, rfl⟩
    · have : (termCtx ctx j data).insts.size = ctx.insts.size := by simp [termCtx]
      have := (Array.getElem?_eq_some_iff.mp h).1
      omega
  · rw [termCtx_insts_ne hj] at h; exact .inl h

/-- **`PInvT` of a terminator's context** (`termCtx`: its data in its placeholder slot). -/
theorem pinv_termCtxT (hP : PInvT f ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (data : V) :
    PInvT f (termCtx ctx ti data) :=
  pinvT_of_insts hP (ctxInvT_termCtx hP.ctxInv hph data) rfl rfl fun _ _ h =>
    termCtx_insts_casesT h

/-- **`PInvT` of a `try_call`'s context** (`tryCtx`: also its return and payload vregs). -/
theorem pinv_tryCtxT (hP : PInvT f ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (data : V) (trs : List Reg × List Reg) :
    PInvT f (tryCtx ctx ti data trs) :=
  pinvT_of_insts hP { ctxInvT_termCtx hP.ctxInv hph data with } rfl rfl fun _ _ h =>
    termCtx_insts_casesT (ti := ti) (data := data) h

end

end Backend.Proof.Prg
