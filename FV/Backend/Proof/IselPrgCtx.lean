import FV.Backend.Proof.IselPrgInv
import FV.Backend.Proof.LowerTotal
import FV.Backend.Proof.IselEmitDriver

/-!
# Progress of the ISLE lowering (V7): the driver's contexts

The input conditions the ISLE progress analysis needs beyond the driver's scope (`iselInB`),
and `PInv` for the contexts the driver lowers in: `buildCtx f`'s (`pinv_build`), a terminator's
(`pinv_termCtx`) and a `try_call`'s (`pinv_tryCtx`).

`PInv`'s fields come from:

* `CtxInv`: `ctxOk_sound`/`ctxOk_complete` (`LowerScope`, from `lowerScopeB`);
* the instructions are `f`'s, results have types: `buildCtx`'s model (`ctxSpec_of`);
* operands have types: dominance (`dominatedB`: every operand is available, so a value of `f`,
  `availOf_defs`) and `buildCtx`'s types of `f`'s values;
* stack slots, callees, `call_indirect` signatures: `iselInB`;
* narrow extends: `extendsWidenB` (`extendsWiden_of`) with the E types.
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64

/-! ## The input conditions -/

/-- `SigOk`, decided: integer parameters and ABI returns (float arguments and results are
outside the ISLE progress analysis), the argument locations compute (`sigArgLocs`:
`i64`-or-narrower `normal` parameters and at most one `sret` one) and at most 8 ABI
returns. -/
def sigOkB (s : Clif.Signature) : Bool :=
  s.params.all (·.ty.isInt) && s.returns.all (·.ty.isInt) &&
    (sigArgLocs s).isOk && decide (s.returns.length ≤ 8)

/-- The statement conditions of `iselInB`. -/
def stmtIselB (f : Clif.Function) : Clif.Inst → Bool
  | .call fn _ | .funcAddr _ fn => match f.extern? fn with
    | some e => sigOkB e.sig
    | none => false
  | .callIndirect sig _ _ => match f.sigDecls.lookup sig with
    | some s => sigOkB s
    | none => false
  | .stackAddr _ s _ => ((slotLayout f.slots).1.lookup s).isSome
  | _ => true

/-- The terminator conditions of `iselInB`. -/
def termIselB (f : Clif.Function) : Clif.Terminator → Bool
  | .ret vs => vs.length == f.sig.returns.length
  | .tryCall _ _ et | .tryCallIndirect _ _ et =>
    decide (et.items.length ≤ maxTryItems) && match f.sigDecls.lookup et.sig with
      | some s => sigOkB s
      | none => false
  | _ => true

/-- **The input conditions of the ISLE progress analysis** (beyond `fnScopeB`'s and
`driverInB`'s):

* every `call`/`func_addr` names a declared callee (Cranelift's verifier: `verify_func_ref`)
  whose signature the aarch64 ABI lowers (`sigOkB`: `compute_arg_locs` succeeds — no `i128`
  or special-purpose parameter, at most one `sret` parameter, an `i64` — and at most 8 ABI
  returns, the return registers x0..x7 without `enable_multi_ret_implicit_sret`; for a `call`
  callee the argument-location part also follows from `lowerScopeB`'s `stackLayoutOk`, the
  return bound does not);
* every `call_indirect`'s and every `try_call`/`try_call_indirect`'s signature declaration
  satisfies `sigOkB` (the same ABI rule);
* every `stack_addr` names a stack slot of the frame (`verify_stack_slot`: a declared slot; the
  frame layout `slotLayout` has every declared slot);
* every `return` passes as many values as the signature returns (`typecheck_return`);
* every exception table has at most `maxTryItems` (8) items — a proof-convenience bound: the
  rule table checks the `try_call` roots for up to 8 items. -/
def iselInB (f : Clif.Function) : Bool :=
  f.blocks.all fun B => B.body.all (fun s => stmtIselB f s.inst) && termIselB f B.term

/-! ## From the conditions -/

theorem sigOk_of {s : Clif.Signature} (h : sigOkB s = true) : SigOk s := by
  simp only [sigOkB, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, h.2⟩
  cases he : sigArgLocs s with
  | ok r => exact ⟨r, rfl⟩
  | error e => rw [he] at h; exact absurd h.1.2 (by simp [Except.isOk, Except.toBool])

theorem stmtIsel_of {f : Clif.Function} (h : iselInB f = true) {c : Clif.Inst} (hc : InstOf f c) :
    stmtIselB f c = true := by
  obtain ⟨B, hB, s, hs, rfl⟩ := hc
  simp only [iselInB, List.all_eq_true, Bool.and_eq_true] at h
  exact (h B hB).1 s hs

theorem termIsel_of {f : Clif.Function} (h : iselInB f = true) {B : Clif.Block} (hB : B ∈ f.blocks) :
    termIselB f B.term = true := by
  simp only [iselInB, List.all_eq_true, Bool.and_eq_true] at h
  exact (h B hB).2

/-! ## Statements of `f` in `buildCtx`'s table -/

theorem instOf_idx {f : Clif.Function} {c : Clif.Inst} (h : InstOf f c) :
    ∃ (bi : Nat) (B : Clif.Block) (j : Nat) (stm : Clif.Stmt), f.blocks[bi]? = some B ∧
      B.body[j]? = some stm ∧ stm.inst = c := by
  obtain ⟨B, hB, s, hs, rfl⟩ := h
  obtain ⟨bi, hbi, e⟩ := List.getElem_of_mem hB
  obtain ⟨j, hj, e'⟩ := List.getElem_of_mem hs
  exact ⟨bi, B, j, s, by rw [List.getElem?_eq_getElem hbi, e], by rw [List.getElem?_eq_getElem hj, e'],
    rfl⟩

section
variable {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}

theorem typed_of_def (sp : CtxSpec f ctx ranges st0) {x : Nat} (hx : x ∈ valueDefs f) :
    (ctx.valueType? x).isSome := by
  obtain ⟨-, t, ht, -⟩ := sp.facts.vals x hx
  rw [ht]; rfl

/-- **`PInv` of `buildCtx`'s context.** -/
theorem pinv_build (hdom : dominatedB f = true) (hs : lowerScopeB f = true)
    (hw : extendsWidenB f = true) (hin : iselInB f = true)
    (hb : buildCtx f = .ok (ctx, ranges, st0)) : PInv f ctx := by
  have sp := ctxSpec_of hb
  have hd := dominated_of hdom
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete (lowerScope_of hs) hb)
  refine ⟨hctx.weak, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j info c hi hc
    rcases sp.insts info (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi)) with
      rfl | ⟨B, hB, s, hs, rfl⟩
    · simp [placeholder] at hc
    · simp only [infoOf, Option.some.injEq] at hc
      exact ⟨B, hB, s, hs, hc⟩
  · intro c hc x hx
    obtain ⟨bi, B, j, stm, hB, hj, rfl⟩ := instOf_idx hc
    exact typed_of_def sp (availOf_defs ((hd.uses ctx ranges st0 hb bi B hB).1 j stm hj x hx))
  · intro j info hi r hr
    rcases sp.insts info (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi)) with
      rfl | ⟨B, hB, s, hs, rfl⟩
    · simp [placeholder] at hr
    · refine typed_of_def sp ?_
      simp only [valueDefs, List.mem_flatMap, List.mem_append]
      exact ⟨B, hB, .inr ⟨s, hs, hr⟩⟩
  · intro ty s off hc
    have h := stmtIsel_of hin hc
    simp only [stmtIselB] at h
    rw [sp.slotOff]; exact h
  · intro c fn hc hk
    have h := stmtIsel_of hin hc
    rcases hk with ⟨args, rfl⟩ | ⟨ty, rfl⟩ <;>
    · simp only [stmtIselB] at h
      cases he : f.extern? fn with
      | none => rw [he] at h; cases h
      | some e => rw [he] at h; exact ⟨e, rfl, sigOk_of h⟩
  · intro sig callee args s hc hs
    have h := stmtIsel_of hin hc
    simp only [stmtIselB, hs] at h
    exact sigOk_of h
  · intro op ty x hc
    obtain ⟨bi, B, j, stm, hB, hj, hst⟩ := instOf_idx hc
    obtain ⟨info, hinfo, hcl, -⟩ := sp.facts.stmt bi B j stm hB hj
    rw [hst] at hcl
    obtain ⟨t, ht, hlt⟩ := extendsWiden_of hw hb _ info op ty x hinfo hcl
    have hte := hctx.valTyE x t ht
    have hE := hctx.instE _ info _ hinfo hcl
    simp only [eCTys, List.mem_cons, List.not_mem_nil, or_false] at hte
    rcases hte with rfl | rfl | rfl | rfl
    · exact ⟨8, ht, .inl rfl⟩
    · exact ⟨16, ht, .inr (.inl rfl)⟩
    · exact ⟨32, ht, .inr (.inr rfl)⟩
    · exfalso
      cases ty <;> simp_all [Compile.instE, Compile.tyE, CTy.ofClif, CTy.bits]

/-- `PInv` survives replacing a terminator's placeholder by an entry without CLIF instruction
or results. -/
theorem pinv_of_insts (hP : PInv f ctx) {ctx' : Ctx} (hinv : CtxInvW f ctx')
    (hvt : ctx'.valTy = ctx.valTy) (hso : ctx'.slotOff = ctx.slotOff)
    (hins : ∀ (j : Nat) (info : IInfo), ctx'.insts[j]? = some info →
      ctx.insts[j]? = some info ∨ (info.clif = none ∧ info.results = [])) : PInv f ctx' := by
  have hty : ∀ x, ctx'.valueType? x = ctx.valueType? x := fun x => by
    simp only [Ctx.valueType?, hvt]
  refine ⟨hinv, fun j info c hi hc => ?_, fun c hc x hx => ?_, fun j info hi r hr => ?_,
    fun ty s off hc => ?_, hP.callees, hP.indSigs, fun op ty x hc => ?_⟩
  · rcases hins j info hi with h | ⟨h, -⟩
    · exact hP.clifOf j info c h hc
    · rw [h] at hc; cases hc
  · rw [hty]; exact hP.argsTyped c hc x hx
  · rw [hty]
    rcases hins j info hi with h | ⟨-, h⟩
    · exact hP.resTyped j info h r hr
    · rw [h] at hr; cases hr
  · rw [hso]; exact hP.slots ty s off hc
  · rw [hty]; exact hP.extNarrow op ty x hc

theorem termCtx_insts_cases {ti : Nat} {data : V} {j : Nat} {info : IInfo}
    (h : (termCtx ctx ti data).insts[j]? = some info) :
    ctx.insts[j]? = some info ∨ (info.clif = none ∧ info.results = []) := by
  by_cases hj : j = ti
  · subst hj
    by_cases hlt : j < ctx.insts.size
    · rw [termCtx_self hlt] at h
      cases h; exact .inr ⟨rfl, rfl⟩
    · have : (termCtx ctx j data).insts.size = ctx.insts.size := by simp [termCtx]
      have := (Array.getElem?_eq_some_iff.mp h).1
      omega
  · rw [termCtx_insts_ne hj] at h; exact .inl h

/-- `ctxInv_termCtx` for `CtxInvW`: a terminator's data in its placeholder slot keeps the
invariant. -/
theorem ctxInvW_termCtx {f : Clif.Function} {ctx : Ctx} (h : CtxInvW f ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (data : V) :
    CtxInvW f (termCtx ctx ti data) := by
  have hne : ∀ x d, ctx.defInst? x = some d → d ≠ ti := by
    intro x d hd e
    subst e
    obtain ⟨info, hi, hx⟩ := h.defInst x d hd
    rw [hph] at hi; cases hi; cases hx
  refine ⟨h.func, fun ii info inst hi hc => ?_, fun ii info inst hi hc => ?_,
    fun ii info inst hi hc => ?_, h.typedSome, fun x d hd => ?_, fun x d info hd hi => ?_, h.slotOff,
    fun ii info hi => ?_, h.valTyE, fun ii info inst x hi hc hx => ?_⟩
  · by_cases e : ii = ti
    · subst e; rw [termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [termCtx_insts_ne e] at hi; exact h.data ii info inst hi hc
  · by_cases e : ii = ti
    · subst e; rw [termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [termCtx_insts_ne e] at hi; exact h.instE ii info inst hi hc
  · by_cases e : ii = ti
    · subst e; rw [termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [termCtx_insts_ne e] at hi; exact h.resTys ii info inst hi hc
  · rw [termCtx_insts_ne (hne x d hd)]; exact h.defInst x d hd
  · rw [termCtx_insts_ne (hne x d hd)] at hi; exact h.defClif x d info hd hi
  · by_cases e : ii = ti
    · subst e; rw [termCtx_insts_self hph] at hi; cases hi; intro t ht; cases ht
    · rw [termCtx_insts_ne e] at hi; exact h.resTysE ii info hi
  · by_cases e : ii = ti
    · subst e; rw [termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [termCtx_insts_ne e] at hi; exact h.addr64 ii info inst x hi hc hx

/-- **`PInv` of a terminator's context** (`termCtx`: its data in its placeholder slot). -/
theorem pinv_termCtx (hP : PInv f ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (data : V) :
    PInv f (termCtx ctx ti data) :=
  pinv_of_insts hP (ctxInvW_termCtx hP.ctxInv hph data) rfl rfl fun _ _ h => termCtx_insts_cases h

/-- **`PInv` of a `try_call`'s context** (`tryCtx`: also its return and payload vregs). -/
theorem pinv_tryCtx (hP : PInv f ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (data : V) (trs : List Reg × List Reg) :
    PInv f (tryCtx ctx ti data trs) :=
  pinv_of_insts hP { ctxInvW_termCtx hP.ctxInv hph data with } rfl rfl fun _ _ h =>
    termCtx_insts_cases (ti := ti) (data := data) h

end

/-! ## Non-vacuity -/

/-- **Non-vacuity of `iselInB`**: it holds on the loop witness of `FV/E2E/LowerDirect.lean`
(`driverWitness`: a `return` of one value) and on the `call`/`try_call` witness
`driverWitnessTry` (a `system_v` callee with one `i64` parameter and return, a one-item exception
table). -/
theorem iselInB_witness : iselInB driverWitness = true ∧ iselInB driverWitnessTry = true := by
  decide

end Backend.Proof.Prg
