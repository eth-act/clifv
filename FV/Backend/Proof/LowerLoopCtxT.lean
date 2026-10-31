import FV.Backend.Proof.LowerLoopCtx
import FV.Backend.Proof.DriverCheckT
import FV.Compile.SubsetT

/-!
# Typed context construction (S11e5 Stage C, slice 1)

On a function of the typed movement scope (`Compile.functionET`, `LowerScopeT`), `buildCtx`'s
context is a float-capable lowering context: `ctxInvT_of : CtxInvT f ctx`, and the checker
accepts it (`ctxOkT_of`: completeness of `ctxOkT`, through `ctxOkT_complete`). The supported
instructions are a separate fact (`InstScopeT ctx`, `instScopeT_of`), not a field of `CtxInvT`;
`CtxInvT` with `InstScopeT` is what `CtxInv` (with its `instE` field) is for the integer scope.

The operands in integer positions (`CtxInvT.intOps`) come from the input typing check
(`Compile.opsTypedT`: no such operand is a float-defined value), not from declaring every value
an integer.

Integer specializations: `LowerScope.toT`, `CtxInv.instScopeT`, `ctxOkT_of_lowerScope`; the
integer results (`ctxOk_of`, `CtxSpec.ctxE`, `CtxInv`) are unchanged.
-/

namespace Backend.Proof

open Backend

/-- `intArgs` is the scope's `Compile.intOperands`. -/
theorem intArgs_eq_intOperands (i : Clif.Inst) : intArgs i = Compile.intOperands i := by
  cases i <;> rfl

/-- **The supported instructions of a float-capable context**: every instruction of `ctx` is
in the typed movement scope (`Compile.instET`). Separate from `CtxInvT`. -/
def InstScopeT (ctx : Ctx) : Prop :=
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
    info.clif = some inst → Compile.instET inst = true

/-- A subset-E context's instructions are in the typed scope. -/
theorem CtxInv.instScopeT {f : Clif.Function} {ctx : Ctx} (h : CtxInv f ctx) : InstScopeT ctx :=
  fun ii info inst hi hc => Compile.instET_of_instE (h.instE ii info inst hi hc)

end Backend.Proof

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- `InstScopeT ctx`, decided. -/
def instScopeOk (ctx : Ctx) : Bool :=
  ctx.insts.toList.all fun info => match info.clif with
    | some i => Compile.instET i
    | none => true

theorem instScopeOk_sound {ctx : Ctx} (h : instScopeOk ctx = true) : InstScopeT ctx := by
  intro ii info inst hi hc
  have := List.all_eq_true.mp h info (by rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? hi)
  simpa [hc] using this

theorem instScopeOk_complete {ctx : Ctx} (h : InstScopeT ctx) : instScopeOk ctx = true := by
  refine List.all_eq_true.mpr fun info hi => ?_
  obtain ⟨ii, hii, e⟩ := List.getElem_of_mem hi
  have hget : ctx.insts[ii]? = some info := by
    rw [← Array.getElem?_toList, List.getElem?_eq_getElem hii, e]
  split
  · exact h ii info _ hget ‹_›
  · rfl

theorem tyIn_complete {l : List CTy} {t : CTy} (h : t ∈ l) : tyIn l t = true :=
  List.any_eq_true.mpr ⟨t, h, decide_eq_true rfl⟩

/-- **`ctxOkT` is complete**: it accepts every float-capable lowering context. -/
theorem ctxOkT_complete {f : Clif.Function} {ctx : Ctx} (h : CtxInvT f ctx) :
    ctxOkT f ctx = true := by
  have hget : ∀ {info}, info ∈ ctx.insts.toList → ∃ ii : Nat, ctx.insts[ii]? = some info := by
    intro info hi
    obtain ⟨ii, hii, e⟩ := List.getElem_of_mem hi
    exact ⟨ii, by rw [← Array.getElem?_toList, List.getElem?_eq_getElem hii, e]⟩
  simp only [ctxOkT, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨h.func, ?_⟩, ?_⟩, ?_⟩, ?_⟩, h.slotOff⟩, ?_⟩, ?_⟩
  · refine List.all_eq_true.mpr fun info hi => ?_
    obtain ⟨ii, hii⟩ := hget hi
    split
    · rename_i i hc
      obtain ⟨tys, hty, h1, h2⟩ := h.resTys ii info i hii hc
      simp only [h.data ii info i hii hc, beq_self_eq_true, ctxResTysOk, hty, h1, h2,
        decide_true, Bool.true_and, Bool.and_true]
      refine List.all_eq_true.mpr fun x hx => ?_
      have hp := h.intOps ii info i hii hc x hx
      unfold intPosOk
      split
      · rename_i t ht; exact tyIn_complete (hp t ht)
      · rfl
    · rfl
  · refine List.all_eq_true.mpr fun x _ => ?_
    split
    · rename_i r hr; simp [h.valueReg x r hr]
    · rfl
  · refine List.all_eq_true.mpr fun x _ => ?_
    split
    · rename_i t ht
      simp [h.typedReg x t ht, tyIn_complete (h.valTyM x t ht)]
    · rfl
  · refine List.all_eq_true.mpr fun x _ => ?_
    split
    · rename_i d hd
      obtain ⟨info, hi, hx⟩ := h.defInst x d hd
      simp [hi, hx, h.defClif x d info hd hi]
    · rfl
  · refine List.all_eq_true.mpr fun info hi => List.all_eq_true.mpr fun t ht => ?_
    obtain ⟨ii, hii⟩ := hget hi
    exact tyIn_complete (h.resTysM ii info hii t ht)
  · refine List.all_eq_true.mpr fun info hi => ?_
    obtain ⟨ii, hii⟩ := hget hi
    split
    · rename_i i hc
      split
      · rename_i x hx; exact decide_eq_true (h.addr64 ii info i x hii hc hx)
      · rfl
    · rfl

/-- `ctxOkT f ctx` decides `CtxInvT f ctx`. -/
theorem ctxOkT_iff {f : Clif.Function} {ctx : Ctx} : ctxOkT f ctx = true ↔ CtxInvT f ctx :=
  ⟨ctxOkT_sound, ctxOkT_complete⟩

/-- **The other input conditions of the typed lowering** (`LowerScope` with the typed movement
scope `Compile.functionET` in place of subset E). -/
structure LowerScopeT (f : Clif.Function) : Prop where
  /-- the typed movement scope -/
  subsetT : Compile.functionET f = true
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
  indStackLayout : ∀ s ∈ indSigs f, stackLayoutOk s = true

/-- **Integer specialization**: the integer scope is in the typed one. -/
theorem LowerScope.toT {f : Clif.Function} (hs : LowerScope f) : LowerScopeT f :=
  ⟨Compile.functionET_of_functionE hs.subsetE, hs.nonempty, hs.noEntryPred, hs.ctxFacts,
    hs.tryRet, hs.stackLayout, hs.indStackLayout⟩

/-- The externs of a typed-scope function have integer signatures. -/
theorem LowerScopeT.externsE {f : Clif.Function} (hs : LowerScopeT f) :
    f.externs.all (Compile.sigE ·.2.sig) = true := by
  have h := hs.subsetT
  simp only [Compile.functionET, Bool.and_eq_true] at h
  exact h.1.1.1.2

/-! ## Construction -/

theorem mem_mCTys_of_valTyOk {ty : Clif.Ty} (h : valTyOk ty = true) : CTy.ofClif ty ∈ mCTys := by
  cases ty <;> simp_all [valTyOk, eTy, Clif.Ty.isInt, Clif.Ty.isFloat, CTy.ofClif, mCTys, eCTys]

theorem mem_eCTys_of_not_float {ty : Clif.Ty} (h : valTyOk ty = true) (hf : ty.isFloat = false) :
    CTy.ofClif ty ∈ eCTys := by
  cases ty <;> simp_all [valTyOk, eTy, Clif.Ty.isInt, Clif.Ty.isFloat, CTy.ofClif, eCTys]

section
variable {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}

/-- A context instruction is `buildCtx`'s entry of a statement of `f`. -/
theorem CtxSpec.inst_of (sp : CtxSpec f ctx ranges st0) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst) :
    ∃ B ∈ f.blocks, ∃ s ∈ B.body, info = infoOf f s ∧ inst = s.inst := by
  rcases sp.insts info (by rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? hi) with
    rfl | ⟨B, hB, s, hs, rfl⟩
  · simp [placeholder] at hc
  · simp only [infoOf, Option.some.injEq] at hc
    exact ⟨B, hB, s, hs, rfl, hc.symm⟩

/-- A value no float definition of `f` defines has an E type. -/
theorem CtxSpec.eCTys_of_not_floatDef (sp : CtxSpec f ctx ranges st0) {x : Nat} {t : CTy}
    (ht : ctx.valueType? x = some t) (hx : x ∉ Compile.floatDefs f) : t ∈ eCTys := by
  rcases sp.tyOf x t ht with ⟨B, hB, q, hq, rfl, rfl⟩ | ⟨B, hB, s, hs, m, ty, hm, hty, rfl⟩
  · refine mem_eCTys_of_not_float ((sp.blockC B hB).1 q hq) ?_
    cases hf : q.2.isFloat
    · rfl
    · exact absurd (by
        simp only [Compile.floatDefs, List.mem_flatMap, List.mem_append, List.mem_map,
          List.mem_filter]
        exact ⟨B, hB, .inl ⟨q, ⟨hq, hf⟩, rfl⟩⟩) hx
  · have hsc := (sp.blockC B hB).2 s hs
    refine mem_eCTys_of_not_float (hsc.2.2 ty (List.mem_of_getElem? hty)) ?_
    cases hci : Compile.isCallIndirect s.inst
    · cases hf : ty.isFloat
      · rfl
      · refine absurd ?_ hx
        simp only [Compile.floatDefs, List.mem_flatMap, List.mem_append, List.mem_map,
          List.mem_filter]
        refine ⟨B, hB, .inr ⟨s, hs, ?_⟩⟩
        simp only [hci, Bool.false_eq_true, ite_false, List.mem_map, List.mem_filter]
        refine ⟨(x, ty), ⟨?_, hf⟩, rfl⟩
        have : (s.results.zip (tysOf f s))[m]? = some (x, ty) := by
          rw [List.getElem?_zip_eq_some]; exact ⟨hm, hty⟩
        exact List.mem_of_getElem? this
    · obtain ⟨res, inst⟩ := s
      cases inst with
      | callIndirect sig c args =>
        obtain ⟨d, hd⟩ := hsc.1
        cases hl : f.sigDecls.lookup sig with
        | none => simp [tysOf, Clif.Inst.resultTypes, hl] at hty
        | some sg =>
          have hmem : ty ∈ tysOf f ⟨res, .callIndirect sig c args⟩ := List.mem_of_getElem? hty
          simp only [tysOf, Clif.Inst.resultTypes, hl, Option.map_some, Option.getD_some,
            List.mem_map] at hmem
          obtain ⟨p, hp, rfl⟩ := hmem
          have := List.all_eq_true.mp (sigIntB_iff.mp (instData_callIndirect_int hd hl)).2 p hp
          revert this; cases p.ty <;> decide
      | _ => simp [Compile.isCallIndirect] at hci

/-- The operands in integer positions of a typed-scope function's instructions are integers. -/
theorem CtxSpec.intOps_of (sp : CtxSpec f ctx ranges st0) (hT : Compile.functionET f = true) :
    ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
      info.clif = some inst → ∀ x ∈ intArgs inst, IntPos ctx x := by
  intro ii info inst hi hc x hx t ht
  obtain ⟨B, hB, s, hs, -, rfl⟩ := sp.inst_of hi hc
  refine sp.eCTys_of_not_floatDef ht fun hfd => ?_
  simp only [Compile.functionET, Compile.opsTypedT, Bool.and_eq_true, List.all_eq_true] at hT
  have := (hT.1.2 B hB).1 s hs x (by rw [← intArgs_eq_intOperands]; exact hx)
  simp [hfd] at this

/-- The instructions of `buildCtx`'s context of a typed-scope function are in the scope. -/
theorem CtxSpec.instScopeT (sp : CtxSpec f ctx ranges st0) (hT : Compile.functionET f = true) :
    InstScopeT ctx := by
  intro ii info inst hi hc
  obtain ⟨B, hB, s, hs, -, rfl⟩ := sp.inst_of hi hc
  simp only [Compile.functionET, Bool.and_eq_true, List.all_eq_true] at hT
  exact (hT.1.1.2 B hB).1.2 s hs

/-- **`buildCtx` on the typed scope gives a float-capable lowering context.** -/
theorem ctxInvT_of (hs : LowerScopeT f) (hb : buildCtx f = .ok (ctx, ranges, st0)) :
    CtxInvT f ctx := by
  have sp := ctxSpec_of hb
  refine ⟨sp.func, ?_, ?_, ?_, ?_, ?_, ?_, sp.slotOff, ?_, ?_, (hs.ctxFacts ctx ranges st0 hb).2,
    sp.intOps_of hs.subsetT⟩
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

/-- **`buildCtx`'s context passes `ctxOkT` on typed-scope input** (completeness). -/
theorem ctxOkT_of (hs : LowerScopeT f) (hb : buildCtx f = .ok (ctx, ranges, st0)) :
    ctxOkT f ctx = true :=
  ctxOkT_complete (ctxInvT_of hs hb)

/-- **Typed context construction**: on the typed scope, `buildCtx`'s context passes `ctxOkT`,
is a float-capable lowering context, and its instructions are in the typed scope. -/
theorem buildCtx_typed (hs : LowerScopeT f) (hb : buildCtx f = .ok (ctx, ranges, st0)) :
    ctxOkT f ctx = true ∧ CtxInvT f ctx ∧ InstScopeT ctx :=
  ⟨ctxOkT_of hs hb, ctxInvT_of hs hb, (ctxSpec_of hb).instScopeT hs.subsetT⟩

/-- Integer specialization of `ctxOkT_of`. -/
theorem ctxOkT_of_lowerScope (hs : LowerScope f) (hb : buildCtx f = .ok (ctx, ranges, st0)) :
    ctxOkT f ctx = true :=
  ctxOkT_of hs.toT hb

/-! ## Edge classes -/

theorem valClass_ofClif_eq {ty ty' : Clif.Ty} (hv : valTyOk ty = true) (hv' : valTyOk ty' = true)
    (hf : ty.isFloat = ty'.isFloat) : (CTy.ofClif ty).valClass = (CTy.ofClif ty').valClass := by
  cases ty <;> cases ty' <;> simp_all [valTyOk, eTy, Clif.Ty.isInt, Clif.Ty.isFloat, CTy.ofClif,
    CTy.valClass, CTy.regClass?]

theorem valTyOk_of_tyM {ty : Clif.Ty} (h : Compile.tyM ty = true) : valTyOk ty = true := by
  cases ty <;> simp_all [Compile.tyM, Compile.tyE, valTyOk, eTy, Clif.Ty.isInt, Clif.Ty.isFloat]

/-- **A class-checked argument has its target's class**: a value `a` passed where type `ty` is
expected (`Compile.argClassOk`) has, in `buildCtx`'s context, a type of `ty`'s class. -/
theorem CtxSpec.class_of_argClassOk (sp : CtxSpec f ctx ranges st0) {a : Nat} {ty : Clif.Ty}
    (h : Compile.argClassOk (Compile.defFloats f) a ty = true) (hv : valTyOk ty = true) :
    ∀ t, ctx.valueType? a = some t → t.valClass = (CTy.ofClif ty).valClass := by
  intro t ht
  have hchk : ∀ fl, (a, fl) ∈ Compile.defFloats f → fl = ty.isFloat := by
    intro fl hm
    have := List.all_eq_true.mp h _ hm
    simpa using this
  rcases sp.tyOf a t ht with ⟨B, hB, q, hq, rfl, rfl⟩ | ⟨B, hB, s, hs, m, ty', hm, hty, rfl⟩
  · refine valClass_ofClif_eq ((sp.blockC B hB).1 q hq) hv (hchk _ ?_)
    simp only [Compile.defFloats, List.mem_flatMap, List.mem_append, List.mem_map]
    exact ⟨B, hB, .inl ⟨q, hq, rfl⟩⟩
  · have hsc := (sp.blockC B hB).2 s hs
    refine valClass_ofClif_eq (hsc.2.2 ty' (List.mem_of_getElem? hty)) hv ?_
    cases hci : Compile.isCallIndirect s.inst
    · refine hchk _ ?_
      simp only [Compile.defFloats, List.mem_flatMap, List.mem_append, List.mem_map]
      refine ⟨B, hB, .inr ⟨s, hs, ?_⟩⟩
      simp only [hci, Bool.false_eq_true, ite_false, List.mem_map]
      refine ⟨(a, ty'), ?_, rfl⟩
      have : (s.results.zip (tysOf f s))[m]? = some (a, ty') := by
        rw [List.getElem?_zip_eq_some]; exact ⟨hm, hty⟩
      exact List.mem_of_getElem? this
    · have h1 : false = ty.isFloat := hchk false (by
        simp only [Compile.defFloats, List.mem_flatMap, List.mem_append, List.mem_map]
        refine ⟨B, hB, .inr ⟨s, hs, ?_⟩⟩
        simp only [hci, ite_true, List.mem_map]
        exact ⟨a, List.mem_of_getElem? hm, rfl⟩)
      rw [← h1]
      obtain ⟨res, inst⟩ := s
      cases inst with
      | callIndirect sig c args =>
        obtain ⟨d, hd⟩ := hsc.1
        cases hl : f.sigDecls.lookup sig with
        | none => simp [tysOf, Clif.Inst.resultTypes, hl] at hty
        | some sg =>
          have hmem : ty' ∈ tysOf f ⟨res, .callIndirect sig c args⟩ := List.mem_of_getElem? hty
          simp only [tysOf, Clif.Inst.resultTypes, hl, Option.map_some, Option.getD_some,
            List.mem_map] at hmem
          obtain ⟨p, hp, rfl⟩ := hmem
          have := List.all_eq_true.mp (sigIntB_iff.mp (instData_callIndirect_int hd hl)).2 p hp
          revert this; cases p.ty <;> decide
      | _ => simp [Compile.isCallIndirect] at hci

theorem blockCalls_eq_dests (t : Clif.Terminator) : Compile.blockCalls t = dests t := by
  cases t <;> rfl

theorem block?_mem {f : Clif.Function} {b : Clif.BlockId} {tb : Clif.Block}
    (h : f.block? b = some tb) : tb ∈ f.blocks := List.mem_of_find?_eq_some h

/-- **Branch arguments have their target parameters' classes** (typed scope). -/
theorem CtxSpec.edgeClass (sp : CtxSpec f ctx ranges st0) (hT : Compile.functionET f = true)
    {B : Clif.Block} (hB : B ∈ f.blocks) {bc : Clif.BlockCall} (hbc : bc ∈ dests B.term)
    {tb : Clif.Block} (htb : f.block? bc.block = some tb) {a : Nat} {p : Clif.ValueId × Clif.Ty}
    (hap : (a, p) ∈ bc.args.zip tb.params) :
    ∀ t, ctx.valueType? a = some t → t.valClass = (CTy.ofClif p.2).valClass := by
  simp only [Compile.functionET, Compile.edgeClassOk, Bool.and_eq_true, List.all_eq_true] at hT
  have h := (hT.2 B hB).1 bc (by rw [blockCalls_eq_dests]; exact hbc)
  rw [htb] at h
  exact sp.class_of_argClassOk (List.all_eq_true.mp h _ hap)
    ((sp.blockC tb (block?_mem htb)).1 p (List.of_mem_zip hap).2)

/-- **A `try_call`'s value arguments have their target parameters' classes** (typed scope). -/
theorem CtxSpec.tryEdgeClass (sp : CtxSpec f ctx ranges st0) (hT : Compile.functionET f = true)
    {B : Clif.Block} (hB : B ∈ f.blocks) {et : Clif.ExnTable} (het : IsTryWith B.term et)
    {td : Clif.TryDest} (htd : td ∈ et.dests) {tb : Clif.Block} (htb : f.block? td.block = some tb)
    {v : Nat} {p : Clif.ValueId × Clif.Ty} (hap : (Clif.TryArg.val v, p) ∈ td.args.zip tb.params) :
    ∀ t, ctx.valueType? v = some t → t.valClass = (CTy.ofClif p.2).valClass := by
  simp only [Compile.functionET, Compile.edgeClassOk, Bool.and_eq_true, List.all_eq_true] at hT
  have h := (hT.2 B hB).2
  have hv := (sp.blockC tb (block?_mem htb)).1 p (List.of_mem_zip hap).2
  rcases het with ⟨fn, args, he⟩ | ⟨c, args, he⟩ <;> rw [he] at h <;> simp only at h <;>
  · have h2 := List.all_eq_true.mp h td htd
    rw [htb] at h2
    have h3 := List.all_eq_true.mp h2 _ hap
    exact sp.class_of_argClassOk h3 hv

/-- **Returned values have the signature's return classes** (typed scope). -/
theorem CtxSpec.retClass (sp : CtxSpec f ctx ranges st0) (hT : Compile.functionET f = true)
    {B : Clif.Block} (hB : B ∈ f.blocks) {vs : List Nat} (hr : B.term = .ret vs) {v : Nat}
    {p : Clif.AbiParam} (hvp : (v, p) ∈ vs.zip f.sig.returns) :
    ∀ t, ctx.valueType? v = some t → t.valClass = (CTy.ofClif p.ty).valClass := by
  have hsig := hT
  simp only [Compile.functionET, Compile.edgeClassOk, Bool.and_eq_true, List.all_eq_true] at hT
  have h := (hT.2 B hB).2
  rw [hr] at h
  simp only [List.all_eq_true] at h
  simp only [Compile.functionET, Compile.sigET, Bool.and_eq_true, List.all_eq_true] at hsig
  exact sp.class_of_argClassOk (h _ hvp)
    (valTyOk_of_tyM (hsig.1.1.1.1.1.2 p (List.of_mem_zip hvp).2))

end

end Backend.Proof.Driver
