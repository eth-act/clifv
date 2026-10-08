import FV.Backend.Proof.StockContext
import FV.Backend.Proof.LowerLoopCtx

/-! Transport source/DFG facts to stock's dense register context. -/

namespace Backend.Stock.Proof

open Backend.Proof Backend.Proof.Driver

/-- Fields read by source typing and pure-definition look-through. Register
assignments and exception temporaries may differ independently. -/
structure DFGViewEq (ctx original : Ctx) : Prop where
  func : ctx.func = original.func
  insts : ctx.insts = original.insts
  valTy : ctx.valTy = original.valTy
  valDef : ctx.valDef = original.valDef
  slotOff : ctx.slotOff = original.slotOff

theorem DFGViewEq.frameTyped_iff {ctx original : Ctx} (h : DFGViewEq ctx original)
    (fr : Clif.Frame) : FrameTyped ctx fr ↔ FrameTyped original fr := by
  simp only [FrameTyped, Ctx.valueType?, h.valTy]

theorem DFGViewEq.dfgCons_iff {ctx original : Ctx} (h : DFGViewEq ctx original)
    (fr : Clif.Frame) : DFGCons ctx fr ↔ DFGCons original fr := by
  simp only [DFGCons, Ctx.defInst?, h.valDef, h.insts, h.frameTyped_iff fr]

/-- Every successful stock context retains the validated original DFG view,
including canonical source ranges and statement/definition/type facts. -/
theorem buildCtx_source {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st : State}
    (hb : Stock.buildCtx f = .ok (ctx, ranges, st)) :
    ∃ original st0, Backend.buildCtx f = .ok (original, ranges, st0) ∧
      CtxSpec f original ranges st0 ∧ DFGViewEq ctx original := by
  obtain ⟨original, st0, requests, hold, _, he⟩ := buildCtx_allocation hb
  have hc := congrArg (fun q => q.1) he
  dsimp only at hc
  refine ⟨original, st0, hold, ctxSpec_of hold, ?_⟩
  rw [hc]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem typed_declared {f : Clif.Function} {original : Ctx}
    {ranges : Array (Nat × Nat)} {st0 : LState} (sp : CtxSpec f original ranges st0)
    {x : Nat} {t : CTy} (ht : original.valueType? x = some t) : x ∈ valueDefs f := by
  rcases sp.tyOf x t ht with ⟨B, hB, p, hp, rfl, _⟩ |
    ⟨B, hB, s, hs, m, ty, hm, _, _⟩
  · simp only [valueDefs, List.mem_flatMap, List.mem_append, List.mem_map]
    exact ⟨B, hB, Or.inl ⟨p, hp, rfl⟩⟩
  · simp only [valueDefs, List.mem_flatMap, List.mem_append, List.mem_map]
    exact ⟨B, hB, Or.inr ⟨s, hs, List.mem_of_getElem? hm⟩⟩

/-- Every typed source value has its own mapped integer register. No assumption
equates a CLIF value ID with a register number. -/
theorem buildCtx_typedReg {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st : State}
    (hb : Stock.buildCtx f = .ok (ctx, ranges, st)) {x : Nat} {t : CTy}
    (ht : ctx.valueType? x = some t) :
    ∃ n, ctx.valueReg? x = some (.vreg n .int) ∧
      firstUserVreg ≤ n ∧ n < st.base.nextVreg := by
  obtain ⟨original, st0, _, sp, view⟩ := buildCtx_source hb
  have ht0 : original.valueType? x = some t := by
    simpa only [Ctx.valueType?, view.valTy] using ht
  have hdecl := typed_declared sp ht0
  have hx : x < ctx.valTy.size := by
    rw [view.valTy, sp.facts.size.2.2, ← sp.facts.size.1]
    exact (sp.facts.vals x hdecl).1
  have hdecl' : x ∈ f.blocks.flatMap blockValues := hdecl
  have hsome := (buildCtx_value_domain hb x hx).mpr hdecl'
  cases hr : ctx.valueReg? x with
  | none => rw [hr] at hsome; cases hsome
  | some r =>
    have allocated := buildCtx_allocated hb
    obtain ⟨n, rfl, hlo⟩ := allocated.2.2.1 x r hr
    exact ⟨n, rfl, hlo, allocated.1 x n hr⟩

/-- Source and mapping assumptions for rule proofs, independent of identity
register numbering. Bound preservation is carried separately by CtxAllocated. These source fields
are transported from CtxInv by name. Factoring the production CtxInv structure
is deferred to avoid changing its existing proof interface in this slice. -/
structure MappedCtxInv (f : Clif.Function) (ctx : Ctx) : Prop where
  func : ctx.func = f
  data : ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
    instData f inst = .ok info.data
  instE : ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
    Compile.instE inst = true
  resTys : ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
    ∃ (tys : List Clif.Ty), inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) = some tys ∧
      info.resTys = tys.map CTy.ofClif ∧ info.results.length = tys.length
  valueReg : ∀ (x : Nat) (r : Reg), ctx.valueReg? x = some r → ∃ n, r = .vreg n .int
  typedReg : ∀ (x : Nat) (t : CTy), ctx.valueType? x = some t → ∃ n, ctx.valueReg? x = some (.vreg n .int)
  injective : ValueMapInjective ctx
  defInst : ∀ (x d : Nat), ctx.defInst? x = some d → ∃ info, ctx.insts[d]? = some info ∧ x ∈ info.results
  defClif : ∀ (x d : Nat) (info : IInfo), ctx.defInst? x = some d → ctx.insts[d]? = some info → info.clif.isSome = true
  slotOff : ctx.slotOff = (slotLayout f.slots).1
  resTysE : ∀ (ii : Nat) (info : IInfo), ctx.insts[ii]? = some info → ∀ t ∈ info.resTys, t ∈ eCTys
  valTyE : ∀ (x : Nat) (t : CTy), ctx.valueType? x = some t → t ∈ eCTys
  addr64 : ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst) (x : Nat), ctx.insts[ii]? = some info → info.clif = some inst →
    memAddr? inst = some x → ctx.valueType? x = some (.int 64)

/-- The original lowering input condition suffices for source facts in the
stock context; successful construction supplies the new mapping facts. -/
theorem buildCtx_mappedInv {f : Clif.Function} (hs : LowerScope f) {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st : State}
    (hb : Stock.buildCtx f = .ok (ctx, ranges, st)) : MappedCtxInv f ctx := by
  obtain ⟨original, st0, hold, _, view⟩ := buildCtx_source hb
  have old := ctxOk_sound (ctxOk_of hs hold)
  have allocated := buildCtx_allocated hb
  refine { func := view.func.trans old.func, data := ?_, instE := ?_, resTys := ?_,
    valueReg := ?_, typedReg := ?_, injective := allocated.2.1, defInst := ?_,
    defClif := ?_, slotOff := view.slotOff.trans old.slotOff, resTysE := ?_,
    valTyE := ?_, addr64 := ?_ }
  · intro ii info inst hi hc
    exact old.data ii info inst (by simpa only [view.insts] using hi) hc
  · intro ii info inst hi hc
    exact old.instE ii info inst (by simpa only [view.insts] using hi) hc
  · intro ii info inst hi hc
    exact old.resTys ii info inst (by simpa only [view.insts] using hi) hc
  · intro x r hr
    obtain ⟨n, hn, _⟩ := allocated.2.2.1 x r hr
    exact ⟨n, hn⟩
  · intro x t ht
    obtain ⟨n, hn, _, _⟩ := buildCtx_typedReg hb ht
    exact ⟨n, hn⟩
  · intro x d hd
    have hd0 : original.defInst? x = some d := by simpa only [Ctx.defInst?, view.valDef] using hd
    obtain ⟨info, hi, hx⟩ := old.defInst x d hd0
    exact ⟨info, by simpa only [view.insts] using hi, hx⟩
  · intro x d info hd hi
    exact old.defClif x d info (by simpa only [Ctx.defInst?, view.valDef] using hd)
      (by simpa only [view.insts] using hi)
  · intro ii info hi t ht
    exact old.resTysE ii info (by simpa only [view.insts] using hi) t ht
  · intro x t ht
    exact old.valTyE x t (by simpa only [Ctx.valueType?, view.valTy] using ht)
  · intro ii info inst x hi hc hx
    have ht := old.addr64 ii info inst x (by simpa only [view.insts] using hi) hc hx
    simpa only [Ctx.valueType?, view.valTy] using ht

theorem MappedCtxInv.withTryRegs {f : Clif.Function} {ctx : Ctx} (h : MappedCtxInv f ctx)
    (regs : List Reg × List Reg) : MappedCtxInv f { ctx with tryRegs := regs } :=
  { func := h.func, data := h.data, instE := h.instE, resTys := h.resTys,
    valueReg := h.valueReg, typedReg := h.typedReg, injective := h.injective,
    defInst := h.defInst, defClif := h.defClif, slotOff := h.slotOff,
    resTysE := h.resTysE, valTyE := h.valTyE, addr64 := h.addr64 }

private theorem definition_ne_term {f : Clif.Function} {ctx : Ctx}
    (h : MappedCtxInv f ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {x d : Nat}
    (hd : ctx.defInst? x = some d) : d ≠ ti := by
  intro he
  subst d
  obtain ⟨info, hi, hx⟩ := h.defInst x ti hd
  rw [hph] at hi
  cases hi
  cases hx

theorem MappedCtxInv.termCtx {f : Clif.Function} {ctx : Ctx} (h : MappedCtxInv f ctx)
    {ti : Nat} (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (data : Backend.V) :
    MappedCtxInv f (Driver.termCtx ctx ti data) := by
  refine { func := h.func, data := ?_, instE := ?_, resTys := ?_, valueReg := h.valueReg,
    typedReg := h.typedReg, injective := h.injective, defInst := ?_, defClif := ?_,
    slotOff := h.slotOff, resTysE := ?_, valTyE := h.valTyE, addr64 := ?_ }
  · intro ii info inst hi hc
    by_cases he : ii = ti
    · subst ii; rw [termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [termCtx_insts_ne he] at hi; exact h.data ii info inst hi hc
  · intro ii info inst hi hc
    by_cases he : ii = ti
    · subst ii; rw [termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [termCtx_insts_ne he] at hi; exact h.instE ii info inst hi hc
  · intro ii info inst hi hc
    by_cases he : ii = ti
    · subst ii; rw [termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [termCtx_insts_ne he] at hi; exact h.resTys ii info inst hi hc
  · intro x d hd
    rw [termCtx_insts_ne (definition_ne_term h hph hd)]
    exact h.defInst x d hd
  · intro x d info hd hi
    rw [termCtx_insts_ne (definition_ne_term h hph hd)] at hi
    exact h.defClif x d info hd hi
  · intro ii info hi t ht
    by_cases he : ii = ti
    · subst ii; rw [termCtx_insts_self hph] at hi; cases hi; cases ht
    · rw [termCtx_insts_ne he] at hi; exact h.resTysE ii info hi t ht
  · intro ii info inst x hi hc hx
    by_cases he : ii = ti
    · subst ii; rw [termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [termCtx_insts_ne he] at hi; exact h.addr64 ii info inst x hi hc hx

theorem MappedCtxInv.dfgCons_termCtx_iff {f : Clif.Function} {ctx : Ctx}
    (h : MappedCtxInv f ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (data : Backend.V) (fr : Clif.Frame) :
    DFGCons (Driver.termCtx ctx ti data) fr ↔ DFGCons ctx fr := by
  constructor
  · rintro ⟨hd, ht⟩
    refine ⟨?_, ht⟩
    intro x j info cl v hdef hi hc hp hv
    exact hd x j info cl v hdef (by rw [termCtx_insts_ne (definition_ne_term h hph hdef)]; exact hi)
      hc hp hv
  · rintro ⟨hd, ht⟩
    refine ⟨?_, ht⟩
    intro x j info cl v hdef hi hc hp hv
    rw [termCtx_insts_ne (definition_ne_term h hph hdef)] at hi
    exact hd x j info cl v hdef hi hc hp hv

/-! Non-vacuity uses a successful sparse-ID context with a defined pure constant.
Only its source context is evaluated; no ISLE interpreter program is run. -/


private def fixture : Clif.Function := {
  name := "mapped_dfg"
  sig := { params := [⟨.i64, .none, .normal⟩], returns := [⟨.i8, .none, .normal⟩] }
  blocks := [{ id := 5, params := [(7, .i64)], body := [⟨[2], .iconst .i8 9⟩], term := .ret [2] }] }

private def fixtureResult : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx fixture).toOption.getD (sinkCtx, #[], sinkState)

private def originalResult : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx fixture).toOption.getD (sinkCtx, #[], sinkState.base)

set_option maxRecDepth 4096 in
private theorem fixture_build : Stock.buildCtx fixture = .ok fixtureResult := rfl

set_option maxRecDepth 4096 in
private theorem fixture_original_build :
    Backend.buildCtx fixture = .ok (originalResult.1, originalResult.2.1, originalResult.2.2) := rfl

set_option maxRecDepth 4096 in
private theorem fixture_scope : LowerScope fixture := by
  refine ⟨by decide, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · intro B hB b hb
    simp [fixture] at hB
    subst B
    cases hb
  · intro ctx ranges st0 hb
    refine ⟨rfl, ?_⟩
    intro ii info inst x hi hc hm
    have sp := ctxSpec_of hb
    have hmem := Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi)
    rcases sp.insts info hmem with hph | ⟨B, hB, s, hs, he⟩
    · rw [hph] at hc
      cases hc
    · simp [fixture] at hB
      subst B
      simp only [List.mem_singleton] at hs
      subst s
      rw [he] at hc
      change some (Clif.Inst.iconst .i8 9) = some inst at hc
      cases hc
      cases hm
  · intro B hB et ht
    simp [fixture] at hB
    subst B
    rcases ht with ⟨fn, args, he⟩ | ⟨callee, args, he⟩ <;> cases he
  · intro B hB s hs fn args e hi _
    simp [fixture] at hB
    subst B
    simp only [List.mem_singleton] at hs
    subst s
    cases hi
  · intro B hB fn args et e ht _
    simp [fixture] at hB
    subst B
    cases ht

set_option maxRecDepth 4096 in
private theorem fixture_view : DFGViewEq fixtureResult.1 originalResult.1 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

private def fixtureFrame : Clif.Frame := {
  func := fixture
  regs := fun x => if x = 2 then some (.ofInt .i8 9) else
    if x = 7 then some (.ofInt .i64 4) else none
  slots := [], body := [], term := .ret [2] }

set_option maxRecDepth 4096 in
private theorem fixture_typed : FrameTyped fixtureResult.1 fixtureFrame := by
  intro x t v ht hv
  by_cases he : x = 2
  · subst x
    change some (.int 8) = some t at ht
    cases ht
    change some (Clif.Val.ofInt .i8 9) = some v at hv
    cases hv
    rfl
  · by_cases he' : x = 7
    · subst x
      change some (.int 64) = some t at ht
      cases ht
      change some (Clif.Val.ofInt .i64 4) = some v at hv
      cases hv
      rfl
    · simp [fixtureFrame, he, he'] at hv

set_option maxRecDepth 4096 in
private theorem fixture_dfg : DFGCons fixtureResult.1 fixtureFrame := by
  refine ⟨?_, fixture_typed⟩
  intro x j info cl v hd hi hc _ hv
  by_cases he : x = 2
  · subst x
    change some 0 = some j at hd
    cases hd
    change some fixtureResult.1.insts[0]! = some info at hi
    cases hi
    change some (Clif.Inst.iconst .i8 9) = some cl at hc
    cases hc
    change some (Clif.Val.ofInt .i8 9) = some v at hv
    cases hv
    exact ⟨[.ofInt .i8 9], fun _ => rfl, rfl⟩
  · by_cases he' : x = 7
    · subst x
      change none = some j at hd
      cases hd
    · simp [fixtureFrame, he, he'] at hv

theorem DFGViewEq.frameTyped_iff_witness :
    DFGViewEq fixtureResult.1 originalResult.1 ∧
    FrameTyped fixtureResult.1 fixtureFrame ∧ FrameTyped originalResult.1 fixtureFrame ∧
    fixtureResult.1.valueReg? 2 = some (.vreg 193 .int) ∧
    originalResult.1.valueReg? 2 = some (.vreg 2 .int) :=
  ⟨fixture_view, fixture_typed, (fixture_view.frameTyped_iff _).mp fixture_typed, rfl,
    ((ctxSpec_of fixture_original_build).facts.vals 2 (by simp [valueDefs, fixture])).2⟩

theorem DFGViewEq.dfgCons_iff_witness :
    DFGViewEq fixtureResult.1 originalResult.1 ∧
    DFGCons fixtureResult.1 fixtureFrame ∧ DFGCons originalResult.1 fixtureFrame ∧
    fixtureResult.1.defInst? 2 = some 0 ∧ fixtureFrame.regs 2 = some (.ofInt .i8 9) :=
  ⟨fixture_view, fixture_dfg, (fixture_view.dfgCons_iff _).mp fixture_dfg, rfl, rfl⟩

set_option maxRecDepth 4096 in
theorem buildCtx_source_witness :
    Stock.buildCtx fixture = .ok fixtureResult ∧
    (∃ original st0, Backend.buildCtx fixture = .ok (original, fixtureResult.2.1, st0) ∧
      CtxSpec fixture original fixtureResult.2.1 st0 ∧ DFGViewEq fixtureResult.1 original) :=
  ⟨fixture_build, buildCtx_source fixture_build⟩

theorem buildCtx_typedReg_witness :
    fixtureResult.1.valueType? 2 = some (.int 8) ∧
    (∃ n, fixtureResult.1.valueReg? 2 = some (.vreg n .int) ∧
      firstUserVreg ≤ n ∧ n < fixtureResult.2.2.base.nextVreg) ∧
    fixtureResult.1.valueReg? 2 = some (.vreg 193 .int) :=
  ⟨rfl, buildCtx_typedReg fixture_build (x := 2) rfl, rfl⟩

set_option maxRecDepth 4096 in
private theorem fixture_inv : MappedCtxInv fixture fixtureResult.1 :=
  buildCtx_mappedInv fixture_scope fixture_build

theorem buildCtx_mappedInv_witness :
    LowerScope fixture ∧ Stock.buildCtx fixture = .ok fixtureResult ∧
    MappedCtxInv fixture fixtureResult.1 ∧
    fixtureResult.1.valueReg? 2 = some (.vreg 193 .int) :=
  ⟨fixture_scope, fixture_build, fixture_inv, rfl⟩

private def tryRegs : List Reg × List Reg := ([.vreg 194 .int], [.vreg 195 .int, .vreg 196 .int])

private def termData : Backend.V := .data 152 9 []

theorem MappedCtxInv.withTryRegs_witness :
    MappedCtxInv fixture fixtureResult.1 ∧
    MappedCtxInv fixture { fixtureResult.1 with tryRegs } ∧
    ({ fixtureResult.1 with tryRegs } : Ctx).tryRegs = tryRegs :=
  ⟨fixture_inv, fixture_inv.withTryRegs tryRegs, rfl⟩

theorem MappedCtxInv.termCtx_witness :
    MappedCtxInv fixture fixtureResult.1 ∧
    fixtureResult.1.insts[1]? = some ⟨.op .unit, [], [], none⟩ ∧
    MappedCtxInv fixture (Driver.termCtx fixtureResult.1 1 termData) ∧
    (Driver.termCtx fixtureResult.1 1 termData).insts[1]? =
      some ⟨termData, [], [], none⟩ :=
  ⟨fixture_inv, rfl, fixture_inv.termCtx (ti := 1) rfl termData, rfl⟩

theorem MappedCtxInv.dfgCons_termCtx_iff_witness :
    MappedCtxInv fixture fixtureResult.1 ∧ DFGCons fixtureResult.1 fixtureFrame ∧
    DFGCons (Driver.termCtx fixtureResult.1 1 termData) fixtureFrame ∧
    fixtureResult.1.defInst? 2 = some 0 ∧ fixtureFrame.regs 2 = some (.ofInt .i8 9) :=
  ⟨fixture_inv, fixture_dfg,
    (fixture_inv.dfgCons_termCtx_iff (ti := 1) rfl termData fixtureFrame).mpr fixture_dfg, rfl, rfl⟩

end Backend.Stock.Proof
