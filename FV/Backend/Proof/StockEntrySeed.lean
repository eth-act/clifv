import FV.Backend.Proof.StockSourceEntry
import FV.Backend.Proof.StockDFG
import FV.Backend.Proof.StockRecordContext
import FV.Backend.Proof.StockEntryAliases
import FV.Backend.Proof.StockSelectScanRefines
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

open Classical in
/-- Proof-selected initial virtual values. The allocation check is independent
of this choice; no extra input or runtime certificate is introduced. -/
noncomputable def entrySeed (ctx : Ctx) (fr : Clif.Frame) (key : Nat) : CV :=
  if h : ∃ pair : Nat × Clif.Val,
      ctx.valueReg? pair.1 = some (.vreg key .int) ∧ fr.regs pair.1 = some pair.2 then
    (Classical.choose h).2.bits.setWidth 128
  else 0

/-- Every defined mapped source value can be held initially, including values
whose argument copies are omitted as unused. -/
theorem entrySeed_values {ctx : Ctx} {fr : Clif.Frame}
    (injective : ValueMapInjective ctx)
    (mapped : ∀ x v, fr.regs x = some v → ∃ key, ctx.valueReg? x = some (.vreg key .int))
    (width : ∀ x v, fr.regs x = some v → v.ty.width ≤ 128) :
    ValuesHeld (fun _ => True) ctx fr (entrySeed ctx fr) := by
  classical
  intro x _ v found
  obtain ⟨key,map⟩ := mapped x v found
  refine ⟨key,map,?_⟩
  have existsValue : ∃ pair : Nat × Clif.Val,
      ctx.valueReg? pair.1 = some (.vreg key .int) ∧ fr.regs pair.1 = some pair.2 :=
    ⟨(x,v),map,found⟩
  unfold entrySeed
  rw [dite_eq_left existsValue]
  have facts := Classical.choose_spec existsValue
  have same : (Classical.choose existsValue).1 = x := injective _ _ key facts.1 map
  have value : (Classical.choose existsValue).2 = v := by
    rw [same] at facts
    exact Option.some.inj (facts.2.symm.trans found)
  rw [value]
  unfold VHolds
  rw [BitVec.setWidth_setWidth_of_le _ (width x v found),BitVec.setWidth_eq]

private theorem entered_param {b : Clif.Block} {regs : Clif.Regs}
    {args : List Clif.Val} {x : Nat} {v : Clif.Val}
    (set : Clif.Regs.empty.setMany (b.params.map (·.1)) args = some regs)
    (found : regs x = some v) : x ∈ b.params.map (·.1) := by
  by_cases member : x ∈ b.params.map (·.1)
  · exact member
  · rw [setMany_other set member] at found
    cases found

private theorem scalar_width (ty : Clif.Ty) (supported : CTy.ofClif ty ∈ eCTys) : ty.width ≤ 128 := by
  cases ty <;> simp [CTy.ofClif,eCTys,Clif.Ty.width] at supported ⊢

/-- Successful original source entry and Stock construction derive all mapping
and width premises of proof-selected initialization internally. -/
theorem stock_lower_entered_value_type_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {args : List Clif.Val} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) :
    ∀ x v, fr.regs x = some v → event.ctx.valueType? x = some (CTy.ofClif v.ty) := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,
    label,bi,data,core,build,ordered,initial,empty,parts,folded,
    final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,oldBuild,spec,view⟩ := buildCtx_source build
  have types : event.ctx.valTy = original.valTy := by
    rw [eventEq,(stock_lowerBlockCore_scanOrigin coreRun).2.1]
    exact view.valTy
  have entryFacts := entered
  obtain ⟨b,regs,entry,argTypes,paramTypes,set,frame⟩ := entryFacts
  have frameRegs : fr.regs = regs := congrArg (fun frame : Clif.Frame => frame.regs) frame
  have block : f.blocks[0]? = some b := by
    simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using entry
  have nd := (List.nodup_append.mp (block_nodup dominated.ssa block)).1
  have typed : ∀ x v, fr.regs x = some v → event.ctx.valueType? x = some (CTy.ofClif v.ty) := by
    intro x v found
    have lookup : regs x = some v := by simpa only [frameRegs] using found
    have member := entered_param set lookup
    obtain ⟨q,qmem,equal,valueTy⟩ := setMany_param_ty set nd paramTypes member lookup
    have originalTy := (spec.facts.types dominated.ssa).2 b (List.mem_of_getElem? block) q qmem
    rw [equal,← valueTy] at originalTy
    simpa only [Ctx.valueType?,types] using originalTy
  exact typed

/-- Executable-entry compatibility variant; retains the original statement. -/
theorem stock_lower_entered_value_type {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {args : List Clif.Val} {cm0 cm : Clif.Mem} {fr : Clif.Frame}
    (entered : Clif.enterFunc f args cm0 = .ok (fr,cm)) :
    ∀ x v, fr.regs x = some v → event.ctx.valueType? x = some (CTy.ofClif v.ty) := by
  exact stock_lower_entered_value_type_frame run dominated events (SourceEntry.of_enterFunc entered)

theorem entrySeed_entered_values_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {args : List Clif.Val} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) :
    ValuesHeld (fun _ => True) event.ctx fr (entrySeed event.ctx fr) := by
  have inv := (stock_lower_record_context run scope events).1
  have typed := stock_lower_entered_value_type_frame run dominated events entered
  apply entrySeed_values inv.injective
  · intro x v found
    exact inv.typedReg x _ (typed x v found)
  · intro x v found
    exact scalar_width v.ty (inv.valTyE x _ (typed x v found))

/-- Executable-entry compatibility variant; retains the original statement. -/
theorem entrySeed_entered_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {args : List Clif.Val} {cm0 cm : Clif.Mem} {fr : Clif.Frame}
    (entered : Clif.enterFunc f args cm0 = .ok (fr,cm)) :
    ValuesHeld (fun _ => True) event.ctx fr (entrySeed event.ctx fr) := by
  exact entrySeed_entered_values_frame run scope dominated events (SourceEntry.of_enterFunc entered)

/-- Original parameters are fixed by final alias resolution, so initialization
also establishes the actual whole-driver resolved source relation. -/
theorem entrySeed_entered_resolved_values_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {args : List Clif.Val} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) :
    ValuesHeld (fun _ => True) event.ctx fr
      (fun key => entrySeed event.ctx fr (aliasNum result.final.alias key)) := by
  have held := entrySeed_entered_values_frame run scope dominated events entered
  have entryFacts := entered
  obtain ⟨b,regs,entry,argTypes,paramTypes,set,frame⟩ := entryFacts
  have frameRegs : fr.regs = regs := congrArg (fun frame : Clif.Frame => frame.regs) frame
  have block : f.blocks[0]? = some b := by
    simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using entry
  intro x _ v found
  obtain ⟨key,mapped,value⟩ := held x trivial v found
  have lookup : regs x = some v := by simpa only [frameRegs] using found
  have parameter := entered_param set lookup
  have resultMap : result.ctx.valueReg? x = some (.vreg key .int) := by
    rw [← (stock_lower_record_context run scope events).2.1 x]
    exact mapped
  have fixed := stock_lower_parameter_resolves run dominated.ssa block parameter resultMap
  refine ⟨key,mapped,?_⟩
  dsimp only
  rw [fixed]
  exact value

/-- Executable-entry compatibility variant; retains the original statement. -/
theorem entrySeed_entered_resolved_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {args : List Clif.Val} {cm0 cm : Clif.Mem} {fr : Clif.Frame}
    (entered : Clif.enterFunc f args cm0 = .ok (fr,cm)) :
    ValuesHeld (fun _ => True) event.ctx fr
      (fun key => entrySeed event.ctx fr (aliasNum result.final.alias key)) := by
  exact entrySeed_entered_resolved_values_frame run scope dominated events (SourceEntry.of_enterFunc entered)

/-- Actual source entry is typed in the actual Stock scan context. -/
theorem stock_lower_entered_frame_typed_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {args : List Clif.Val} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) : FrameTyped event.ctx fr := by
  intro x ty v type found
  have expected := stock_lower_entered_value_type_frame run dominated events entered x v found
  exact Option.some.inj (expected.symm.trans type)

/-- Executable-entry compatibility variant; retains the original statement. -/
theorem stock_lower_entered_frame_typed {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {args : List Clif.Val} {cm0 cm : Clif.Mem} {fr : Clif.Frame}
    (entered : Clif.enterFunc f args cm0 = .ok (fr,cm)) : FrameTyped event.ctx fr := by
  exact stock_lower_entered_frame_typed_frame run dominated events (SourceEntry.of_enterFunc entered)

/-- Original entry values are parameters and have no source instruction definition. -/
theorem stock_lower_entered_definition_none_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {args : List Clif.Val} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) :
    ∀ x v, fr.regs x = some v → event.ctx.defInst? x = none := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,
    label,bi,data,core,build,ordered,initial,empty,parts,folded,
    final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,oldBuild,spec,view⟩ := buildCtx_source build
  have defs : event.ctx.valDef = original.valDef := by
    rw [eventEq,(stock_lowerBlockCore_scanOrigin coreRun).2.1]
    exact view.valDef
  have entryFacts := entered
  obtain ⟨b,regs,entry,argTypes,paramTypes,set,frame⟩ := entryFacts
  have frameRegs : fr.regs = regs := congrArg (fun frame : Clif.Frame => frame.regs) frame
  have block : f.blocks[0]? = some b := by
    simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using entry
  intro x v found
  have lookup : regs x = some v := by simpa only [frameRegs] using found
  have parameter := entered_param set lookup
  have originalNone := defInst_par spec.facts dominated.ssa block parameter
  simpa only [Ctx.defInst?,defs] using originalNone

/-- Executable-entry compatibility variant; retains the original statement. -/
theorem stock_lower_entered_definition_none {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {args : List Clif.Val} {cm0 cm : Clif.Mem} {fr : Clif.Frame}
    (entered : Clif.enterFunc f args cm0 = .ok (fr,cm)) :
    ∀ x v, fr.regs x = some v → event.ctx.defInst? x = none := by
  exact stock_lower_entered_definition_none_frame run dominated events (SourceEntry.of_enterFunc entered)

/-- The source entry frame satisfies restricted DFG consistency for any
availability set, without an external consistency certificate. -/
theorem stock_lower_entered_restrict_dfg_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {args : List Clif.Val} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) (available : List Nat) :
    DFGCons event.ctx (restrict fr available) := by
  have defined := stock_lower_entered_definition_none_frame run dominated events entered
  have typed := stock_lower_entered_frame_typed_frame run dominated events entered
  have original : ∀ x v, (restrict fr available).regs x = some v → fr.regs x = some v := by
    intro x v found
    have member := restrict_regs_isSome (by rw [found]; rfl)
    rw [restrict_regs_of_mem member] at found
    exact found
  refine ⟨?_,?_⟩
  · intro x d info inst v definition source clif pure found
    have absent := defined x v (original x v found)
    rw [absent] at definition
    cases definition
  · intro x ty v type found
    exact typed x ty v type (original x v found)

/-- Executable-entry compatibility variant; retains the original statement. -/
theorem stock_lower_entered_restrict_dfg {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {args : List Clif.Val} {cm0 cm : Clif.Mem} {fr : Clif.Frame}
    (entered : Clif.enterFunc f args cm0 = .ok (fr,cm)) (available : List Nat) :
    DFGCons event.ctx (restrict fr available) := by
  exact stock_lower_entered_restrict_dfg_frame run dominated events (SourceEntry.of_enterFunc entered) available

/-- Original entry establishes the complete guarded source relation in the
proof-selected initial virtual file, independently of demand and unused parameters. -/
theorem stock_lower_entered_seed_guarded_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    (st : State) {MR : MemRelT} (w : Arm.ArmState) (memory : MR fr.slots cm w) :
    GuardedScanRel f result event.ctx event.block MR st (0,fr,cm) (entrySeed event.ctx fr) w := by
  have entryFacts := entered
  obtain ⟨b,regs,entry,argTypes,paramTypes,set,frame⟩ := entryFacts
  refine ⟨congrArg (fun frame : Clif.Frame => frame.func) frame,
    stock_lower_entered_restrict_dfg_frame run dominated events entered _,memory,?_⟩
  have values := entrySeed_entered_resolved_values_frame run scope dominated events entered
  intro x needed
  exact values x trivial

/-- Executable-entry compatibility variant; retains the original statement. -/
theorem stock_lower_entered_seed_guarded {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {args : List Clif.Val} {cm0 cm : Clif.Mem} {fr : Clif.Frame}
    (entered : Clif.enterFunc f args cm0 = .ok (fr,cm))
    (st : State) {MR : MemRelT} (w : Arm.ArmState) (memory : MR fr.slots cm w) :
    GuardedScanRel f result event.ctx event.block MR st (0,fr,cm) (entrySeed event.ctx fr) w := by
  exact stock_lower_entered_seed_guarded_frame run scope dominated events (SourceEntry.of_enterFunc entered) st w memory

end Backend.Stock.Proof
