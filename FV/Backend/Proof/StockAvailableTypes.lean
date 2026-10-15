import FV.Backend.Proof.StockSelectParameterOriginalSourceValues
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Every declared original value has a type in the actual scan context;
source typing certificates need not be added to accepted programs. -/
theorem stock_lower_record_declared_type {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {x : Nat} (declared : x ∈ valueDefs f) : (event.ctx.valueType? x).isSome = true := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,oldState,oldBuild,spec,view⟩ := buildCtx_source build
  have typed := spec.regTy x
  rw [(spec.facts.vals x declared).2] at typed
  have actual : (result.ctx.valueType? x).isSome = true := by
    simpa only [Ctx.valueType?,view.valTy,Option.isSome_some] using typed.symm
  rw [eventEq,(stock_lowerBlockCore_scanOrigin coreRun).2.1]
  exact actual
/-- Original availability, a successful source getter and restricted DFG typing
derive the actual context type. This discharges recurring family type premises
internally while keeping earlier theorem interfaces available. -/
theorem stock_lower_available_getAs_type {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {bi j x : Nat} (available : x ∈ availOf f (availIn f result.ctx) bi j)
    {fr : Clif.Frame} (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    {ty : Clif.Ty} {bits : BitVec ty.width}
    (get : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok bits) :
    event.ctx.valueType? x = some (.int ty.width) := by
  have declared := avail_vals (fun tl value member => ((inFix_fixOk (f := f) (ctx := result.ctx) (gn := id)).cand tl value member).2.2.2.1) available
  obtain ⟨type,typed⟩ := Option.isSome_iff_exists.mp (stock_lower_record_declared_type run events declared)
  have same := getAs_typed dfg typed get
  simpa only [same,ofClif_int_width] using typed
end Backend.Stock.Proof