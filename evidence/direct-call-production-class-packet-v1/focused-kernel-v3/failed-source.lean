import FV.E2E.StockResultCallSource
import FV.Backend.Proof.StockSourceEntry

namespace Backend.Stock.ResultCall
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Proof-internal facts come from the original source and actual retained artifacts. -/
structure Layout (f : Clif.Function) (result : Stock.Result) where
  data : SourceData
  source : sourceB f data = true
  finalCode : codeB data result = true
  records : result.blockScans.toList.all (scanB data result) = true
  reads : codeCheck f.sig result.code = true

theorem Layout.source_fields {f : Clif.Function} {result : Stock.Result} (layout : Layout f result) :
    f.blocks = [layout.data.block] ∧
    layout.data.block.body = [⟨[layout.data.result],.call layout.data.fn layout.data.args⟩] ∧
    layout.data.block.term = .ret [layout.data.result] ∧
    f.sig.returns = [layout.data.returned] ∧ layout.data.ext.sig.returns = [layout.data.returned] ∧
    layout.data.returned.ty = .i64 ∧ f.extern? layout.data.fn = some layout.data.ext ∧
    sigParamBytes layout.data.ext.sig = .ok layout.data.bytes ∧ layout.data.bytes.length ≤ 8 ∧
    returnPins f 1 = some [.x 0] := by
  simpa only [sourceB,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using layout.source

/-- Actual scan records retain both source mapping and fresh result definition. -/
theorem Layout.scan_fields {f : Clif.Function} {result : Stock.Result} (layout : Layout f result)
    {event : Stock.BlockScanEvent} (member : event ∈ result.blockScans.toList) (atEntry : event.block = 0) :
    ∃ (root destination : Nat) (pairs : List (Nat × Reg)),
      event.ctx.valueReg? layout.data.result = some (.vreg root .int) ∧
      event.output.code = #[.call ⟨.sym layout.data.ext.name,retPairs pairs,callDefs [(.x 0,destination)]⟩,
        .rets (retPairs [(root,.x 0)])] ∧
      aliasNum result.final.alias root = aliasNum result.final.alias destination ∧
      pairs.map (·.1) = layout.data.args.map (VoidCall.sourceKey event.ctx) := by
  have checked := List.all_eq_true.mp layout.records event member
  simp only [scanB,atEntry,beq_self_eq_true,↓reduceIte] at checked
  split at checked
  · rename_i root info returns mapped shape
    split at checked
    · rename_i destination defs
      simp only [Bool.and_eq_true,decide_eq_true_eq,and_assoc] at checked
      obtain ⟨dest,returnsEq,resolved,uses,keys⟩ := checked
      have aliases : aliasNum result.final.alias root = aliasNum result.final.alias destination := by
        simpa only [resolve_vreg,aliasNum,Reg.vreg.injEq,and_true] using resolved
      have same : info = ⟨.sym layout.data.ext.name,retPairs (VoidCall.callUses info.uses),
          callDefs [(.x 0,destination)]⟩ := by
        cases info
        simp only [CallInfo.mk.injEq]
        exact ⟨dest,uses,defs⟩
      refine ⟨root,destination,VoidCall.callUses info.uses,mapped,?_,aliases,keys⟩
      apply Array.toList_inj.mp
      rw [shape,returnsEq]
      exact congrArg (fun call : CallInfo => [MInst.call call,MInst.rets (retPairs [(root,.x 0)])]) same
    · cases checked
  · cases checked

/-- Finite source and artifact checks construct the internal layout without a caller certificate. -/
theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ∃ result,Stock.lower f = .ok result ∧ result.code = vc ∧ LowerScope f ∧ Dominated f ∧
      sigAbiOk f.sig = true ∧ Nonempty (Layout f result) ∧
      result.edgeArgs.all (fun row => row.all (·.isEmpty)) = true := by
  unfold check at checked
  cases data : sourceData? f with
  | none => simp only [data,Bool.false_eq_true] at checked
  | some source =>
    simp only [data] at checked
    cases lowered : Stock.lower f with
    | error message => simp only [lowered,Bool.and_false,Bool.false_eq_true] at checked
    | ok result =>
      simp only [lowered,Bool.and_eq_true,decide_eq_true_eq,and_assoc] at checked
      obtain ⟨sourceOk,scope,dominated,abi,equal,code,records,reads,edges⟩ := checked
      exact ⟨result,rfl,equal,lowerScope_of scope,dominated_of dominated,abi,
        ⟨⟨source,sourceOk,code,records,reads⟩⟩,edges⟩

/-- Original entry and execution derive the callback result; memory remains the actual callback memory. -/
theorem Layout.source_result {f : Clif.Function} {result : Stock.Result} (layout : Layout f result)
    {env : Clif.Env} {cp : Clif.Program} (subset : InSubset cp f)
    {args : List Clif.Val} {fr : Clif.Frame} {cm outMem : Clif.Mem}
    (entered : SourceEntry f args fr) {fuel : Nat} {values : List Clif.Val}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned values outMem) :
    ∃ (g : List Clif.Val → Clif.Mem → Clif.Outcome) (arguments : List Clif.Val)
      (after : Clif.Mem) (value : Clif.Val),
      env.extern layout.data.ext.name = some g ∧ fr.getMany layout.data.args = .ok arguments ∧
      arguments.map (·.ty) = Clif.AbiParam.tys layout.data.ext.sig.params ∧
      g arguments cm = .returned [value] after ∧ value.ty = .i64 ∧ values = [value] ∧
      outMem = (after.free (fr.slots.map (·.2))).leave := by
  obtain ⟨blocks,body,term,returns,calleeReturns,integer,lookup,sizes,registers,pins⟩ := layout.source_fields
  obtain ⟨b,regs,found,types,paramTypes,set,frame⟩ := entered
  have first : f.entry? = some layout.data.block := by
    simp only [Clif.Function.entry?,blocks,List.head?_cons]
  cases Option.some.inj (found.symm.trans first)
  have func : fr.func = f := congrArg Clif.Frame.func frame
  have body' : fr.body = [⟨[layout.data.result],.call layout.data.fn layout.data.args⟩] :=
    (congrArg Clif.Frame.body frame).trans body
  have term' : fr.term = .ret [layout.data.result] := (congrArg Clif.Frame.term frame).trans term
  have lookup' : fr.func.extern? layout.data.fn = some layout.data.ext := by rw [func]; exact lookup
  have external : cp.func? layout.data.ext.name = none :=
    subset.externCalls layout.data.block (by simp [blocks])
      ⟨[layout.data.result],.call layout.data.fn layout.data.args⟩ (by simp [body])
      layout.data.fn layout.data.args rfl layout.data.ext lookup
  obtain ⟨g,arguments,after,value,called,read,typed,run,valueType,equal,memory⟩ :=
    source_return_call body' term' (by rw [func]; exact returns) lookup' external calleeReturns returned
  exact ⟨g,arguments,after,value,called,read,typed,run,valueType.trans integer,equal,memory⟩

end Backend.Stock.ResultCall
