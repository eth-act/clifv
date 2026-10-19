import FV.Backend.Proof.StockCallResultBinding
namespace Backend.Stock.Proof.CallResultValuesDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open TupleBindingDraft TupleRecordBindingDraft CallResultBindingDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

/-- Explicit call definitions hold the source return prefix even when the ABI
also supplies an unused implicit return. This uses the existing callee relation. -/
theorem stock_resultsHeld_call_prefix {fr : Clif.Frame} {ρ : Nat → CV} {b : Nat} {rvals : List Clif.Val}
    {outs : List CV} (hro : PrefixHold rvals outs) :
    ResultsHeld b fr (outRegs' b rvals.length) rvals
      (writeV ρ ((callDefOps (outDefs b rvals.length)).zip outs)) := by
  refine ⟨by simp [outRegs'], fun j rs v hrs hvj => ?_⟩
  have hjN : j < rvals.length := by
    rcases Nat.lt_or_ge j rvals.length with h | h
    · exact h
    · simp [outRegs', h] at hrs
  simp only [outRegs', List.getElem?_map, List.getElem?_range hjN, Option.map_some,
    Option.some.injEq] at hrs
  subst hrs
  refine ⟨b + j, .int, rfl, .inl (by omega), ?_⟩
  obtain ⟨x, hx⟩ : ∃ x, outs[j]? = some x :=
    ⟨outs[j]'(by have := hro.1; omega), by simp⟩
  have hk : ((callDefOps (outDefs b rvals.length)).zip outs).map (·.1.vreg) =
      (List.range rvals.length).map (b + ·) := by
    rw [show (fun q : Operand × CV => q.1.vreg) = Operand.vreg ∘ Prod.fst from rfl, ← List.map_map,
      List.map_fst_zip (by simp only [callDefOps,outDefs,List.length_map,List.length_range]; exact hro.1)]
    simp [callDefOps, outDefs]
  have hnd : (((callDefOps (outDefs b rvals.length)).zip outs).map (·.1.vreg)).Nodup := by
    rw [hk]
    exact List.Pairwise.map _ (fun a c h e => h (by omega)) List.nodup_range
  have hget : ((callDefOps (outDefs b rvals.length)).zip outs)[j]? =
      some (⟨b + j, .int, .def, .late, .fixed (.x j)⟩, x) := by
    rw [List.getElem?_zip_eq_some]
    simp [callDefOps, outDefs, hx, hjN]
  rw [writeV_nodup_ctl _ ρ j _ x hnd hget]
  exact hro.2 j v x hvj hx

private theorem bound_values {ctx : Ctx} {aliases : Array (Option Nat)} {xs : List Nat} {base : Nat}
    (distinct : xs.Nodup)
    (bound : ∀ j x,xs[j]? = some x → ∃ key,ctx.valueReg? x = some (.vreg key .int) ∧
      (aliases[key]?).join = some (base+j) ∧ aliasNum aliases key = base+j)
    {fr fr' : Clif.Frame} {vals : List Clif.Val} {regs : Clif.Regs} {ρ : Nat → CV} {outs : List CV}
    (set : fr.regs.setMany xs vals = some regs) (updated : fr'.regs = regs) (held : PrefixHold vals outs) :
    ValuesHeld (fun x => x ∈ xs) ctx fr'
      (fun key => writeV ρ ((callDefOps (outDefs base xs.length)).zip outs) (aliasNum aliases key)) := by
  have length := setMany_length set
  have results := stock_resultsHeld_call_prefix (fr := fr) (ρ := ρ) (b := base) held
  intro x member v lookup
  obtain ⟨j,value,atValue,atResult,stored⟩ := setMany_mem set distinct x member
  rw [updated,stored] at lookup
  cases lookup
  obtain ⟨key,mapping,entry,resolved⟩ := bound j x atValue
  have below : j < vals.length := (List.getElem?_eq_some_iff.mp atResult).1
  have atReg : (outRegs' base vals.length)[j]? = some [Reg.vreg (base+j) .int] := by
    simp [outRegs',below]
  obtain ⟨out,cls,shape,_,valueHeld⟩ := results.2 j _ _ atReg atResult
  have same : out = base+j ∧ cls = .int := by simpa only [List.cons.injEq,Reg.vreg.injEq,and_true] using shape.symm
  rcases same with ⟨rfl,rfl⟩
  exact ⟨key,mapping,by dsimp only; rw [resolved,length]; exact valueHeld⟩

/-- Every source result of an actual direct or GOT call is held through its
final alias after successful source result binding. Source arity and result
mappings are derived internally; callee values use the original PrefixHold relation. -/
theorem stock_lower_call_result_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup) (abi : AbiSigsOk f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {fn : Nat} {args : List Nat} {ext : Clif.ExtFunc}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.call fn args))
    (external : f.extern? fn = some ext)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {fr fr' : Clif.Frame} {vals : List Clif.Val} {regs : Clif.Regs} {ρ : Nat → CV} {outs : List CV}
    (set : fr.regs.setMany info.results vals = some regs) (updated : fr'.regs = regs) (held : PrefixHold vals outs) :
    ValuesHeld (fun x => x ∈ info.results) result.ctx fr'
      (fun key => writeV ρ ((callDefOps (outDefs record.input.base.nextVreg info.results.length)).zip outs)
        (aliasNum result.final.alias key)) := by
  have bindings := (stock_lower_call_result_binding run scope ssa abi events records slot clif external recorded emitted).2.2
  have maps := (stock_lower_record_context run scope events).2.1
  apply bound_values (stock_lower_record_results_nodup run scope ssa events slot clif) ?_ set updated held
  intro j x atValue
  obtain ⟨key,mapping,entry,resolved⟩ := bindings j x atValue
  exact ⟨key,(maps x).symm.trans mapping,entry,resolved⟩

/-- Actual indirect-call results have the same final source-value transfer,
with their signature and all result aliases supplied by the real selected record. -/
theorem stock_lower_indirect_call_result_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup) (abi : AbiSigsOk f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {ref callee : Nat} {args : List Nat}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.callIndirect ref callee args))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {fr fr' : Clif.Frame} {vals : List Clif.Val} {regs : Clif.Regs} {ρ : Nat → CV} {outs : List CV}
    (set : fr.regs.setMany info.results vals = some regs) (updated : fr'.regs = regs) (held : PrefixHold vals outs) :
    ValuesHeld (fun x => x ∈ info.results) result.ctx fr'
      (fun key => writeV ρ ((callDefOps (outDefs record.input.base.nextVreg info.results.length)).zip outs)
        (aliasNum result.final.alias key)) := by
  obtain ⟨sig,declared,length,outputs,bindings⟩ := stock_lower_indirect_call_result_binding run scope ssa abi events records slot clif recorded emitted
  have maps := (stock_lower_record_context run scope events).2.1
  apply bound_values (stock_lower_record_results_nodup run scope ssa events slot clif) ?_ set updated held
  intro j x atValue
  obtain ⟨key,mapping,entry,resolved⟩ := bindings j x atValue
  exact ⟨key,(maps x).symm.trans mapping,entry,resolved⟩
end Backend.Stock.Proof.CallResultValuesDraft
