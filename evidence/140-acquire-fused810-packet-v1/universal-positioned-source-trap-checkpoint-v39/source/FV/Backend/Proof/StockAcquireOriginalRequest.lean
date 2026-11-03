import FV.Backend.Proof.StockAcquireOriginalPointer

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Complete helper execution derives the pointer request from actual original source data. -/
theorem sink_atomic_original_request {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {st next : State} {before after : Array RuleId}
    {fuel producer : Nat} {out : V} {info : IInfo} {original : Clif.Inst}
    (installed : ctx.insts[producer]? = some info) (source : info.clif = some original)
    (enough : 25 ≤ fuel)
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 27 564 [.inst producer]
      (st,before) out (next,after)) :
    ∃ ty flags pointer middle address,
      original = .atomicLoad ty flags pointer ∧ eTy ty = true ∧ flags.endianness ≠ some .big ∧
      Stock.externCtor ctx T.sink_inst [.inst producer] st = .ok (.op .unit,middle) ∧
      Stock.externCtor ctx T.put_in_reg [.value pointer] middle = .ok (.reg address,next) ∧
      DemandAllowed ctx middle pointer ∧ ctx.valueReg? pointer = some address ∧
      out = .reg address ∧ next = middle.mark pointer := by
  obtain ⟨actual,rest,found,shape⟩ := AcquireHelpers.sink_atomic_call_data (by omega) run
  have same : actual = info := Option.some.inj (found.symm.trans installed)
  subst actual
  obtain ⟨ty,flags,pointer,originalEq,integer,little⟩ :=
    AcquireHelpers.mapped_atomic_producer mapped installed source shape
  have atomicSource : info.clif = some (.atomicLoad ty flags pointer) :=
    source.trans (congrArg some originalEq)
  have fields := mapped_atomic_original_fields mapped installed atomicSource integer little shape
  obtain ⟨middle,address,sink,request,safe,register,output,marked⟩ :=
    sink_atomic_call_request installed fields enough run
  exact ⟨ty,flags,pointer,middle,address,originalEq,integer,little,sink,request,safe,register,output,marked⟩

end Backend.Stock.Proof.Acquire810
