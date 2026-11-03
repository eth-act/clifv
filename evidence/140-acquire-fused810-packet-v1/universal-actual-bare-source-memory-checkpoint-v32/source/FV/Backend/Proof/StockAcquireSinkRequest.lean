import FV.Backend.Proof.StockAcquireSinkAddress

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
attribute [local irreducible] Isle.Aarch64.program

/-- The actual sink helper demands its original source pointer and derives the mapped register.
No caller safety receipt is required. -/
theorem sink_atomic_rhs_request {ctx : Ctx} {st next : State} {before after : Array RuleId}
    {bound : Isle.Interp.Env V} {producer pointer n : Nat} {out : V}
    (producerValue : bound[1]? = some (some (.inst producer)))
    (pointerValue : bound[0]? = some (some (.value pointer)))
    (run : (evalExpr program (Stock.sem ctx) {} (n+20) rule_inst_3905.rhs bound).run
      (st,before) = .ok (some out,next,after)) :
    ∃ middle address,
      Stock.externCtor ctx T.sink_inst [.inst producer] st = .ok (.op .unit,middle) ∧
      Stock.externCtor ctx T.put_in_reg [.value pointer] middle = .ok (.reg address,next) ∧
      DemandAllowed ctx middle pointer ∧ ctx.valueReg? pointer = some address ∧
      out = .reg address ∧ next = middle.mark pointer := by
  have ctor (term : Term) (args : List V) (state : State) :
      (Stock.sem ctx).ctor term args state = Stock.externCtor ctx term args state := rfl
  have overlap : ({} : Config).checkOverlap = false := rfl
  isel_inv [*,rule_inst_3905,ctor] at run
  simp only [data_program.t182,data_program.t236,T.put_in_reg,T.sink_inst,pure,Except.pure] at *
  isel_destruct
  subst_vars
  rename_i next middle sinkCall putCall
  simp only [pointerValue,Option.some.injEq] at *
  subst_vars
  have accepted := sink_accepted sinkCall
  have sinkUnit : Stock.externCtor ctx T.sink_inst [.inst producer] st = .ok (.op .unit,middle) := by
    simpa only [accepted.2.2.2.1,T.sink_inst] using sinkCall
  have request := (stock_put_in_reg_iff ctx middle pointer _ next).1 putCall
  obtain ⟨safe,address,mapped,output,marked⟩ := request
  refine ⟨middle,sinkUnit,address,?_,safe,mapped,output,marked⟩
  simpa only [output] using putCall

end Backend.Stock.Proof.Acquire810
