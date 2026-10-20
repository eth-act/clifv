import FV.Backend.Proof.StockCallRootMatch
namespace Backend.Stock.Proof.IndirectCallRhsDraft
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open CallRootSelectionDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl

def indirectEnv (callee : Nat) (args : List Nat) (sig : Clif.Signature) : Isle.Interp.Env V :=
  #[some (.value callee),some (.values args),some (.op (.sig sig)),none,none,none,none,none,none,none]

/-- Real indirect-call matching derives its complete canonical environment,
scheduling state and trace from actual original source data. -/
theorem stock_indirect_call_root_match {p : Program} (hp : Data p) (hpI : IndData p) (ctx : Ctx)
    {ti callee : Nat} {info : IInfo} {args : List Nat} {sig : Clif.Signature}
    (slot : ctx.insts[ti]? = some info)
    (data : info.data = .data 152 7 [.data 151 9 [],.values (callee :: args),.op (.sig sig)])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+1000) rule_lower_2529 [.inst ti]).run (st,tr) =
      .ok (some (indirectEnv callee args sig),st,tr) := by
  have source := ext_inst_data_value ctx st.base slot
  rw [data] at source
  have sliced : Backend.externExtract ctx T.value_list_slice (.values (callee :: args)) st.base =
      .ok [.values (callee :: args)] := rfl
  have unwrapped : Backend.externExtract ctx T.value_slice_unwrap (.values (callee :: args)) st.base =
      .ok [.value callee,.values args] := rfl
  obtain ⟨t196,t2293,t2454⟩ := hpI
  cases hp
  isel_eval [*,rule_lower_2529,indirectEnv,sem_extract,sem_unData]
  isel_eval [*,rule_lower_2529,indirectEnv,sem_extract,sem_unData]
  rfl

def IndirectRootCalls (p : Program) (ctx : Ctx) (callee : Nat) (args : List Nat)
    (sig : Clif.Signature) (before next : State) (tr trace : Array RuleId) (out : V) : Prop :=
  ∃ outs afterOut abi afterAbi target afterTarget requested afterRequest uses afterArgs defs afterDefs noTry afterNone
      info afterInfo machine afterMachine machineTrace unit afterEmit emitTrace callFuel emitFuel,
    Stock.externCtor ctx T.gen_call_output [.op (.sig sig)] before = .ok (outs,afterOut) ∧
    Stock.externCtor ctx T.abi_sig [.op (.sig sig)] afterOut = .ok (abi,afterAbi) ∧
    Stock.externCtor ctx T.put_in_reg [.value callee] afterAbi = .ok (target,afterTarget) ∧
    Stock.externCtor ctx T.put_in_regs_vec [.values args] afterTarget = .ok (requested,afterRequest) ∧
    Stock.externCtor ctx T.gen_call_args [abi,requested] afterRequest = .ok (uses,afterArgs) ∧
    Stock.externCtor ctx T.gen_call_rets [abi,outs] afterArgs = .ok (defs,afterDefs) ∧
    Stock.externCtor ctx T.try_call_none [] afterDefs = .ok (noTry,afterNone) ∧
    Stock.externCtor ctx T.gen_call_ind_info [abi,target,uses,defs,noTry] afterNone = .ok (info,afterInfo) ∧
    30 ≤ callFuel ∧ 30 ≤ emitFuel ∧
    ApplyInternal p (Stock.sem ctx) {} callFuel 46 639 [info] (afterInfo,tr) machine (afterMachine,machineTrace) ∧
    ApplyInternal p (Stock.sem ctx) {} emitFuel 13 242 [machine] (afterMachine,machineTrace) unit (afterEmit,emitTrace) ∧
    Stock.externCtor ctx T.output_vec [outs] afterEmit = .ok (out,next) ∧ trace = emitTrace

/-- Every helper in the actual indirect RHS, including its real guarded
callee request, is retained at its actual Stock state and execution trace. -/
theorem stock_indirect_call_rhs_calls {p : Program} (hp : Data p) (ctx : Ctx)
    (callee : Nat) (args : List Nat) (sig : Clif.Signature)
    {before next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} 999999 rule_lower_2529.rhs (indirectEnv callee args sig)).run
      (before,tr) = .ok (some out,next,trace)) : IndirectRootCalls p ctx callee args sig before next tr trace out := by
  have hc : ({} : Config).checkOverlap = false := rfl
  cases hp
  isel_inv [*,rule_lower_2529,indirectEnv,sem_ctor] at run
  isel_destruct
  simp [Array.getElem?_setIfInBounds,Array.size_setIfInBounds] at *
  isel_destruct
  subst_vars
  unfold IndirectRootCalls
  refine ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,(by assumption),(by assumption),(by assumption),(by assumption),(by assumption),(by assumption),(by assumption),(by assumption),?_,?_,(by assumption),(by assumption),(by assumption),rfl⟩
  all_goals omega

/-- Actual source matching and first-match selection derive the indirect rule
and every real RHS helper; no caller-selected rule or replay is accepted. -/
theorem stock_selected_indirect_call_rhs_calls {ctx : Ctx} {ti callee : Nat}
    {info : IInfo} {args : List Nat} {sig : Clif.Signature}
    (slot : ctx.insts[ti]? = some info)
    (data : info.data = .data 152 7 [.data 151 9 [],.values (callee :: args),.op (.sig sig)])
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx ti st out next rules) :
    selected.rule = rule_lower_2529 ∧ selected.env = indirectEnv callee args sig ∧
      selected.matched = st ∧ selected.matchTrace = #[] ∧
      IndirectRootCalls program ctx callee args sig st next #[] selected.rhsTrace out := by
  have chosen := stock_selected_call_indirect_rule slot data selected
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨n,equal⟩ : ∃ n,selected.matchFuel=n+1000 := ⟨selected.matchFuel-1000,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,equal,stock_indirect_call_root_match data_program indData_program ctx slot data st #[] n] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨environment,state,trace⟩ := matched
  refine ⟨chosen,environment.symm,state.symm,trace.symm,?_⟩
  have rhs := selected.rhsRun
  rw [chosen,← environment,← state,← trace] at rhs
  exact stock_indirect_call_rhs_calls data_program ctx callee args sig rhs
end Backend.Stock.Proof.IndirectCallRhsDraft
