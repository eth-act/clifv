import FV.Backend.Proof.StockCallRootMatch
namespace Backend.Stock.Proof.GotCallRhsDraft
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
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_bool (ctx : Ctx) (b : Bool) : (Stock.sem ctx).bool b = .bool b := rfl

private theorem sem_zero (ctx : Ctx) : (Stock.sem ctx).int 10 0 = .int 0 := by
  unfold Stock.sem Backend.sem normInt Isle.Aarch64.program
  rfl

def gotEnv (args : List Nat) (sig : Clif.Signature) (name : String) : Isle.Interp.Env V :=
  #[some (.values args),some (.op (.sig sig)),some (.op (.extName name)),some (.data 38 1 []),
    none,none,none,none,none,none,none]

/-- Actual non-colocated source data supplies the full GOT-call match and
preserves the complete Stock scheduling state and trace. -/
theorem stock_got_call_root_match {p : Program} (hp : Data p) (ctx : Ctx)
    {ti fn : Nat} {info : IInfo} {args : List Nat} {ext : Clif.ExtFunc}
    (slot : ctx.insts[ti]? = some info)
    (data : info.data = .data 152 6 [.data 151 8 [],.values args,.op (.funcRef fn)])
    (external : ctx.func.extern? fn = some ext) (far : ext.colocated = false)
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+1000) rule_lower_2518 [.inst ti]).run (st,tr) =
      .ok (some (gotEnv args ext.sig ext.name),st,tr) := by
  have source := ext_inst_data_value ctx st.base slot
  rw [data] at source
  have extracted : Backend.externExtract ctx T.func_ref_data (.op (.funcRef fn)) st.base =
      .ok [.op (.sig ext.sig),.op (.extName ext.name),.data 38 1 [],.bool false] := by
    apply (ext_func_ref_data_iff st.base fn _).mpr
    exact ⟨ext,external,by rw [far]; rfl⟩
  have sliced : Backend.externExtract ctx T.value_list_slice (.values args) st.base = .ok [.values args] := rfl
  cases hp
  isel_eval [*,rule_lower_2518,gotEnv,sem_extract,sem_unData,sem_eq,sem_bool]
  isel_eval [*,rule_lower_2518,gotEnv,sem_extract,sem_unData,sem_eq,sem_bool]
  rfl

private theorem direct_no_match {p : Program} (hp : Data p) (ctx : Ctx)
    {ti fn : Nat} {info : IInfo} {args : List Nat} {ext : Clif.ExtFunc}
    (slot : ctx.insts[ti]? = some info)
    (data : info.data = .data 152 6 [.data 151 8 [],.values args,.op (.funcRef fn)])
    (external : ctx.func.extern? fn = some ext) (far : ext.colocated = false)
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+1000) rule_lower_2508 [.inst ti]).run (st,tr) = .ok (none,st,tr) := by
  have source := ext_inst_data_value ctx st.base slot
  rw [data] at source
  have extracted : Backend.externExtract ctx T.func_ref_data (.op (.funcRef fn)) st.base =
      .ok [.op (.sig ext.sig),.op (.extName ext.name),.data 38 1 [],.bool false] := by
    apply (ext_func_ref_data_iff st.base fn _).mpr
    exact ⟨ext,external,by rw [far]; rfl⟩
  have sliced : Backend.externExtract ctx T.value_list_slice (.values args) st.base = .ok [.values args] := rfl
  cases hp
  isel_eval [*,rule_lower_2508,sem_extract,sem_unData,sem_eq,sem_bool]
  isel_eval [*,rule_lower_2508,sem_extract,sem_unData,sem_eq,sem_bool]
  all_goals rfl

def GotRootCalls (p : Program) (ctx : Ctx) (args : List Nat) (sig : Clif.Signature)
    (name : String) (before next : State) (tr trace : Array RuleId) (out : V) : Prop :=
  ∃ outs afterOut abi afterAbi requested afterRequest uses afterArgs defs afterDefs boxed afterBox
      target afterTarget targetTrace noTry afterNone info afterInfo machine afterMachine machineTrace
      unit afterEmit emitTrace loadFuel callFuel emitFuel,
    Stock.externCtor ctx T.gen_call_output [.op (.sig sig)] before = .ok (outs,afterOut) ∧
    Stock.externCtor ctx T.abi_sig [.op (.sig sig)] afterOut = .ok (abi,afterAbi) ∧
    Stock.externCtor ctx T.put_in_regs_vec [.values args] afterAbi = .ok (requested,afterRequest) ∧
    Stock.externCtor ctx T.gen_call_args [abi,requested] afterRequest = .ok (uses,afterArgs) ∧
    Stock.externCtor ctx T.gen_call_rets [abi,outs] afterArgs = .ok (defs,afterDefs) ∧
    Stock.externCtor ctx T.box_external_name [.op (.extName name)] afterDefs = .ok (boxed,afterBox) ∧
    40 ≤ loadFuel ∧
    ApplyInternal p (Stock.sem ctx) {} loadFuel 27 570 [boxed,.int 0,.data 38 1 []]
      (afterBox,tr) target (afterTarget,targetTrace) ∧
    Stock.externCtor ctx T.try_call_none [] afterTarget = .ok (noTry,afterNone) ∧
    Stock.externCtor ctx T.gen_call_ind_info [abi,target,uses,defs,noTry] afterNone = .ok (info,afterInfo) ∧
    30 ≤ callFuel ∧ 30 ≤ emitFuel ∧
    ApplyInternal p (Stock.sem ctx) {} callFuel 46 639 [info] (afterInfo,targetTrace) machine (afterMachine,machineTrace) ∧
    ApplyInternal p (Stock.sem ctx) {} emitFuel 13 242 [machine] (afterMachine,machineTrace) unit (afterEmit,emitTrace) ∧
    Stock.externCtor ctx T.output_vec [outs] afterEmit = .ok (out,next) ∧ trace = emitTrace

/-- The actual GOT-call RHS exposes its real target load, ABI helpers, call
construction and emitter at their exact Stock states and traces. -/
theorem stock_got_call_rhs_calls {p : Program} (hp : Data p) (ctx : Ctx)
    (args : List Nat) (sig : Clif.Signature) (name : String)
    {before next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} 999999 rule_lower_2518.rhs (gotEnv args sig name)).run
      (before,tr) = .ok (some out,next,trace)) : GotRootCalls p ctx args sig name before next tr trace out := by
  have hc : ({} : Config).checkOverlap = false := rfl
  cases hp
  isel_inv [*,rule_lower_2518,gotEnv,sem_ctor] at run
  isel_destruct
  simp [Array.getElem?_setIfInBounds,Array.size_setIfInBounds] at *
  isel_destruct
  subst_vars
  simp only [sem_zero] at *
  unfold GotRootCalls
  refine ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,
    (by assumption),(by assumption),(by assumption),(by assumption),(by assumption),(by assumption),?_,
    (by assumption),(by assumption),(by assumption),?_,?_,(by assumption),(by assumption),(by assumption),rfl⟩
  all_goals omega

/-- Real successful source matching derives the GOT rule and its actual RHS;
the non-colocated condition excludes the earlier direct-call matcher. -/
theorem stock_selected_got_call_rhs_calls {ctx : Ctx} {ti fn : Nat}
    {info : IInfo} {args : List Nat} {ext : Clif.ExtFunc}
    (slot : ctx.insts[ti]? = some info)
    (data : info.data = .data 152 6 [.data 151 8 [],.values args,.op (.funcRef fn)])
    (external : ctx.func.extern? fn = some ext) (far : ext.colocated = false)
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx ti st out next rules) :
    selected.rule = rule_lower_2518 ∧ selected.env = gotEnv args ext.sig ext.name ∧
      selected.matched = st ∧ selected.matchTrace = #[] ∧
      GotRootCalls program ctx args ext.sig ext.name st next #[] selected.rhsTrace out := by
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨n,equal⟩ : ∃ n,selected.matchFuel=n+1000 := ⟨selected.matchFuel-1000,by omega⟩
  have chosen : selected.rule = rule_lower_2518 := by
    rcases stock_selected_call_rule slot data selected with direct | got
    · have matched := selected.matchedRun
      rw [direct,equal,direct_no_match data_program ctx slot data external far st #[] n] at matched
      cases matched
    · exact got
  have matched := selected.matchedRun
  rw [chosen,equal,stock_got_call_root_match data_program ctx slot data external far st #[] n] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨environment,state,trace⟩ := matched
  refine ⟨chosen,environment.symm,state.symm,trace.symm,?_⟩
  have rhs := selected.rhsRun
  rw [chosen,← environment,← state,← trace] at rhs
  exact stock_got_call_rhs_calls data_program ctx args ext.sig ext.name rhs
end Backend.Stock.Proof.GotCallRhsDraft
