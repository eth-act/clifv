import FV.Backend.Proof.StockIndirectCallRhs
import FV.Backend.Proof.StockFreshAlias
namespace Backend.Stock.Proof.IndirectCallEmissionDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open IndirectCallRhsDraft CallAbiStaticDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl

private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl

private theorem stock_internal_split_first {p : Program} {cfg : Config} {σ : Type} {sem : Isle.Sem V σ}
    (hc : cfg.checkOverlap = false) {ty : TypeId} {t : TermId} {vs : List V} {term : Term}
    {flags : TermFlags} {ex : Option Extractor} (ht : termOf p t = .ok term)
    (hk : term.kind = .decl flags (some .internal) ex) (hm : flags.isMulti = false)
    {n : Nat} (hn : 22 + (p.rulesOf t).length ≤ n) {s s' : σ × Array RuleId} {v : V}
    (h : ApplyInternal p sem cfg n ty t vs s v s') :
    ∃ pre r post, p.rulesOf t = pre ++ r :: post ∧
      (∀ r' ∈ pre, ∃ m' s1, (matchRule p sem cfg (m' + 20) r' vs).run s = .ok (none, s1)) ∧
      ∃ m' n' env s1 st tr,
      (matchRule p sem cfg (m' + 20) r vs).run s = .ok (some env, s1) ∧
      (evalExpr p sem cfg (n' + 20) r.rhs env).run s1 = .ok (some v, (st, tr)) ∧
      s' = (st, tr.push r.id) ∧ n = n' + 20 := by
  obtain ⟨r, pre, post, hL, hpre, m, env, s1, st, tr, hmn, hmt, he, rfl⟩ :=
    applyTerm_internal_some_first hc ht hk hm h
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 20 := ⟨m - 20, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 20 := ⟨n - 20, by omega⟩
  refine ⟨pre, r, post, hL, fun r' hr' => ?_, m', n', env, s1, st, tr, hmt, he, rfl, rfl⟩
  obtain ⟨k, hk, s2, h2⟩ := hpre r' hr'
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 20 := ⟨k - 20, by omega⟩
  exact ⟨k', s2, h2⟩

private theorem call_machine {p : Program} (hp : Data p) {ctx : Ctx} {n : Nat}
    (enough : 30 ≤ n) {info : V} {before after : State × Array RuleId} {machine : V}
    (run : ApplyInternal p (Stock.sem ctx) {} n 46 639 [info] before machine after) :
    after.1 = before.1 ∧ machine = .data 46 0 [.data 58 110 [info]] := by
  have hc : ({} : Config).checkOverlap = false := rfl
  rcases before with ⟨st,tr⟩
  rcases after with ⟨next,trace⟩
  obtain ⟨_,_,_,hL,hpre,_,_,_,_,_,_,hm,he,stateEq,fuelEq⟩ :=
    stock_internal_split_first hc hp.t639 term_639_kind rfl (by rw [hp.r639]; simp; omega) run
  rcases Prod.mk.inj stateEq with ⟨rfl,rfl⟩
  cases fuelEq
  rw [hp.r639] at hL
  isel_rule_cases hL
  cases hp
  isel_inv [*,rule_inst_4786,sem_mkData,sem_unData] at hm he

private theorem emit_call {p : Program} (hp : Data p) {ctx : Ctx} {n : Nat}
    (enough : 30 ≤ n) {call : CallInfo} {before after : State × Array RuleId} {unit : V}
    (run : ApplyInternal p (Stock.sem ctx) {} n 13 242
      [.data 46 0 [.data 58 110 [.op (.callInfo call)]]] before unit after) :
    after.1 = {before.1 with base := before.1.base.emit (.call call)} ∧ unit = .op .unit := by
  have hc : ({} : Config).checkOverlap = false := rfl
  have emitted (st : State) : Stock.externCtor ctx T.emit [.data 58 110 [.op (.callInfo call)]] st =
      .ok (.op .unit,{st with base := st.base.emit (.call call)}) := by
    rw [stock_ctor_baseOnly _ _ _ _ (by decide),ctor_emit _ _ (ofV_callInd call)]
  rcases before with ⟨st,tr⟩
  rcases after with ⟨next,trace⟩
  obtain ⟨_,_,_,hL,hpre,_,_,_,_,_,_,hm,he,stateEq,fuelEq⟩ :=
    stock_internal_split_first hc hp.t242 term_242_kind rfl (by rw [hp.r242]; simp; omega) run
  rcases Prod.mk.inj stateEq with ⟨rfl,rfl⟩
  cases fuelEq
  rw [hp.r242] at hL
  isel_rule_cases hL
  all_goals cases hp
  · isel_inv [*,rule_prelude_lower_522,sem_ctor,sem_mkData,sem_unData,emitted] at hm he
    isel_destruct
    rename_i actual
    rw [emitted] at actual
    cases actual
    exact ⟨rfl,rfl⟩
  · isel_inv [*,rule_prelude_lower_524,sem_mkData,sem_unData] at hm
  · isel_inv [*,rule_prelude_lower_527,sem_mkData,sem_unData] at hm

private theorem abi_identity {ctx : Ctx} {sig : Clif.Signature} {st next : State} {v : V}
    (run : Stock.externCtor ctx T.abi_sig [.op (.sig sig)] st = .ok (v,next)) :
    v = .op (.sig sig) ∧ next = st := by
  rw [stock_ctor_baseOnly _ _ _ _ (by decide)] at run
  change ExtResult.ok (.op (.sig sig),st) = .ok (v,next) at run
  cases run; exact ⟨rfl,rfl⟩
private theorem none_identity {ctx : Ctx} {st next : State} {v : V}
    (run : Stock.externCtor ctx T.try_call_none [] st = .ok (v,next)) :
    v = .op .tryCallNone ∧ next = st := by
  change ExtResult.ok (.op .tryCallNone,st) = .ok (v,next) at run
  cases run; exact ⟨rfl,rfl⟩
private theorem output_identity {ctx : Ctx} {rss : List (List Reg)} {st next : State} {v : V}
    (run : Stock.externCtor ctx T.output_vec [.regsVec rss] st = .ok (v,next)) :
    v = .regsVec rss ∧ next = st := by
  change ExtResult.ok (.regsVec rss,st) = .ok (v,next) at run
  cases run; exact ⟨rfl,rfl⟩
private theorem numbers : ∀ rs : List Reg,(∀ r ∈ rs,∃ n,r = .vreg n .int) →
    ∃ ns : List Nat,rs = ns.map (fun n => Reg.vreg n .int)
  | [],_ => ⟨[],rfl⟩
  | r :: rs,virtual => by
    obtain ⟨n,rfl⟩ := virtual r (List.mem_cons_self ..)
    obtain ⟨ns,rfl⟩ := numbers rs (fun r member => virtual r (List.mem_cons_of_mem _ member))
    exact ⟨n :: ns,rfl⟩
private theorem marked_base (xs : List Nat) (st : State) : (xs.foldl State.mark st).base = st.base := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => exact ih (st.mark x)

private theorem defs_fresh {target : Nat} {uses : List (Nat × Reg)} {base count : Nat}
    {ops : Array Operand}
    (operands : (MInst.call ⟨.reg (.vreg target .int),retPairs uses,callDefs (outDefs base count)⟩).operands = .ok ops) :
    ∀ o ∈ ops.toList,o.kind = .def → base ≤ o.vreg := by
  rw [operands_call_reg] at operands
  cases operands
  intro o member defined
  simp only [List.toList_toArray,List.mem_cons,List.mem_append] at member
  rcases member with rfl | use | definition
  · cases defined
  · simp only [retOps,List.mem_map] at use
    obtain ⟨q,present,rfl⟩ := use
    cases defined
  · simp only [callDefOps,List.mem_map] at definition
    obtain ⟨q,present,rfl⟩ := definition
    obtain ⟨j,below,rfl⟩ := mem_outDefs present
    simp only
    omega

/-- The actual selected indirect-call helper protocol emits the real call after
its exact stack stores and returns its exact fresh explicit result vector.
The emitted call has SpillInstOk and every definition is fresh at this RHS.
The ABI and mapped-source conditions are the existing original conditions. -/
theorem stock_indirect_call_protocol_emission {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {args : List Nat} {sig : Clif.Signature} (abi : sigAbiOk sig = true) {callee : Nat}
    {before next : State} {tr trace : Array RuleId} {out : V}
    (calls : IndirectRootCalls p ctx callee args sig before next tr trace out) :
    ∃ (target : Nat) (ns : List Nat) (locs : List ArgLoc) (bytes : List Nat) (stack : Nat) (call : CallInfo),
      ctx.valueReg? callee = some (.vreg target .int) ∧
      args.mapM ctx.valueReg? = some (ns.map fun n => Reg.vreg n .int) ∧
      sigParamBytes sig = .ok bytes ∧ sigArgLocs sig = .ok (locs,stack) ∧
      call = ⟨.reg (.vreg target .int),retPairs (regPairsOf ((locs.zip ns).zip bytes)),
        callDefs (outDefs before.base.nextVreg sig.returns.length)⟩ ∧
      out = .regsVec (outRegs before.base sig.returns.length) ∧
      next.base.emitted = (before.base.emitted ++
        ((stackEnts ((locs.zip ns).zip bytes)).map argStore).toArray).push (.call call) ∧
      SpillInstOk (.call call) ∧
      ∀ ops,(MInst.call call).operands = .ok ops → ∀ o ∈ ops.toList,o.kind = .def → before.base.nextVreg ≤ o.vreg := by
  obtain ⟨outs,afterOut,abiValue,afterAbi,targetValue,afterTarget,requested,afterRequest,uses,afterArgs,defs,afterDefs,noTry,afterNone,
    info,afterInfo,machine,afterMachine,machineTrace,unit,afterEmit,emitTrace,callFuel,emitFuel,
    output,abiRun,targetRun,request,arguments,returns,noneRun,formed,callBound,emitBound,machineCall,emission,outputRun,traceEq⟩ := calls
  obtain ⟨rfl,rfl⟩ := abi_identity abiRun
  obtain ⟨safeTarget,r,targetMap,rfl,targetState⟩ := (stock_put_in_reg_iff _ _ _ _ _).mp targetRun
  obtain ⟨target,rfl⟩ := mapped.valueReg callee r targetMap
  obtain ⟨safe,rs,mapping,rfl,requestState⟩ := (stock_put_in_regs_vec_iff _ _ _ _ _).mp request
  have virtual : ∀ r ∈ rs,∃ n,r = .vreg n .int := by
    intro r member
    obtain ⟨x,present,lookup⟩ := Backend.Proof.Flow.mapM_mem mapping r member
    exact mapped.valueReg x r lookup
  obtain ⟨ns,rfl⟩ := numbers rs virtual
  obtain ⟨rfl,rfl⟩ := none_identity noneRun
  obtain ⟨locs,bytes,stack,call,byteRun,locations,useValue,defValue,infoValue,shape,valid,static,
    stores,pins,outgoing⟩ := stock_call_helpers_static abi true "" target output arguments returns formed
  rw [infoValue] at machineCall
  obtain ⟨machineState,machineValue⟩ := call_machine hp callBound machineCall
  rw [machineValue] at emission
  obtain ⟨emittedState,unitValue⟩ := emit_call hp emitBound emission
  dsimp only at machineState emittedState
  have outputShape := output
  rw [CallOutputStaticDraft.stock_gen_call_output_exact] at outputShape
  cases outputShape
  obtain ⟨outValue,lastState⟩ := output_identity outputRun
  refine ⟨target,ns,locs,bytes,stack,call,targetMap,mapping,byteRun,locations,shape,outValue,?_,static,?_⟩
  · rw [lastState,emittedState,machineState,outgoing,pins,stores,requestState,targetState]
    simp only [marked_base,State.mark,LState.emit,freshN_emitted]
  · rw [shape]
    intro ops operands
    exact defs_fresh operands
end Backend.Stock.Proof.IndirectCallEmissionDraft
