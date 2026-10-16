import FV.Backend.Proof.StockGotLoad
import FV.Backend.Proof.StockFreshAlias
namespace Backend.Stock.Proof.GotCallEmissionDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open GotCallRhsDraft CallAbiStaticDraft GotLoadDraft
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

private theorem box_identity {ctx : Ctx} {name : String} {st next : State} {v : V}
    (run : Stock.externCtor ctx T.box_external_name [.op (.extName name)] st = .ok (v,next)) :
    v = .op (.extName name) ∧ next = st := by
  change ExtResult.ok (.op (.extName name),st) = .ok (v,next) at run
  cases run; exact ⟨rfl,rfl⟩

/-- The real selected GOT-call protocol emits its exact stack stores, fresh
GOT target load and call, and returns exact fresh explicit result vectors.
Both actual emitted instructions satisfy the existing complete control shapes. -/
theorem stock_got_call_protocol_emission {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {args : List Nat} {sig : Clif.Signature} (abi : sigAbiOk sig = true) {name : String}
    {before next : State} {tr trace : Array RuleId} {out : V}
    (calls : GotRootCalls p ctx args sig name before next tr trace out) :
    ∃ (ns : List Nat) (locs : List ArgLoc) (bytes : List Nat) (stack target : Nat) (call : CallInfo),
      args.mapM ctx.valueReg? = some (ns.map fun n => Reg.vreg n .int) ∧
      sigParamBytes sig = .ok bytes ∧ sigArgLocs sig = .ok (locs,stack) ∧
      target = before.base.nextVreg + sig.returns.length ∧
      call = ⟨.reg (.vreg target .int),retPairs (regPairsOf ((locs.zip ns).zip bytes)),
        callDefs (outDefs before.base.nextVreg sig.returns.length)⟩ ∧
      out = .regsVec (outRegs before.base sig.returns.length) ∧
      next.base.emitted = ((before.base.emitted ++
        ((stackEnts ((locs.zip ns).zip bytes)).map argStore).toArray).push
          (.loadExtNameGot (.vreg target .int) name)).push (.call call) ∧
      CtlShape before.base.nextVreg (.loadExtNameGot (.vreg target .int) name) ∧
      CtlShape before.base.nextVreg (.call call) := by
  obtain ⟨outs,afterOut,abiValue,afterAbi,requested,afterRequest,uses,afterArgs,defs,afterDefs,boxed,afterBox,
    targetValue,afterTarget,targetTrace,noTry,afterNone,info,afterInfo,machine,afterMachine,machineTrace,
    unit,afterEmit,emitTrace,loadFuel,callFuel,emitFuel,output,abiRun,request,arguments,returns,boxedRun,
    loadBound,loadRun,noneRun,formed,callBound,emitBound,machineCall,emission,outputRun,traceEq⟩ := calls
  obtain ⟨rfl,rfl⟩ := abi_identity abiRun
  obtain ⟨safe,rs,mapping,rfl,requestState⟩ := (stock_put_in_regs_vec_iff _ _ _ _ _).mp request
  have virtual : ∀ r ∈ rs,∃ n,r = .vreg n .int := by
    intro r member
    obtain ⟨x,present,lookup⟩ := Backend.Proof.Flow.mapM_mem mapping r member
    exact mapped.valueReg x r lookup
  obtain ⟨ns,rfl⟩ := numbers rs virtual
  obtain ⟨rfl,rfl⟩ := box_identity boxedRun
  obtain ⟨targetValueEq,targetState⟩ := stock_load_ext_name_got hp loadBound loadRun
  let target := afterBox.base.nextVreg
  change targetValue = .reg (.vreg target .int) at targetValueEq
  rw [targetValueEq] at formed
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
  have targetEq : target = before.base.nextVreg + sig.returns.length := by
    dsimp only [target]
    rw [pins,stores,requestState,marked_base,freshN_nextVreg]
  refine ⟨ns,locs,bytes,stack,target,call,mapping,byteRun,locations,targetEq,shape,outValue,?_,?_,?_⟩
  · dsimp only [target]
    rw [lastState,emittedState,machineState,outgoing,targetState,pins,stores,requestState]
    simp only [marked_base,LState.emit,LState.fresh,freshN_emitted]
  · exact .got target name (by omega)
  · rw [shape]
    exact .callReg target _ _ valid
end Backend.Stock.Proof.GotCallEmissionDraft
