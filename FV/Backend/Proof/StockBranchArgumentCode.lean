import FV.Backend.Proof.StockEdgeValues

/-! Actual plain-jump argument collection and its final resolved register list.
The source map is derived from successful collection, not supplied as a certificate. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def argStep (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (acc : State × Array Reg) :
    Except String (ForInStep (State × Array Reg)) := do
  match arg with
  | .val v =>
    let some r := ctx.valueReg? v | throw s!"unknown value v{v}"
    pure (.yield (acc.1.mark v, acc.2.push r))
  | .ret i =>
    if index < nh then throw "try_call return on exception edge"
    let some r := rets[i]? | throw "try_call return index"
    pure (.yield (acc.1, acc.2.push r))
  | .exn i =>
    if index == nh then throw "try_call payload on normal edge"
    let some r := pays[i]? | throw "try_call payload index"
    pure (.yield (acc.1, acc.2.push r))


private theorem val_loop {ctx : Ctx} {rets pays : List Reg} {index nh : Nat} {xs : List Nat}
    {st next : State} {before after : Array Reg}
    (run : forIn (xs.map Clif.TryArg.val) (st,before) (argStep ctx rets pays index nh) = .ok (next,after)) :
    ∃ rs,xs.mapM ctx.valueReg? = some rs ∧ after = before ++ rs.toArray := by
  induction xs generalizing st before with
  | nil =>
    simp only [List.map_nil,List.forIn_nil,pure,Except.pure] at run
    cases run
    exact ⟨[],rfl,by simp⟩
  | cons x xs ih =>
    simp only [List.map_cons,List.forIn_cons,argStep] at run
    cases lookup : ctx.valueReg? x with
    | none => simp only [lookup,bind,Except.bind] at run; cases run
    | some r =>
      simp only [lookup,bind,Except.bind,pure,Except.pure] at run
      obtain ⟨rs,mapped,code⟩ := ih run
      refine ⟨r :: rs,?_,?_⟩
      · simp only [List.mapM_cons,lookup,mapped]
        rfl
      · rw [code]
        apply Array.toList_inj.mp
        simp [Array.toList_push,List.append_assoc]

private theorem jump_arguments {ctx : Ctx} {f : Clif.Function} (func : ctx.func = f)
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b)
    {bc : Clif.BlockCall} (term : b.term = .jump bc) {input next : State} {args : Array Reg}
    (run : branchArgs ctx input bi 0 = .ok (args,next)) :
    bc.args.mapM ctx.valueReg? = some args.toList := by
  have source : ctx.func.blocks[bi]! = b := by simp only [func,getElem!_def,block,Option.getD_some]
  unfold branchArgs at run
  rw [source] at run
  dsimp only at run
  rw [term] at run
  simp only [destinations,List.getElem?_cons_zero] at run
  split at run
  · rename_i target found
    split at run
    · cases run
    · let ti := (input.instBlock.findIdx? (· == bi)).getD 0 + b.body.length
      let reserved := input.tryRegs[ti]!
      change (do
        let result ← forIn (bc.args.map Clif.TryArg.val) (input,#[]) (argStep ctx reserved.1 reserved.2 0 0)
        pure (result.2,result.1)) = .ok (args,next) at run
      cases loop : forIn (bc.args.map Clif.TryArg.val) (input,#[]) (argStep ctx reserved.1 reserved.2 0 0) with
      | error e => simp only [loop,bind,Except.bind] at run; cases run
      | ok pair =>
        obtain ⟨state,registers⟩ := pair
        simp only [loop,bind,Except.bind,pure,Except.pure] at run
        cases run
        obtain ⟨rs,mapped,code⟩ := val_loop loop
        simpa only [code,Array.empty_append,List.toList_toArray] using mapped
  · cases run

private theorem mapped_numbers {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) :
    ∀ {xs : List Nat} {rs : List Reg},xs.mapM ctx.valueReg? = some rs →
      rs = xs.map (fun x => Reg.vreg (edgeValueNum ctx x) .int)
  | [],rs,mapping => by simp at mapping; subst rs; rfl
  | x :: xs,rs,mapping => by
    simp only [List.mapM_cons,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at mapping
    obtain ⟨r,lookup,tail,rest,rfl⟩ := mapping
    obtain ⟨n,rfl⟩ := inv.valueReg x r lookup
    rw [mapped_numbers inv rest]
    simp only [List.map_cons,edgeValueNum,lookup]

/-- Successful actual plain-jump argument collection yields exactly the
source argument registers after the real final alias resolver. Scope supplies
the mapped-register class facts; no register-map certificate is supplied. -/
theorem stock_branchArgs_jump_numbers {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b)
    {bc : Clif.BlockCall} (term : b.term = .jump bc) {input next : State} {args : Array Reg}
    (call : branchArgs result.ctx input bi 0 = .ok (args,next)) :
    args.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)) =
      ((edgeArgumentNumbers result bc).map (fun n => Reg.vreg n .int)).toArray := by
  have built : ∃ ranges,Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) := by
    unfold Stock.lower at run
    dsimp only at run
    repeat' first
      | (solve | cases run)
      | simp only [bind,Except.bind,pure,Except.pure] at run
      | split at run
    cases run
    exact ⟨_,by assumption⟩
  obtain ⟨ranges,build⟩ := built
  have inv := buildCtx_mappedInv scope build
  have mapping := mapped_numbers inv (jump_arguments inv.func block term call)
  apply Array.toList_inj.mp
  simp [mapping,edgeArgumentNumbers,List.map_map,Function.comp_def,resolve_vreg,aliasNum]
end Backend.Stock.Proof
