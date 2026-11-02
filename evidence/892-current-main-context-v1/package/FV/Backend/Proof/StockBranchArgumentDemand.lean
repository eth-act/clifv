import FV.Backend.Lowering.Stock
import FV.Backend.Proof.IselCtlCall

/-! Actual selected outgoing arguments mark every requested source value.
The complete post-state follows from executable argument collection. -/
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
    ∃ rs,xs.mapM ctx.valueReg? = some rs ∧ next = xs.foldl State.mark st ∧
      after = before ++ rs.toArray := by
  induction xs generalizing st before with
  | nil =>
    simp only [List.map_nil,List.forIn_nil,pure,Except.pure] at run
    cases run
    exact ⟨[],rfl,rfl,by simp⟩
  | cons x xs ih =>
    simp only [List.map_cons,List.forIn_cons,argStep] at run
    cases lookup : ctx.valueReg? x with
    | none => simp only [lookup,bind,Except.bind] at run; cases run
    | some r =>
      simp only [lookup,bind,Except.bind,pure,Except.pure] at run
      obtain ⟨rs,mapped,state,code⟩ := ih run
      refine ⟨r :: rs,?_,?_,?_⟩
      · simp only [List.mapM_cons,lookup,mapped]
        rfl
      · simpa only [List.foldl_cons] using state
      · rw [code]
        apply Array.toList_inj.mp
        simp [Array.toList_push,List.append_assoc]


private theorem selected_arguments {ctx : Ctx} {f : Clif.Function} (func : ctx.func = f)
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b)
    {bc : Clif.BlockCall} {index : Nat} (selected : (destinations b.term)[index]? = some (bc.block,bc.args.map Clif.TryArg.val)) {input next : State} {args : Array Reg}
    (run : branchArgs ctx input bi index = .ok (args,next)) :
    next = bc.args.foldl State.mark input ∧ bc.args.mapM ctx.valueReg? = some args.toList := by
  have source : ctx.func.blocks[bi]! = b := by simp only [func,getElem!_def,block,Option.getD_some]
  unfold branchArgs at run
  rw [source] at run
  dsimp only at run
  rw [selected] at run
  dsimp only at run
  split at run
  · rename_i target found
    split at run
    · cases run
    · let ti := (input.instBlock.findIdx? (· == bi)).getD 0 + b.body.length
      let reserved := input.tryRegs[ti]!
      let nh := match b.term with
        | .tryCall _ _ et | .tryCallIndirect _ _ et => et.handlers.length
        | _ => 0
      change (do
        let result ← forIn (bc.args.map Clif.TryArg.val) (input,#[]) (argStep ctx reserved.1 reserved.2 index nh)
        pure (result.2,result.1)) = .ok (args,next) at run
      cases loop : forIn (bc.args.map Clif.TryArg.val) (input,#[]) (argStep ctx reserved.1 reserved.2 index nh) with
      | error e => simp only [loop,bind,Except.bind] at run; cases run
      | ok pair =>
        obtain ⟨state,registers⟩ := pair
        simp only [loop,bind,Except.bind,pure,Except.pure] at run
        cases run
        obtain ⟨rs,mapped,state,code⟩ := val_loop loop
        exact ⟨state,by simpa only [code,Array.empty_append,List.toList_toArray] using mapped⟩
  · cases run


private theorem selected_destination {t : Clif.Terminator} {index : Nat} {bc : Clif.BlockCall}
    (selected : (dests t)[index]? = some bc) :
    (destinations t)[index]? = some (bc.block,bc.args.map Clif.TryArg.val) := by
  have same : destinations t = (dests t).map (fun bc => (bc.block,bc.args.map Clif.TryArg.val)) := by
    cases t <;> simp_all [dests,destinations,List.map_map,Function.comp_def]
  simp only [same,List.getElem?_map,selected,Option.map_some]

/-- Actual ordinary successor collection modifies exactly the demanded values,
including repeated arguments. Other compiler state is preserved. -/
theorem stock_branchArgs_selected_marks {ctx : Ctx} {f : Clif.Function}
    (func : ctx.func = f) {bi index : Nat} {b : Clif.Block}
    (block : f.blocks[bi]? = some b) {bc : Clif.BlockCall}
    (selected : (dests b.term)[index]? = some bc) {input next : State} {args : Array Reg}
    (call : branchArgs ctx input bi index = .ok (args,next)) :
    next = bc.args.foldl State.mark input := by
  exact (selected_arguments func block (selected_destination selected) call).1

/-- The same actual outgoing call derives its source register map, needed to
prove demand bounds without a certificate from the accepted program. -/
theorem stock_branchArgs_selected_mapping {ctx : Ctx} {f : Clif.Function}
    (func : ctx.func = f) {bi index : Nat} {b : Clif.Block}
    (block : f.blocks[bi]? = some b) {bc : Clif.BlockCall}
    (selected : (dests b.term)[index]? = some bc) {input next : State} {args : Array Reg}
    (call : branchArgs ctx input bi index = .ok (args,next)) :
    bc.args.mapM ctx.valueReg? = some args.toList := by
  exact (selected_arguments func block (selected_destination selected) call).2

end Backend.Stock.Proof
