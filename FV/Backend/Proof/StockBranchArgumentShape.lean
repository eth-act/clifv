import FV.Backend.Proof.StockAliasBounds
import FV.Backend.Proof.IselCtlCall
import FV.Backend.Proof.RegallocCSem

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Internal outgoing-vector class fact, allowing repeated source arguments. -/
def ArgumentShape (args : Array Reg) : Prop := ∀ r ∈ args.toList,∃ n,r = .vreg n .int

private def argStep (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (acc : State × Array Reg) : Except String (ForInStep (State × Array Reg)) := do
  match arg with
  | .val v =>
    let some r := ctx.valueReg? v | throw s!"unknown value v{v}"
    pure (.yield (acc.1.mark v,acc.2.push r))
  | .ret i =>
    if index < nh then throw "try_call return on exception edge"
    let some r := rets[i]? | throw "try_call return index"
    pure (.yield (acc.1,acc.2.push r))
  | .exn i =>
    if index == nh then throw "try_call payload on normal edge"
    let some r := pays[i]? | throw "try_call payload index"
    pure (.yield (acc.1,acc.2.push r))

private theorem argStep_shape {ctx : Ctx} {rets pays : List Reg} {index nh : Nat}
    (values : ∀ x r,ctx.valueReg? x = some r → ∃ n,r = .vreg n .int)
    (reserved : ∀ r ∈ rets ++ pays,∃ n,r = .vreg n .int)
    {arg : Clif.TryArg} {input output : State × Array Reg}
    (run : argStep ctx rets pays index nh arg input = .ok (.yield output)) :
    ∃ r,output.2 = input.2.push r ∧ output.1.tryRegs = input.1.tryRegs ∧ ∃ n,r = .vreg n .int := by
  cases arg with
  | val v =>
    simp only [argStep,bind,Except.bind,pure,Except.pure] at run
    cases found : ctx.valueReg? v with
    | none => simp [found,bind,Except.bind] at run
    | some r =>
      simp only [found,pure,Except.pure] at run
      cases run
      exact ⟨r,rfl,rfl,values v r found⟩
  | ret i =>
    simp only [argStep,bind,Except.bind,pure,Except.pure] at run
    split at run
    · cases run
    · cases found : rets[i]? with
      | none => simp [found,bind,Except.bind] at run
      | some r =>
        simp only [found,pure,Except.pure] at run
        cases run
        exact ⟨r,rfl,rfl,reserved r (List.mem_append_left _ (List.mem_of_getElem? found))⟩
  | exn i =>
    simp only [argStep,bind,Except.bind,pure,Except.pure] at run
    split at run
    · cases run
    · cases found : pays[i]? with
      | none => simp [found,bind,Except.bind] at run
      | some r =>
        simp only [found,pure,Except.pure] at run
        cases run
        exact ⟨r,rfl,rfl,reserved r (List.mem_append_right _ (List.mem_of_getElem? found))⟩

private theorem argStep_not_done (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (input output : State × Array Reg) :
    argStep ctx rets pays index nh arg input ≠ .ok (.done output) := by
  cases arg <;> simp only [argStep,bind,Except.bind,pure,Except.pure]
  all_goals repeat' split
  all_goals simp [pure,Except.pure,bind,Except.bind]

private theorem loop_shape {ctx : Ctx} {rets pays : List Reg} {index nh : Nat}
    (values : ∀ x r,ctx.valueReg? x = some r → ∃ n,r = .vreg n .int)
    (reserved : ∀ r ∈ rets ++ pays,∃ n,r = .vreg n .int)
    {xs : List Clif.TryArg} {input output : State × Array Reg}
    (shaped : ArgumentShape input.2)
    (run : forIn xs input (argStep ctx rets pays index nh) = .ok output) :
    output.2.size = input.2.size + xs.length ∧ ArgumentShape output.2 ∧ output.1.tryRegs = input.1.tryRegs := by
  induction xs generalizing input with
  | nil => cases run; exact ⟨by simp,shaped,rfl⟩
  | cons x xs ih =>
    rw [List.forIn_cons] at run
    cases first : argStep ctx rets pays index nh x input with
    | error err => simp only [first,bind,Except.bind] at run; cases run
    | ok step =>
      cases step with
      | done stop => exact False.elim (argStep_not_done _ _ _ _ _ _ _ _ first)
      | yield mid =>
        simp only [first,bind,Except.bind] at run
        obtain ⟨r,added,frame,n,rShape⟩ := argStep_shape values reserved first
        have midShape : ArgumentShape mid.2 := by
          rw [added]
          intro q member
          simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
          rcases member with old | equal
          · exact shaped q old
          · subst q; exact ⟨n,rShape⟩
        obtain ⟨count,shape,framed⟩ := ih midShape run
        refine ⟨?_,shape,framed.trans frame⟩
        rw [added,Array.size_push] at count
        simp only [List.length_cons]
        omega

/-- Successful actual argument collection exposes its selected source
successor, real destination and exact target arity, and preserves virtual-int
class for ordinary and reserved normal/exception arguments. Build-context and
reservation facts are derived from actual construction; the reservation frame
is an internal driver-state fact, never an accepted-source condition. -/
theorem stock_branchArgs_shape {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial))
    {input next : State} (reservations : input.tryRegs = initial.tryRegs)
    {bi j : Nat} {args : Array Reg} (call : branchArgs ctx input bi j = .ok (args,next)) :
    (∃ (id : Nat) (sourceArgs : List Clif.TryArg) (target : Clif.Block),
      (destinations ctx.func.blocks[bi]!.term)[j]? = some (id,sourceArgs) ∧
      ctx.func.block? id = some target ∧ args.size = target.params.length) ∧
    ArgumentShape args ∧ next.tryRegs = input.tryRegs := by
  have values : ∀ x r,ctx.valueReg? x = some r → ∃ n,r = .vreg n .int := by
    intro x r found
    obtain ⟨n,shape,_⟩ := (buildCtx_allocated build).2.2.1 x r found
    exact ⟨n,shape⟩
  have reserved : ∀ (ti : Nat) r,r ∈ (input.tryRegs[ti]!).1 ++ (input.tryRegs[ti]!).2 → ∃ n,r = .vreg n .int := by
    intro ti r member
    rw [reservations] at member
    cases found : initial.tryRegs[ti]? with
    | none => simp only [getElem!_def,found] at member; cases member
    | some rs =>
      simp only [getElem!_def,found] at member
      obtain ⟨n,shape,_⟩ := buildCtx_reservedBelow build ti rs found r member
      exact ⟨n,shape⟩
  unfold branchArgs at call
  dsimp only at call
  cases selected : (destinations ctx.func.blocks[bi]!.term)[j]? with
  | none => simp only [selected] at call; cases call
  | some pair =>
    obtain ⟨id,sourceArgs⟩ := pair
    rw [selected] at call
    dsimp only at call
    cases found : ctx.func.block? id with
    | none => simp only [found] at call; cases call
    | some target =>
      rw [found] at call
      dsimp only at call
      split at call
      · cases call
      · rename_i arity
        let b := ctx.func.blocks[bi]!
        let ti := (input.instBlock.findIdx? (· == bi)).getD 0 + b.body.length
        let nh := match b.term with
          | .tryCall _ _ et | .tryCallIndirect _ _ et => et.handlers.length
          | _ => 0
        change (do
          let pair ← forIn sourceArgs (input,#[])
            (argStep ctx (input.tryRegs[ti]!).1 (input.tryRegs[ti]!).2 j nh)
          pure (pair.2,pair.1)) = .ok (args,next) at call
        cases loop : forIn sourceArgs (input,#[]) (argStep ctx (input.tryRegs[ti]!).1 (input.tryRegs[ti]!).2 j nh) with
        | error err => simp only [loop,bind,Except.bind] at call; cases call
        | ok pair =>
          obtain ⟨state,rs⟩ := pair
          simp only [loop,bind,Except.bind,pure,Except.pure] at call
          cases call
          obtain ⟨count,shape,frame⟩ := loop_shape values (reserved ti) (by simp [ArgumentShape]) loop
          have sameArity : sourceArgs.length = target.params.length := by simpa using arity
          exact ⟨⟨id,sourceArgs,target,rfl,found,by simpa only [Array.size_empty,Nat.zero_add,sameArity] using count⟩,shape,frame⟩

end Backend.Stock.Proof
