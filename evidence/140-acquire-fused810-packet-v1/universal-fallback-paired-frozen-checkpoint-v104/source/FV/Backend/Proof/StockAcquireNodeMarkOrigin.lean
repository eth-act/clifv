import FV.Backend.Proof.StockAcquireActualCoreReadMarked

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm lowerBlockCore assembleOriginalBlock branchArgs

private def blockData (f : Clif.Function) (term : Clif.Terminator) : Except String V :=
  match term with
  | .tryCall .. | .tryCallIndirect .. => tryCallData f term
  | _ => termData (abiTerm f term)

/-- An actual node either preserves marks and scans or records the exact complete core that changes them. -/
theorem lowerNode_mark_origin {ctx : Ctx} {f : Clif.Function} {ranges : Array (Nat × Nat)} {order : Order}
    {params : List Nat} {label : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    (output.state.sunk = input.state.sunk ∧ output.blockScans = input.blockScans) ∨
    ∃ (bi : Nat) (data : V) (core : LoweredBlockCore),
      lowerBlockCore ctx order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2 data
        order.successors[label]! input.state = .ok core ∧ output.state = core.state ∧
      output.blockScans = input.blockScans.push core.scan := by
  cases node : order.nodes[label]! with
  | edge pred k target =>
    unfold lowerNode at run
    simp only [node] at run
    cases edge : branchArgs ctx input.state pred k with
    | error message => simp only [edge,bind,Except.bind] at run; cases run
    | ok pair =>
      obtain ⟨args,next⟩ := pair
      simp only [edge,bind,Except.bind,pure,Except.pure] at run
      cases run
      exact Or.inl ⟨Coverage.stock_branchArgs_sunk edge,rfl⟩
  | original bi =>
    let block := f.blocks[bi]!
    let start := ranges[bi]!.1
    let stop := ranges[bi]!.2
    let reject : Bool := (match block.term with | .ret .. => true | _ => false) &&
      (sretRet f).isEmpty && (sigRets f.sig != f.sig.returns)
    have normal : lowerNode ctx ranges order f params label input = (do
        let data ← blockData f block.term
        if reject then throw "sret parameter is not an entry-block parameter"
        let lowered ← lowerBlockCore ctx order f block bi start stop data order.successors[label]! input.state
        let assembled ← assembleOriginalBlock ctx f block bi label order.successors[label]!
          lowered.outgoing params lowered.state.uses lowered.code
        pure {recordCore input lowered bi stop with
          blocks := input.blocks.set! label assembled,
          edgeArgs := input.edgeArgs.set! label lowered.outgoing}) := by
      unfold lowerNode
      simp only [node]
      dsimp only [blockData,reject,block,start,stop]
      split <;> simp_all only [reject] <;> rfl
    rw [normal] at run
    cases dataRun : blockData f block.term with
    | error message => simp only [dataRun,bind,Except.bind] at run; cases run
    | ok data =>
      simp only [dataRun,bind,Except.bind] at run
      split at run
      · cases run
      · cases coreRun : lowerBlockCore ctx order f block bi start stop data order.successors[label]! input.state with
        | error message => simp only [coreRun] at run; cases run
        | ok core =>
          simp only [coreRun] at run
          cases assembled : assembleOriginalBlock ctx f block bi label order.successors[label]!
              core.outgoing params core.state.uses core.code with
          | error message => simp only [assembled] at run; cases run
          | ok finished =>
            simp only [assembled,pure,Except.pure] at run
            cases run
            exact Or.inr ⟨bi,data,core,coreRun,rfl,rfl⟩

end Backend.Stock.Proof.Acquire810
