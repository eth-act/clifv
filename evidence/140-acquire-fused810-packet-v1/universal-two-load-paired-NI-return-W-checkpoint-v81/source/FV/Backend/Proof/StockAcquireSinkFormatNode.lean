import FV.Backend.Proof.StockAcquireSinkFormatContext

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] lowerBlockCore assembleOriginalBlock

private def blockData (f : Clif.Function) (term : Clif.Terminator) : Except String V :=
  match term with
  | .tryCall .. | .tryCallIndirect .. => tryCallData f term
  | _ => termData (abiTerm f term)

private theorem block_data_safe {ctx : Ctx} {f : Clif.Function}
    {term : Clif.Terminator} {data : V} (run : blockData f term = .ok data) :
    ∀ fmt fields,fmt = 16 ∨ fmt = 17 →
      (Backend.sem ctx).unData 152 data ≠ some (fmt,fields) := by
  unfold blockData at run
  split at run
  · exact SinkRules.try_call_data_no_load run
  · exact SinkRules.try_call_data_no_load run
  · exact SinkRules.term_data_no_load run

def DriverSinkFormatSources (f : Clif.Function) (state : DriverState) : Prop :=
  ∀ event ∈ state.blockScans.toList,SinkFormatSources f event.ctx

/-- Every actual node preserves original source existence through terminators and exception reservations. -/
theorem lowerNode_sink_format_sources {ctx : Ctx} {f : Clif.Function}
    (sources : SinkFormatSources f ctx) {ranges : Array (Nat × Nat)} {order : Order}
    {params : List Nat} {label : Nat} {input output : DriverState}
    (prior : DriverSinkFormatSources f input)
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    DriverSinkFormatSources f output := by
  cases node : order.nodes[label]! with
  | edge pred k target =>
    unfold lowerNode at run
    simp only [node] at run
    cases edge : branchArgs ctx input.state pred k with
    | error message => simp only [edge,bind,Except.bind] at run; cases run
    | ok pair =>
      rcases pair with ⟨args,next⟩
      simp only [edge,bind,Except.bind,pure,Except.pure] at run
      cases run
      exact prior
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
      · cases core : lowerBlockCore ctx order f block bi start stop data order.successors[label]! input.state with
        | error message => simp only [core] at run; cases run
        | ok lowered =>
          simp only [core] at run
          cases assembled : assembleOriginalBlock ctx f block bi label order.successors[label]!
              lowered.outgoing params lowered.state.uses lowered.code with
          | error message => simp only [assembled] at run; cases run
          | ok finished =>
            simp only [assembled,pure,Except.pure] at run
            cases run
            intro event member
            change event ∈ (input.blockScans.push lowered.scan).toList at member
            simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
            rcases member with member | rfl
            · exact prior event member
            · exact blockCore_scan_sink_format_sources sources (block_data_safe dataRun) core

end Backend.Stock.Proof.Acquire810
