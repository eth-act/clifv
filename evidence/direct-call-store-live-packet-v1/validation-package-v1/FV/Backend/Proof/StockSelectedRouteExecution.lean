import FV.Backend.Proof.StockSelectedRoutes
import FV.Backend.Proof.StockComputedCfg
import FV.Backend.Proof.PerEdgeSeq

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem selected_successor {result : Result} {ps : Array (Array Nat)}
    (computed : result.code.cfg = .ok (result.order.successors,ps))
    {label index target : Nat} (selected : result.order.successors[label]![index]? = some target) :
    succOf result.code label index = some target := by
  cases row : result.order.successors[label]? with
  | none =>
    simp only [getElem!_def,row,Option.getD_none] at selected
    change (#[] : Array Nat)[index]? = some target at selected
    simp at selected
  | some values => simpa [succOf,computed,getElem!_def,row] using selected

/-- Execute the selected actual copy route after a complete stopped branch
segment. A critical route includes its real emitted synthetic jump and second
copy; the machine world is preserved across that jump. -/
theorem SelectedCopyRoute.execute {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {isem : Backend.Proof.Sem} (driver : DriverSemG isem)
    {label index target k0 offset : Nat} {vb : VBlock} {code : List MInst}
    {ρ regs next : Nat → CV} {world prefixWorld endWorld : Arm.ArmState}
    {inst : MInst} {ops : Array Operand}
    (route : SelectedCopyRoute result label index regs target next)
    (block : result.code.blocks[label]? = some vb) (segment : SegAt vb k0 code)
    (execution : seqRun isem code ρ world =
      some (.stop offset inst ops regs prefixWorld [] endWorld (.goto index)))
    (last : k0+offset+1 = vb.insts.size) :
    Star (VStepAt result.code result.edgeArgs isem)
      (.run ⟨label,k0,ρ,world⟩) (.run ⟨target,0,next,endWorld⟩) := by
  obtain ⟨ps,computed⟩ := stock_lower_computed_cfg run scope
  cases route with
  | direct successor copied =>
    exact seqRun_goto_starAt (edges := result.edgeArgs) block segment execution last (selected_successor computed successor)
      (by simpa only [vdefUpd,writeV,List.foldl_nil,Array.toList_empty,List.filter_nil,List.zip_nil_left,List.zip_nil_right] using copied)
  | @synthetic middle successor identity successors placed copied =>
    have first := seqRun_goto_starAt (edges := result.edgeArgs) block segment execution last (selected_successor computed successor)
      (by simpa only [vdefUpd,writeV,List.foldl_nil,Array.toList_empty,List.filter_nil,List.zip_nil_left,List.zip_nil_right] using identity)
    obtain ⟨middleBlock,found,codeEq⟩ := placed
    have jumpRun : seqRun isem [.jump target] regs endWorld =
        some (.stop 0 (.jump target) #[] regs endWorld [] endWorld (.goto 0)) := by
      simp only [seqRun,show (MInst.jump target).operands = .ok #[] from rfl,
        show vuses (#[] : Array Operand) regs = [] from rfl,driver.jump]
      rfl
    have middleSegment : SegAt middleBlock 0 [.jump target] := by
      intro k bound
      have zero : k = 0 := by simp only [List.length_singleton] at bound; omega
      subst k
      rw [codeEq]
      rfl
    have lastMiddle : 0+0+1 = middleBlock.insts.size := by rw [codeEq]; rfl
    have nextSuccessor : result.order.successors[middle]![0]? = some target := by
      simp only [getElem!_def,successors,Option.getD_some]
      rfl
    have second := seqRun_goto_starAt found middleSegment jumpRun lastMiddle
      (selected_successor computed nextSuccessor)
      (by simpa only [vdefUpd,writeV,List.foldl_nil,Array.toList_empty,List.filter_nil,List.zip_nil_left,List.zip_nil_right] using copied)
    exact first.trans second

end Backend.Stock.Proof
