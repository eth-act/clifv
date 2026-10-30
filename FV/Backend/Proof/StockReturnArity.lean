import FV.Backend.Proof.IselCtlTerm
import FV.Backend.Proof.RegallocCSem
import FV.Backend.Proof.StockTraversalRecordOrigin
import FV.Backend.Proof.StockCoreScanOrigin

/-! Derive implicit return request arity from successful original source
execution, the original ABI signature condition and actual Stock lowering.
Helper success by itself is insufficient; no accepted-program guard is added. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

private theorem sret_signature {sig : Clif.Signature} (abi : sigAbiOk sig = true)
    (sret : (sigRets sig).any (·.purpose == .sret) = true) :
    sig.returns = [] ∧ (sigRets sig).length = 1 ∧ sigRets sig ≠ sig.returns := by
  have normal : sig.returns.all (·.purpose == .normal) = true := by
    simp only [sigAbiOk,Bool.and_eq_true] at abi
    exact abi.1.1.2
  have noSret : sig.returns.any (·.purpose == .sret) = false := by
    apply List.any_eq_false.mpr
    intro p member
    have purpose := List.all_eq_true.mp normal p member
    have same : p.purpose = .normal := beq_iff_eq.mp purpose
    rw [same]
    decide
  cases found : sig.params.find? (·.purpose == .sret) with
  | none => simp only [sigRets,found,noSret] at sret; cases sret
  | some p =>
    by_cases empty : sig.returns = []
    · simp [sigRets,found,empty]
    · have notEmpty : sig.returns.isEmpty = false := List.isEmpty_eq_false_iff.mpr empty
      simp [sigRets,found,notEmpty,noSret] at sret

private theorem sret_length (f : Clif.Function) : (sretRet f).length ≤ 1 := by
  unfold sretRet
  split
  · cases b : f.blocks.head? with
    | none => simp
    | some block =>
      cases i : f.sig.params.findIdx? (·.purpose == .sret) with
      | none => simp
      | some index => cases value : block.params[index]? <;> simp
  · simp

private theorem node_return_sret {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label bi : Nat} {input output : DriverState}
    (node : order.nodes[label]! = .original bi) {b : Clif.Block}
    (block : f.blocks[bi]! = b) {xs : List Nat} (ret : b.term = .ret xs)
    (run : lowerNode ctx ranges order f params label input = .ok output)
    (empty : sretRet f = []) : sigRets f.sig = f.sig.returns := by
  apply Classical.byContradiction
  intro different
  simp [lowerNode,node,block,ret,abiTerm,Backend.termData,empty,different] at run

private theorem source_return_count {env : Clif.Env} {cp : Clif.Program} {s : Clif.State}
    {xs : List Nat} {vals : List Clif.Val} {cm : Clif.Mem}
    (done : Clif.stepTerm env cp s (.ret xs) = .done vals cm) :
    xs.length = s.frame.func.sig.returns.length := by
  simp only [Clif.stepTerm] at done
  cases get : s.frame.getMany xs with
  | trap c => rw [get] at done; cases done
  | stuck msg => rw [get] at done; cases done
  | ok values =>
    rw [get] at done
    simp only [Clif.StepResult.ofRes,Clif.returnValues] at done
    rcases checkTys_cases s!"return values of %{s.frame.func.name}" values
      (Clif.AbiParam.tys s.frame.func.sig.returns) with typed | ⟨msg,stuck⟩
    · have count := congrArg List.length typed.2
      have length := (getMany_ok get).1
      simpa only [List.length_map,Clif.AbiParam.tys,← length] using count
    · rw [stuck] at done
      cases done

/-- Successful original source return derives exactly one implicit ABI request
in the struct-return case. Source execution establishes the explicit arity;
the actual original-node lowering establishes the available implicit pointer. -/
theorem stock_lower_sret_source_arity {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (abi : sigAbiOk f.sig = true)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {xs : List Nat} (ret : b.term = .ret xs)
    (sret : (sigRets f.sig).any (·.purpose == .sret) = true)
    {env : Clif.Env} {cp : Clif.Program} {s : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (func : s.frame.func = f) (done : Clif.stepTerm env cp s (.ret xs) = .done vals cm) :
    xs = [] ∧ (sretRet f).length = 1 ∧ (xs ++ sretRet f).length = 1 := by
  obtain ⟨noExplicit,abiLength,different⟩ := sret_signature abi sret
  have count := source_return_count done
  rw [func,noExplicit,List.length_nil] at count
  have noArgs : xs = [] := List.length_eq_zero_iff.mp count
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, bi, data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, nodeRun, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  have eventBlock : event.block = bi := by
    rw [eventEq]
    exact (stock_lowerBlockCore_scanOrigin coreRun).2.2.1
  have sourceBlock : f.blocks[bi]! = b := by simp only [getElem!_def,← eventBlock,block,Option.getD_some]
  have nonempty : sretRet f ≠ [] := fun empty => different (node_return_sret node sourceBlock ret nodeRun empty)
  have bound := sret_length f
  have one : (sretRet f).length = 1 := by
    have positive : (sretRet f).length ≠ 0 := fun h => nonempty (List.length_eq_zero_iff.mp h)
    omega
  exact ⟨noArgs,one,by rw [noArgs,List.nil_append,one]⟩
end Backend.Stock.Proof
