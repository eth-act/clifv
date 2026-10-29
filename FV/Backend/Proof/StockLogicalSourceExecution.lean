module

public import FV.Backend.Proof.StockLogicalBodyRefines
public import FV.Backend.Proof.StockPureSourceExecution

@[expose] public section

/-! Compatibility variants using the shared pure-source execution proof. -/
namespace Backend.Stock.Proof.LogicalBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem family_pure {inst : Clif.Inst} (family : Family inst) : pureInst inst = true := by
  rcases family with ⟨subtract,ty,x,y,rfl⟩ | ⟨ty,c,x,y,rfl⟩ | ⟨kind,ty,x,y,rfl⟩
  all_goals rfl

def SourceFrameEq (s t : Clif.State) : Prop :=
  t.callers = s.callers ∧ t.frame.func = s.frame.func ∧
    t.frame.slots = s.frame.slots ∧ t.frame.term = s.frame.term


theorem actual_logical_source_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body) {record : ScanRecord} {j : Nat} {stm : Clif.Stmt}
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f event.block + j)
    (family : Family stm.inst)
    {env : Clif.Env} {cp : Clif.Program} {s t : Clif.State} {rest : List Clif.Stmt}
    (remaining : s.frame.body = stm :: rest) (next : Clif.step env cp s = .next t) :
    IndexedSourceInst env cp f event.ctx event.block record.inst
      (j,s.frame,s.mem) (j+1,t.frame,t.mem) := by
  exact PureBody.actual_pure_source_step run events split statement current
    (family_pure family) remaining next

theorem actual_logical_source_execution_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    (family : ∀ stm ∈ b.body, Family stm.inst)
    {env : Clif.Env} {cp : Clif.Program} {fuel j : Nat} {s : Clif.State}
    (bound : j ≤ b.body.length) (remaining : s.frame.body = b.body.drop j)
    {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel s = .returned vals mem) :
    ∃ t left, left + (b.body.length-j) = fuel ∧
      Clif.runLoop env cp left t = .returned vals mem ∧ t.frame.body = [] ∧
      SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        (List.range' (blockStart f event.block+j) (b.body.length-j))
        (j,s.frame,s.mem) (b.body.length,t.frame,t.mem) ∧ SourceFrameEq s t := by
  exact PureBody.actual_pure_source_execution_frame run events split
    (fun stm member => family_pure (family stm member)) bound remaining returned

end Backend.Stock.Proof.LogicalBody
