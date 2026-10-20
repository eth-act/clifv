import FV.Backend.Proof.StockCriticalSplit
import FV.Backend.Proof.PerEdgeSpillEntryFixture

namespace Backend.Stock.Proof.CriticalSplitFixture
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgeSpill
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
private def signature : Clif.Signature := {returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
private def table : Clif.ExnTable := {sig := 0,normal := ⟨1,[.ret 0]⟩,items := []}
/-- The second source predecessor is unreachable. Source indegree still counts
it, so a one-successor TryCall must be forcibly split before preparation. -/
def function (indirect : Bool) : Clif.Function := {
  name := "stock_forced_single_try_split",sig := signature,sigDecls := [(0,signature)],externs := [(0,{name := "callee",sig := signature})]
  blocks := [{id := 0,body := (if indirect then [⟨[0],.iconst .i64 4096⟩] else []),term := (if indirect then .tryCallIndirect 0 [] table else .tryCall 0 [] table)},
    {id := 1,params := [(2,.i64)],term := .ret [2]},
    {id := 2,body := [⟨[7],.iconst .i64 9⟩],term := .jump ⟨1,[7]⟩}] }
private def pipeline (indirect : Bool) : Except String (Result × EdgeVCode × RFunc × AFunc) := do
  let result ← Stock.lower (function indirect)
  let p ← prepareAt result.code result.edgeArgs
  let rf ← allocResultAt p.code p.edges (.error "force indexed split witness")
  let af ← lowerRFunc p.code rf
  pure (result,p,rf,af)
private theorem observed (indirect : Bool) : (pipeline indirect).isOk = true := by cases indirect <;> decide +kernel
private theorem scope (indirect : Bool) : LowerScope (function indirect) := by
  cases indirect <;> apply lowerScope_of <;> decide +kernel
private theorem arity (indirect : Bool) : ArityOk (function indirect) := by
  cases indirect <;> apply arityOk_of <;> decide +kernel

structure Output (indirect : Bool) where
  result : Result
  prepared : EdgeVCode
  rf : RFunc
  af : AFunc
  lowered : Stock.lower (function indirect) = .ok result
  scope : LowerScope (function indirect)
  arity : ArityOk (function indirect)
  prepare : prepareAt result.code result.edgeArgs = .ok prepared
  fallback : rf = spillAllocAt prepared.code prepared.edges
  accepted : checkAllocAt prepared.code prepared.edges rf = .ok ()
  physical : lowerRFunc prepared.code rf = .ok af

/-- Complete direct/indirect one-successor TryCall sources retain the
unreachable source predecessor, original conditions and every successful
checked/physical stage while forced critical splitting is exercised. -/
theorem single_try_fixture (indirect : Bool) : Nonempty (Output indirect) := by
  have actual := observed indirect
  cases run : pipeline indirect with
  | error err => simp only [run,Except.isOk] at actual; cases actual
  | ok q =>
    unfold pipeline at run
    obtain ⟨result,lowered,h⟩ := Except.bind_ok run
    obtain ⟨p,prepare,h⟩ := Except.bind_ok h
    obtain ⟨rf,selected,h⟩ := Except.bind_ok h
    obtain ⟨af,physical,h⟩ := Except.bind_ok h
    cases h
    have accepted := PerEdge.allocResultAt_checked selected
    have fallback : rf = spillAllocAt p.code p.edges := by
      unfold allocResultAt checkedSpillAt at selected
      simp only [bind,Except.bind] at selected
      split at selected <;> cases selected
      rfl
    exact ⟨⟨result,p,rf,af,lowered,scope indirect,arity indirect,prepare,fallback,accepted,physical⟩⟩

end Backend.Stock.Proof.CriticalSplitFixture
