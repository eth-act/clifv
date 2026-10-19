import StockActualModesProbe

namespace E2E.LinkCheck.StrictStockProbe
open Backend Lean

def oracle (vc : VCode) : Except String Json := do
  let mut rows : Array (Array String) := #[]
  for b in vc.blocks do
    for i in b.insts do
      let ops ← i.operands
      rows := rows.push (Array.replicate ops.size "x0")
  pure <| Json.mkObj [
    ("ok", toJson true), ("checker", toJson "ok"),
    ("allocs", toJson rows), ("edits", Json.arr #[]),
    ("num_spillslots", toJson (0 : Nat))]

#eval do
  let f := Stock.D0.source "strict_stock_witness" .systemVI64 []
  for cleanup in [false, true] do
    let stage : VCode → VCode := cond cleanup DeadCleanup.prune id
    match Stock.D0.defaultLower f >>= (prepare ∘ stage) >>= oracle with
    | .error e => IO.println s!"oracle failed: {e}"
    | .ok answer =>
      match pipeWithLowering Stock.D0.defaultLower stage f 0 4096 answer with
      | .error e => IO.println s!"cleanup={cleanup} strict failed: {e}"
      | .ok a =>
        IO.println s!"cleanup={cleanup} strict_success=true checkAlloc={(checkAlloc a.vcp a.rf).isOk} answer={answer.compress}"

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

def fixedAnswer : Json := Json.mkObj [
  ("ok", toJson true), ("checker", toJson "ok"),
  ("allocs", toJson (#[#["x0"], #["x0"]] : Array (Array String))),
  ("edits", Json.arr #[]), ("num_spillslots", toJson (0 : Nat))]

/-- Fixed inhabited compiler witness; the actual selector must take Stock and
strict allocation must succeed and pass every existing local validator. -/
def accepted (cleanup : Bool) : Bool :=
  let f := Stock.D0.source "strict_stock_witness" .systemVI64 []
  let stage : VCode → VCode := cond cleanup DeadCleanup.prune id
  let result : Except String Bool := do
    let (origin, _) ← Stock.D0.selectWith Stock.lower f
    match origin with
    | .legacy => pure false
    | .stockD0 => do
      let a ← pipeWithLowering Stock.D0.defaultLower stage f 0 4096 fixedAnswer
      pure (Backend.Proof.Driver.lowerCheck f a.vc &&
        Backend.Proof.Driver.prepCheck (stage a.vc) a.vcp &&
        (checkAlloc a.vcp a.rf).isOk)
  result.toOption.getD false

-- witness: native_decide
theorem strict_stock_both_cleanup_modes (cleanup : Bool) : accepted cleanup = true := by
  cases cleanup <;> native_decide

#print axioms strict_stock_both_cleanup_modes

end E2E.LinkCheck.StrictStockProbe
