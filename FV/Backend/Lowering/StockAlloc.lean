import FV.Backend.RegallocOps

/-! Stock's initial register allocation, separated from source color analysis.
Requests retain layout order and exception allocation points. -/

namespace Backend.Stock

/-- Stock reserves 192 register numbers for physical-register representations. -/
def firstUserVreg : Nat := 192

inductive AllocationRequest where
  | value (id : Nat)
  | exception (instruction returns payloads : Nat)
  deriving Inhabited, Repr, DecidableEq

def AllocationRequest.count : AllocationRequest → Nat
  | .value _ => 1
  | .exception _ rets pays => rets + pays

def AllocationRequest.value? : AllocationRequest → Option Nat
  | .value x => some x
  | .exception .. => none

structure Allocation where
  valReg : Array (Option Reg)
  base : LState
  tryRegs : Array (List Reg × List Reg)
  deriving Inhabited

def Allocation.initial (values instructions : Nat) : Allocation := {
  valReg := Array.replicate values none
  base := { nextVreg := firstUserVreg, classes := Array.replicate firstUserVreg .int }
  tryRegs := Array.replicate instructions ([], []) }

def Allocation.step (a : Allocation) : AllocationRequest → Allocation
  | .value x =>
    let (r, base) := a.base.fresh .int
    { a with valReg := a.valReg.set! x (some r), base }
  | .exception i rets pays =>
    let rs := (List.range rets).map fun j => Reg.vreg (a.base.nextVreg + j) .int
    let ps := (List.range pays).map fun j => Reg.vreg (a.base.nextVreg + rets + j) .int
    { a with
      base := { a.base with
        nextVreg := a.base.nextVreg + rets + pays
        classes := a.base.classes ++ Array.replicate (rets + pays) .int }
      tryRegs := a.tryRegs.set! i (rs, ps) }

def allocateRequests (values instructions : Nat) (requests : List AllocationRequest) : Allocation :=
  requests.foldl Allocation.step (Allocation.initial values instructions)

def exceptionReservation (f : Clif.Function) (ranges : Array (Nat × Nat)) (bi : Nat) :
    Clif.Terminator → Except String (Option (Nat × Nat × Nat))
  | .tryCall _ _ et | .tryCallIndirect _ _ et => do
    let (sig, _) ← exnTableOpnd f et
    if sig.returns.any (·.ty == .i128) then throw "try_call returning i128"
    pure (some (ranges[bi]!.2 - 1, sig.returns.length, (payloadRegs sig.callConv).length))
  | _ => pure none

def blockAllocationRequests (f : Clif.Function) (ranges : Array (Nat × Nat))
    (b : Clif.Block) (bi : Nat) : Except String (List AllocationRequest) := do
  let extra ← exceptionReservation f ranges bi b.term
  let values := (b.params.map fun p => AllocationRequest.value p.1) ++
    b.body.flatMap (fun s => s.results.map AllocationRequest.value)
  pure (values ++ extra.toList.map fun (i, rets, pays) => .exception i rets pays)

def blockValues (b : Clif.Block) : List Nat :=
  b.params.map Prod.fst ++ b.body.flatMap (·.results)

/-- Parameter/result requests and exception reservations occur in the same
layout traversal as the pinned stock implementation. -/
def allocationRequests (f : Clif.Function) (ranges : Array (Nat × Nat)) :
    Except String (List AllocationRequest) := do
  let chunks ← f.blocks.zipIdx.mapM fun (b, bi) => blockAllocationRequests f ranges b bi
  pure chunks.flatten

end Backend.Stock
