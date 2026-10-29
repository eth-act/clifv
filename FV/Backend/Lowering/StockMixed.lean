module

public import FV.Backend.Lowering.StockArithmetic

@[expose] public section

namespace Backend.Stock.Mixed
set_option autoImplicit false

abbrev abiEligible := Arithmetic.abiEligible

def bodyEligible (stm : Clif.Stmt) : Bool :=
  match stm.inst with
  | .binary op ty _ _ => (op == .iadd || op == .isub) && (ty == .i32 || ty == .i64)
  | .select ty _ _ _ => ty == .i32 || ty == .i64
  | _ => false

def eligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [b] => b.body.all bodyEligible &&
      (match b.term with | .ret _ => true | _ => false) &&
      f.sig.params.all abiEligible && f.sig.returns.all abiEligible
  | _ => false

/-- Previously shipped arithmetic classes retain their exact selector. -/
def activationEligible (f : Clif.Function) : Bool :=
  eligible f && !Arithmetic.eligible f

def lowerCandidate (f : Clif.Function) : Except String VCode :=
  if !activationEligible f then Arithmetic.lowerCandidate f
  else do
    let result ← Stock.lower f
    if result.edgeArgs.all (fun row => row.all (·.isEmpty)) then pure result.code
    else throw "Stock mixed candidate has nonempty edge arguments"


end Backend.Stock.Mixed
