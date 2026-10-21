import FV.Backend.Lowering.StockLogical

namespace Backend.Stock.Scalar
set_option autoImplicit false

abbrev abiEligible := Arithmetic.abiEligible

def constantEligible (stm : Clif.Stmt) : Bool :=
  match stm.inst with
  | .iconst ty _ => ty == .i32 || ty == .i64
  | _ => false

def bodyEligible (stm : Clif.Stmt) : Bool := Logical.bodyEligible stm || constantEligible stm

def eligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [b] => b.body.all bodyEligible &&
      (match b.term with | .ret _ => true | _ => false) &&
      f.sig.params.all abiEligible && f.sig.returns.all abiEligible
  | _ => false

/-- Previously shipped classes keep their exact selectors and route ordering. -/
def activationEligible (f : Clif.Function) : Bool := eligible f && !Logical.eligible f

def lowerCandidate (f : Clif.Function) : Except String VCode :=
  if !activationEligible f then Logical.lowerCandidate f
  else do
    let result ← Stock.lower f
    if result.edgeArgs.all (fun row => row.all (·.isEmpty)) then pure result.code
    else throw "Stock scalar candidate has nonempty edge arguments"

end Backend.Stock.Scalar
