module

public import FV.Backend.Lowering.StockScalarProduction
public import FV.Backend.DeadCleanup

public section

namespace Backend.Stock.Arithmetic
set_option autoImplicit false

/-- The next input-syntax class: ordinary i32/i64 parameters and returns,
one return block, and any straight-line add/sub body. Source scope and SSA are
checked separately by the production validator. -/
def bodyEligible (stm : Clif.Stmt) : Bool :=
  match stm.inst with
  | .binary op ty _ _ => (op == .iadd || op == .isub) && (ty == .i32 || ty == .i64)
  | _ => false

def abiEligible (param : Clif.AbiParam) : Bool :=
  param.purpose == .normal && (param.ty == .i32 || param.ty == .i64)

def eligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [b] => b.body.all bodyEligible &&
      (match b.term with | .ret _ => true | _ => false) &&
      f.sig.params.all abiEligible && f.sig.returns.all abiEligible
  | _ => false

def stage (cleanup : Bool) (vc : VCode) : VCode :=
  if cleanup then Backend.DeadCleanup.prune vc else vc

/-- Data-only candidate. Previously shipped classes retain their exact route;
new arithmetic outputs keep the actual Stock code and diagnostics. Edge data
is discarded only after checking that every row is empty. The enclosing
production pipeline is responsible for validation and transactional fallback. -/
def lowerCandidate (f : Clif.Function) : Except String VCode :=
  if D0.eligible f || ScalarAdd.activationEligible f then ScalarAdd.lower f
  else if eligible f then do
    let result ← Stock.lower f
    if result.edgeArgs.all (fun row => row.all (·.isEmpty)) then pure result.code
    else throw "Stock arithmetic candidate has nonempty edge arguments"
  else ScalarAdd.lower f

end Backend.Stock.Arithmetic
