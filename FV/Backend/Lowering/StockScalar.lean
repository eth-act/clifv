import FV.Backend.Lowering.StockLogical

namespace Backend.Stock.Scalar
set_option autoImplicit false

abbrev abiEligible := Arithmetic.abiEligible

def constantEligible (stm : Clif.Stmt) : Bool :=
  match stm.inst with
  | .iconst ty _ => ty == .i32 || ty == .i64
  | _ => false

def bodyEligible (stm : Clif.Stmt) : Bool := Logical.bodyEligible stm || constantEligible stm

/-- Extend source syntax while preserving the old constant classifier and its theorem. -/
def notEligible (stm : Clif.Stmt) : Bool :=
  match stm.inst with
  | .unary .bnot ty _ => ty == .i32 || ty == .i64
  | _ => false

def extendedBodyEligible (stm : Clif.Stmt) : Bool := bodyEligible stm || notEligible stm

/-- Multiplication extends the source family; all earlier classifiers stay fixed. -/
def mulEligible (stm : Clif.Stmt) : Bool :=
  match stm.inst with
  | .binary .imul ty _ _ => ty == .i32 || ty == .i64
  | _ => false

def mulBodyEligible (stm : Clif.Stmt) : Bool := extendedBodyEligible stm || mulEligible stm

/-- Shifts extend the source family while earlier selectors retain their meaning. -/
def shiftEligible (stm : Clif.Stmt) : Bool :=
  match stm.inst with
  | .binary .ishl ty _ _ | .binary .ushr ty _ _ | .binary .sshr ty _ _ => ty == .i32 || ty == .i64
  | _ => false

def shiftBodyEligible (stm : Clif.Stmt) : Bool := mulBodyEligible stm || shiftEligible stm

/-- Casts extend source syntax without changing earlier selectors. -/
def castEligible (stm : Clif.Stmt) : Bool :=
  match stm.inst with
  | .extend _ ty _ | .ireduce ty _ => ty == .i32 || ty == .i64
  | _ => false

def castBodyEligible (stm : Clif.Stmt) : Bool := shiftBodyEligible stm || castEligible stm

/-- Unary bit operations and rotations extend the class while old selectors stay fixed. -/
def bitEligible (stm : Clif.Stmt) : Bool :=
  match stm.inst with
  | .unary .ineg ty _ | .unary .clz ty _ | .unary .ctz ty _
  | .unary .bitrev ty _ | .unary .bswap ty _
  | .binary .rotl ty _ _ | .binary .rotr ty _ _ => ty == .i32 || ty == .i64
  | _ => false

def bitBodyEligible (stm : Clif.Stmt) : Bool := castBodyEligible stm || bitEligible stm

/-- Popcount extends the source family while all previous selectors stay fixed. -/
def popcountEligible (stm : Clif.Stmt) : Bool :=
  match stm.inst with
  | .unary .popcnt ty _ => ty == .i32 || ty == .i64
  | _ => false

def popcountBodyEligible (stm : Clif.Stmt) : Bool := bitBodyEligible stm || popcountEligible stm

/-- Signed and unsigned min/max extend source syntax while prior selectors remain fixed. -/
def minmaxEligible (stm : Clif.Stmt) : Bool :=
  match stm.inst with
  | .binary .smin ty _ _ | .binary .smax ty _ _
  | .binary .umin ty _ _ | .binary .umax ty _ _ => ty == .i32 || ty == .i64
  | _ => false

def minmaxBodyEligible (stm : Clif.Stmt) : Bool := popcountBodyEligible stm || minmaxEligible stm

/-- Comparisons compose with prior scalar classes, including real cast look-through. -/
def cmpEligible (stm : Clif.Stmt) : Bool :=
  match stm.inst with
  | .icmp _ ty _ _ => ty == .i32 || ty == .i64
  | _ => false

def cmpBodyEligible (stm : Clif.Stmt) : Bool := minmaxBodyEligible stm || cmpEligible stm

/-- High multiplication extends the original source family; prior selectors stay. -/
def highmulEligible (stm : Clif.Stmt) : Bool :=
  match stm.inst with
  | .binary .smulhi ty _ _ | .binary .umulhi ty _ _ => ty == .i32 || ty == .i64
  | _ => false

def highmulBodyEligible (stm : Clif.Stmt) : Bool := cmpBodyEligible stm || highmulEligible stm

def eligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [b] => b.body.all highmulBodyEligible &&
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
