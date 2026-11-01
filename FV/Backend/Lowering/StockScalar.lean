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

/-- First complete colored source class, with every original operand value.
Old body selectors remain unchanged for artifact retention. -/
def singleDivEligible (b : Clif.Block) : Bool :=
  match b.body,b.term with
  | [⟨[z],.div _ ty _ _⟩],.ret [z'] => z == z' && (ty == .i32 || ty == .i64)
  | _,_ => false

/-- Previously proved scalar syntax before one final returned division.
The old single-division and pure-body classifiers remain unchanged. -/
def mixedDivEligible (b : Clif.Block) : Bool :=
  match b.body.reverse,b.term with
  | ⟨[z],.div _ ty _ _⟩ :: front,.ret [z'] =>
      z == z' && (ty == .i32 || ty == .i64) && front.all highmulBodyEligible
  | _,_ => false


/-- Match the original returned division; no divisor/value guard is added. -/
def returnedDivAt (stm : Clif.Stmt) (z : Nat) : Bool :=
  match stm.results,stm.inst with
  | [z'],.div _ ty _ _ => z' == z && (ty == .i32 || ty == .i64)
  | _,_ => false

/-- Previously proved scalar statements may occur on both sides of the
returned division. The original final-position classifiers remain intact. -/
def returnedDivBodyEligible : List Clif.Stmt → Nat → Bool
  | [],_ => false
  | stm :: rest,z =>
      (returnedDivAt stm z && rest.all highmulBodyEligible) ||
      (highmulBodyEligible stm && returnedDivBodyEligible rest z)

def returnedDivEligible (b : Clif.Block) : Bool :=
  match b.term with
  | .ret [z] => returnedDivBodyEligible b.body z
  | _ => false


/-- Division syntax is classified independently of its use or return position. -/
def divisionBodyEligible (stm : Clif.Stmt) : Bool :=
  match stm.inst with
  | .div _ ty _ _ => ty == .i32 || ty == .i64
  | _ => false

/-- Any number and ordering of proved scalar operations and divisions. -/
def generalDivBodyEligible (stm : Clif.Stmt) : Bool :=
  highmulBodyEligible stm || divisionBodyEligible stm


def eligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [b] => (b.body.all highmulBodyEligible || singleDivEligible b || mixedDivEligible b || returnedDivEligible b || b.body.all generalDivBodyEligible) &&
      (match b.term with | .ret _ => true | _ => false) &&
      f.sig.params.all abiEligible && f.sig.returns.all abiEligible
  | _ => false

/-- Original narrow integer operations share the existing scalar source family.
The previously shipped per-family selectors above remain unchanged. -/
def narrowBodyEligible (stm : Clif.Stmt) : Bool :=
  match stm.inst with
  | .iconst ty _ | .select ty _ _ _ | .icmp _ ty _ _
  | .extend _ ty _ | .ireduce ty _ | .div _ ty _ _ => ty == .i8 || ty == .i16
  | .unary op ty _ =>
      (op == .bnot || op == .ineg || op == .clz || op == .ctz ||
       op == .bitrev || op == .bswap || op == .popcnt) && (ty == .i8 || ty == .i16)
  | .binary op ty _ _ =>
      (op == .iadd || op == .isub || op == .band || op == .bor || op == .bxor ||
       op == .imul || op == .ishl || op == .ushr || op == .sshr ||
       op == .rotl || op == .rotr || op == .smin || op == .smax ||
       op == .umin || op == .umax || op == .smulhi || op == .umulhi) &&
      (ty == .i8 || ty == .i16)
  | _ => false

def narrowMixedBodyEligible (stm : Clif.Stmt) : Bool :=
  generalDivBodyEligible stm || narrowBodyEligible stm

def narrowAbiEligible (param : Clif.AbiParam) : Bool :=
  param.purpose == .normal &&
    (param.ty == .i8 || param.ty == .i16 || param.ty == .i32 || param.ty == .i64)

def narrowEligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [b] => b.body.all narrowMixedBodyEligible &&
      (match b.term with | .ret _ => true | _ => false) &&
      f.sig.params.all narrowAbiEligible && f.sig.returns.all narrowAbiEligible
  | _ => false

/-- The remaining local pure cases compose with every earlier scalar/division class. -/
def maskBodyEligible (stm : Clif.Stmt) : Bool :=
  match stm.inst with
  | .bmask ty _ => ty == .i8 || ty == .i16 || ty == .i32 || ty == .i64
  | .nop => true
  | _ => false

def maskMixedBodyEligible (stm : Clif.Stmt) : Bool :=
  narrowMixedBodyEligible stm || maskBodyEligible stm

def maskEligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [b] => b.body.all maskMixedBodyEligible &&
      (match b.term with | .ret _ => true | _ => false) &&
      f.sig.params.all narrowAbiEligible && f.sig.returns.all narrowAbiEligible
  | _ => false

def productionEligible (f : Clif.Function) : Bool :=
  (eligible f || narrowEligible f) || maskEligible f

/-- The same bodies when the block ends in `trap` (the trap root, `udf`) instead of `return`. -/
def maskTrapEligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [b] => b.body.all maskMixedBodyEligible &&
      (match b.term with | .trap _ => true | _ => false) &&
      f.sig.params.all narrowAbiEligible && f.sig.returns.all narrowAbiEligible
  | _ => false

/-- Previously shipped selectors remain fixed; narrow syntax and trap terminators add routes. -/
def activationEligible (f : Clif.Function) : Bool :=
  (productionEligible f || maskTrapEligible f) && !Logical.eligible f

def lowerCandidate (f : Clif.Function) : Except String VCode :=
  if !activationEligible f then Logical.lowerCandidate f
  else do
    let result ← Stock.lower f
    if result.edgeArgs.all (fun row => row.all (·.isEmpty)) then pure result.code
    else throw "Stock scalar candidate has nonempty edge arguments"

end Backend.Stock.Scalar
