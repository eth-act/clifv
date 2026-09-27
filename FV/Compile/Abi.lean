import FV.DSL.Check
import FV.Clif

/-!
# Data layout and function ABI of compiled DSL functions

See `docs/contracts/compile.md` §1–§2. Every DSL value is flattened into a list of scalar CLIF
values (`flat`); vectors and products never live in memory. Maps are `i64` handles to runtime
objects. A compiled function returns `i8 tag` followed by the flattened payload, or, when that
would exceed the eight AArch64 return registers, stores the payload into a caller-provided
buffer (`FnAbi.sret`).
-/

namespace Compile

open DSL (Ty IntW)

/-- CLIF type of a DSL machine integer. -/
def intTy : IntW → Clif.Ty
  | .w8 => .i8
  | .w16 => .i16
  | .w32 => .i32
  | .w64 => .i64

@[simp] theorem intTy_width (w : IntW) : (intTy w).width = w.bits := by cases w <;> rfl

/-- The flattened CLIF representation of a DSL type. -/
def flat : Ty → List Clif.Ty
  | .int w => [intTy w]
  | .bool => [.i8]
  | .unit => []
  | .vec n t => (List.replicate n (flat t)).flatten
  | .prod a b => flat a ++ flat b
  | .map _ _ => [.i64]

/-- Flattened parameter list. -/
def flatList : List Ty → List Clif.Ty
  | [] => []
  | t :: ts => flat t ++ flatList ts

/-- Integer return registers of the target (AArch64 x0–x7): at most this many return values
(tag included) are returned in registers. -/
def maxRegReturns : Nat := 8

/-! ## Which functions need the runtime context -/

/-- Does evaluating the expression call the map runtime? -/
def Expr.usesCtx {Γ : List Ty} : {t : Ty} → DSL.Expr Γ t → Bool
  | t, .clone _ => t.hasMap
  | _, .var _ | _, .ilit _ _ | _, .blit _ | _, .unit => false
  | _, .ibin _ a b | _, .icmp _ a b => Expr.usesCtx a || Expr.usesCtx b
  | _, .band a b | _, .bor a b | _, .pair a b => Expr.usesCtx a || Expr.usesCtx b
  | _, .inot a | _, .cast _ _ a | _, .bnot a | _, .fst a | _, .snd a | _, .vrepl _ a =>
    Expr.usesCtx a
  | _, .cond c a b => Expr.usesCtx c || Expr.usesCtx a || Expr.usesCtx b
  | _, .mapEmpty | _, .mapContains _ _ => true

def Exprs.usesCtx {Γ : List Ty} : {σ : List Ty} → DSL.Exprs Γ σ → Bool
  | _, .nil => false
  | _, .cons e es => Expr.usesCtx e || Exprs.usesCtx es

def Op.usesCtx {Γ : List Ty} {t : Ty} : DSL.Op Γ t → Bool
  | .iop _ a b => Expr.usesCtx a || Expr.usesCtx b
  | .vget _ i => Expr.usesCtx i
  | .mapGet _ _ => true

/-- Does executing the statement call the map runtime (directly or in a callee)? A compiled
function takes the runtime context parameter iff its body `usesCtx`. -/
def Stmt.usesCtx : {Γ : List Ty} → {τ : Ty} → DSL.Stmt Γ τ → Bool
  | _, _, .ret e => Expr.usesCtx e
  | _, _, .throw _ => false
  | _, _, .op o => Op.usesCtx o
  | _, _, .call _ body args => Stmt.usesCtx body || Exprs.usesCtx args
  | _, _, .let_ e k | _, _, .letPair e k => Expr.usesCtx e || Stmt.usesCtx k
  | _, _, .bind s k => Stmt.usesCtx s || Stmt.usesCtx k
  | _, _, .set _ e k => Expr.usesCtx e || Stmt.usesCtx k
  | _, _, .vset _ i e k => Expr.usesCtx i || Expr.usesCtx e || Stmt.usesCtx k
  | _, _, .mapInsert _ _ _ _ => true
  | _, _, .ite c t e => Expr.usesCtx c || Stmt.usesCtx t || Stmt.usesCtx e
  | _, _, .forRange _ init body => Expr.usesCtx init || Stmt.usesCtx body

/-! ## Function ABI -/

/-- The ABI of a compiled function with parameters `params` and result `result`. -/
structure FnAbi where
  /-- Takes the runtime context (first parameter). -/
  ctx : Bool
  params : List Ty
  result : Ty
  deriving Repr

namespace FnAbi

/-- Payload returned through a caller buffer (tag plus payload exceed the return registers). -/
def sret (a : FnAbi) : Bool := decide (maxRegReturns < 1 + (flat a.result).length)

/-- Byte size of the result buffer (8 bytes per flat value) in buffer mode. -/
def bufSize (a : FnAbi) : Nat := 8 * (flat a.result).length

def paramTys (a : FnAbi) : List Clif.Ty :=
  (if a.ctx then [.i64] else []) ++ (if a.sret then [.i64] else []) ++ flatList a.params

def retTys (a : FnAbi) : List Clif.Ty :=
  .i8 :: (if a.sret then [] else flat a.result)

def signature (a : FnAbi) : Clif.Signature :=
  { params := a.paramTys.map fun t => { ty := t }
    returns := a.retTys.map fun t => { ty := t } }

end FnAbi

/-- ABI of a function body. -/
def bodyAbi {σ : List Ty} {τ : Ty} (body : DSL.Stmt σ τ) : FnAbi :=
  { ctx := Stmt.usesCtx body, params := σ, result := τ }

def fnAbi {σ : List Ty} {τ : Ty} (f : DSL.FlatFn σ τ) : FnAbi := bodyAbi f.body

/-! ## Symbol names -/

def hexString (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def mangleChar (c : Char) : String :=
  if c.isAlphanum then c.toString
  else if c = '.' then "__"
  else if c = '_' then "_1"
  else "_x" ++ hexString c.toNat ++ "_"

/-- Injective mapping of Lean declaration names to CLIF names (`[A-Za-z0-9_]*`). -/
def mangle (s : String) : String := String.join (s.toList.map mangleChar)

/-! ## Map keys and values as `i64` words -/

/-- Keys and values are passed to the runtime zero-extended to 64 bits. -/
def toWord : (t : Ty) → t.denote → BitVec 64
  | .int _, x => x.setWidth 64
  | .bool, b => if b then 1#64 else 0#64
  | _, _ => 0#64

/-- Inverse of `toWord` on canonical words. -/
def ofWord? : (t : Ty) → BitVec 64 → Option t.denote
  | .int w, x => if x.toNat < 2 ^ w.bits then some (x.setWidth w.bits) else none
  | .bool, x => if x = 0#64 then some false else if x = 1#64 then some true else none
  | _, _ => none

end Compile
