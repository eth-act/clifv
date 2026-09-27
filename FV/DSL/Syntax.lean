import FV.DSL.Ops

/-!
# Deep syntax: intrinsically typed AST

Contexts are `List Ty` with the most recent binder at the head; variables are typed de Bruijn
indices `Var Γ t`. Ill-typed programs are unrepresentable.

The AST is in A-normal form with respect to effects:

* `Expr Γ t` is **pure and total**: its meaning is a function `Env Γ → t.denote`.
* `Op Γ t` are the **fallible primitives** (checked arithmetic, division, checked vector
  index, map lookup), meaning `Env Γ → M t.denote`. They occur only as `Stmt.op`.
* `Stmt Γ τ` sequences effects; `Stmt.bind s k` runs `s` and binds its value in `k`.

See `docs/contracts/dsl.md` for how an emitter traverses this.
-/

namespace DSL

/-- Typed de Bruijn index: `zero` is the most recent binder. -/
inductive Var : List Ty → Ty → Type
  | zero {t : Ty} {Γ : List Ty} : Var (t :: Γ) t
  | succ {s t : Ty} {Γ : List Ty} : Var Γ t → Var (s :: Γ) t

/-- The numeric de Bruijn index of a variable. -/
def Var.idx : {Γ : List Ty} → {t : Ty} → Var Γ t → Nat
  | _, _, .zero => 0
  | _, _, .succ v => v.idx + 1

instance {Γ : List Ty} {t : Ty} : Repr (Var Γ t) := ⟨fun v _ => "#" ++ repr v.idx⟩

/-- Runtime environment: nested pairs, most recent binder first, ending in `Unit`. -/
@[reducible] def Env : List Ty → Type
  | [] => Unit
  | t :: Γ => t.denote × Env Γ

/-- Function arguments are an environment for the parameter list. -/
abbrev Args (σ : List Ty) : Type := Env σ

def Var.get : {Γ : List Ty} → {t : Ty} → Var Γ t → Env Γ → t.denote
  | _ :: _, _, .zero, env => env.1
  | _ :: _, _, .succ v, env => v.get env.2

def Var.set : {Γ : List Ty} → {t : Ty} → Var Γ t → Env Γ → t.denote → Env Γ
  | _ :: _, _, .zero, env, x => (x, env.2)
  | _ :: _, _, .succ v, env, x => (env.1, v.set env.2 x)

/-- Wrapping integer binary operations (CLIF `iadd isub imul band bor bxor ishl ushr sshr`). -/
inductive IBin
  | add | sub | mul | and | or | xor | shl | lshr | ashr
  deriving DecidableEq, Repr

/-- Integer comparisons (CLIF `icmp eq ne ult ule slt sle`). -/
inductive ICmp
  | eq | ne | ult | ule | slt | sle
  deriving DecidableEq, Repr

/-- Width changes (CLIF `uextend sextend ireduce`). -/
inductive Cast
  | zext | sext | trunc
  deriving DecidableEq, Repr

/-- Fallible integer operations (unsigned). -/
inductive IOp
  /-- checked add, throws `overflow` -/
  | addC
  /-- checked sub, throws `overflow` -/
  | subC
  /-- checked mul, throws `overflow` -/
  | mulC
  /-- unsigned div, throws `divByZero` -/
  | udiv
  /-- unsigned rem, throws `divByZero` -/
  | urem
  deriving DecidableEq, Repr

/-- Pure expressions. -/
inductive Expr : List Ty → Ty → Type
  /-- Read a variable. For linear types (`Ty.linear`) this *moves* the value. -/
  | var {Γ t} : Var Γ t → Expr Γ t
  /-- Explicit copy; never consumes. Semantically equal to `var`. -/
  | clone {Γ t} : Var Γ t → Expr Γ t
  | ilit {Γ} (w : IntW) (v : BitVec w.bits) : Expr Γ (.int w)
  | blit {Γ} (b : Bool) : Expr Γ .bool
  | unit {Γ} : Expr Γ .unit
  | ibin {Γ w} (op : IBin) : Expr Γ (.int w) → Expr Γ (.int w) → Expr Γ (.int w)
  | inot {Γ w} : Expr Γ (.int w) → Expr Γ (.int w)
  | icmp {Γ w} (op : ICmp) : Expr Γ (.int w) → Expr Γ (.int w) → Expr Γ .bool
  | cast {Γ w} (op : Cast) (w' : IntW) : Expr Γ (.int w) → Expr Γ (.int w')
  | band {Γ} : Expr Γ .bool → Expr Γ .bool → Expr Γ .bool
  | bor {Γ} : Expr Γ .bool → Expr Γ .bool → Expr Γ .bool
  | bnot {Γ} : Expr Γ .bool → Expr Γ .bool
  /-- Pure conditional (both arms pure, so evaluation order is irrelevant). -/
  | cond {Γ t} : Expr Γ .bool → Expr Γ t → Expr Γ t → Expr Γ t
  | pair {Γ a b} : Expr Γ a → Expr Γ b → Expr Γ (.prod a b)
  | fst {Γ a b} : Expr Γ (.prod a b) → Expr Γ a
  | snd {Γ a b} : Expr Γ (.prod a b) → Expr Γ b
  /-- `Vector.replicate n x`. -/
  | vrepl {Γ t} (n : Nat) : Expr Γ t → Expr Γ (.vec n t)
  | mapEmpty {Γ k v} : Expr Γ (.map k v)
  /-- Non-consuming read of a map variable. -/
  | mapContains {Γ k v} : Var Γ (.map k v) → Expr Γ k → Expr Γ .bool

/-- Argument lists: `Exprs Γ σ` gives one expression per parameter type in `σ`. -/
inductive Exprs : List Ty → List Ty → Type
  | nil {Γ} : Exprs Γ []
  | cons {Γ t σ} : Expr Γ t → Exprs Γ σ → Exprs Γ (t :: σ)

/-- Fallible primitives. Vector/map operands are variables (read, not consumed). -/
inductive Op : List Ty → Ty → Type
  | iop {Γ w} (op : IOp) : Expr Γ (.int w) → Expr Γ (.int w) → Op Γ (.int w)
  /-- Checked index (index of any width); throws `indexOutOfBounds`. -/
  | vget {Γ n t w} : Var Γ (.vec n t) → Expr Γ (.int w) → Op Γ t
  /-- Map lookup; throws `notFound`. -/
  | mapGet {Γ k v} : Var Γ (.map k v) → Expr Γ k → Op Γ v

/-- Statements. `τ` is the type of the value the statement produces. -/
inductive Stmt : List Ty → Ty → Type
  | ret {Γ τ} : Expr Γ τ → Stmt Γ τ
  | throw {Γ τ} : Err → Stmt Γ τ
  | op {Γ τ} : Op Γ τ → Stmt Γ τ
  /-- Call of another `flat def`, whose name and body are embedded (no recursion possible). -/
  | call {Γ σ τ} (name : String) (body : Stmt σ τ) (args : Exprs Γ σ) : Stmt Γ τ
  /-- Pure `let`. -/
  | let_ {Γ α τ} : Expr Γ α → Stmt (α :: Γ) τ → Stmt Γ τ
  /-- Destructuring `let (x, y) := e; k`: `y` is `#0`, `x` is `#1` in `k`. -/
  | letPair {Γ a b τ} : Expr Γ (.prod a b) → Stmt (b :: a :: Γ) τ → Stmt Γ τ
  /-- Effectful `let x ← s; k`. Also the join point after a non-tail `if` or a loop. -/
  | bind {Γ α τ} : Stmt Γ α → Stmt (α :: Γ) τ → Stmt Γ τ
  /-- Reassign variable `v` (the old value is dead afterwards). -/
  | set {Γ α τ} (v : Var Γ α) : Expr Γ α → Stmt Γ τ → Stmt Γ τ
  /-- Checked in-place element update of vector variable `v`; throws `indexOutOfBounds`. -/
  | vset {Γ n α w τ} (v : Var Γ (.vec n α)) : Expr Γ (.int w) → Expr Γ α → Stmt Γ τ → Stmt Γ τ
  /-- In-place insert into map variable `v`. -/
  | mapInsert {Γ k val τ} (v : Var Γ (.map k val)) : Expr Γ k → Expr Γ val → Stmt Γ τ → Stmt Γ τ
  | ite {Γ τ} : Expr Γ .bool → Stmt Γ τ → Stmt Γ τ → Stmt Γ τ
  /-- `for i in [0:n]` fold: the body sees the accumulator (`#0`) and `i : u64` (`#1`) and
  returns the next accumulator; the statement's value is the final accumulator. -/
  | forRange {Γ α} (n : Nat) : Expr Γ α → Stmt (α :: .u64 :: Γ) α → Stmt Γ α

/-- A DSL function: parameters `σ` (first parameter = `#0` at entry), result `τ`. -/
structure FlatFn (σ : List Ty) (τ : Ty) where
  name : String
  body : Stmt σ τ

end DSL
