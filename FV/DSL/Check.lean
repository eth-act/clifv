import FV.DSL.Denote

/-!
# Fragment checker and the affine rule

`FlatFn.check f : Except String Unit` explains rejections; `FlatFn.checkB` is its `Bool`
shadow and `FlatFn.checked f : Prop := f.checkB = true` is what the compiler theorems assume.

## The affine rule

Variables of *linear* type (`Ty.linear`: containing a vector or a map) are memory-backed and
updated in place. Per variable the checker tracks `dead` (moved out) and `mut` (updated since
the enclosing `bind` started):

* A *move* is an occurrence `Expr.var v` with `v` linear: it kills `v`.
  `Expr.clone v`, `Op.vget v`, `Op.mapGet v`, `Expr.mapContains v` read without moving.
* Every occurrence of `v` (move, clone, read, or in-place update target) requires `v` alive.
* `Stmt.set v e` may target a dead `v` (it revives it); `vset`/`mapInsert` need `v` alive.
* `Stmt.bind s k`: a linear variable of the enclosing context that `s` updates (via `set`,
  `vset`, `mapInsert`) is dead in `k` (semantically `k` sees the *old* value, which was
  overwritten in place).
* `Stmt.ite`: after the conditional, a variable is dead if it is dead after either branch.
* `Stmt.forRange` body: may not move or update any linear variable bound *outside* the body
  (each iteration starts from the same outer environment).

Invariant the emitter may assume for a `checked` function: at every read or in-place update
of a linear variable `v`, `v` is alive and no other live variable or in-flight value shares
`v`'s storage, so a move may transfer the pointer and `vset`/`mapInsert` may write in place.

## Fragment rules (`Ty.wf` and per-construct)

* map keys and values are `int`/`bool`; maps do not occur inside vectors;
  vector lengths are `> 0`;
* `zext`/`sext` widen or keep the width, `trunc` narrows or keeps it;
* `forRange n` has `n < 2^64`;
* the callee body of every `Stmt.call` is itself checked.
-/

namespace DSL

namespace Ty

def hasMap : Ty → Bool
  | .map _ _ => true
  | .vec _ t => t.hasMap
  | .prod a b => a.hasMap || b.hasMap
  | _ => false

/-- Map keys and values: integers and booleans (passed as zero-extended `i64` to externs). -/
def isKey : Ty → Bool
  | .int _ | .bool => true
  | _ => false

def wf : Ty → Bool
  | .int _ | .bool | .unit => true
  | .vec n t => 0 < n && !t.hasMap && t.wf
  | .prod a b => a.wf && b.wf
  | .map k v => k.isKey && v.isKey

end Ty

/-- Per-variable checker state `(dead, mut)`, head = `#0`. -/
abbrev CheckSt := List (Bool × Bool)

namespace Check

/-- `lim = some l`: variables with index `≥ l` are outside the innermost loop body. -/
def frozen (lim : Option Nat) (i : Nat) : Bool :=
  match lim with
  | some l => l ≤ i
  | none => false

def isDead (st : CheckSt) (i : Nat) : Bool := (st.getD i (false, false)).1

def alive (st : CheckSt) (i : Nat) (what : String) : Except String Unit :=
  if isDead st i then .error s!"affine rule: {what} of variable #{i} after it was moved (use `.clone` before the move)"
  else .ok ()

/-- An occurrence of variable `i`; `move` and `lin` decide whether it consumes. -/
def use (lin move : Bool) (lim : Option Nat) (i : Nat) (st : CheckSt) : Except String CheckSt := do
  alive st i (if move then "use" else "read")
  if move && lin then
    if frozen lim i then
      .error s!"affine rule: loop body moves variable #{i} bound outside the loop"
    else .ok (st.set i (true, (st.getD i (false, false)).2))
  else .ok st

/-- In-place update or reassignment of variable `i`. -/
def update (lin : Bool) (lim : Option Nat) (i : Nat) (st : CheckSt) : Except String CheckSt :=
  if lin then
    if frozen lim i then
      .error s!"affine rule: loop body updates variable #{i} bound outside the loop"
    else .ok (st.set i (false, true))
  else .ok st

def castOk (op : Cast) (w w' : IntW) : Bool :=
  match op with
  | .zext | .sext => w.bits ≤ w'.bits
  | .trunc => w'.bits ≤ w.bits

def need (b : Bool) (msg : String) : Except String Unit :=
  if b then .ok () else .error msg

/-- Pointwise join after a conditional: dead or updated in either branch. -/
def join : CheckSt → CheckSt → CheckSt
  | (d₁, m₁) :: t₁, (d₂, m₂) :: t₂ => (d₁ || d₂, m₁ || m₂) :: join t₁ t₂
  | _, _ => []

/-- Entering `k` of `bind s k`: variables `s` updated are dead in `k`. -/
def killUpdated (st : CheckSt) : CheckSt := st.map fun (d, m) => (d || m, m)

/-- Start of `s` in `bind s k`: forget earlier updates. -/
def clearMut (st : CheckSt) : CheckSt := st.map fun (d, _) => (d, false)

/-- After `bind s k`: dead flags from `new`, update flags from both. -/
def restoreMut : CheckSt → CheckSt → CheckSt
  | (_, m₁) :: t₁, (d₂, m₂) :: t₂ => (d₂, m₁ || m₂) :: restoreMut t₁ t₂
  | _, _ => []

end Check

open Check

def Expr.chk {Γ : List Ty} : {t : Ty} → Expr Γ t → Option Nat → CheckSt → Except String CheckSt
  | t, .var v, lim, st => use t.linear true lim v.idx st
  | t, .clone v, lim, st => use t.linear false lim v.idx st
  | _, .ilit _ _, _, st => .ok st
  | _, .blit _, _, st => .ok st
  | _, .unit, _, st => .ok st
  | _, .ibin _ a b, lim, st => do let st ← a.chk lim st; b.chk lim st
  | _, .inot a, lim, st => a.chk lim st
  | _, .icmp _ a b, lim, st => do let st ← a.chk lim st; b.chk lim st
  | _, @Expr.cast _ w op w' a, lim, st => do
    need (castOk op w w') s!"cast {repr op} from {w.bits} to {w'.bits} bits changes width the wrong way"
    a.chk lim st
  | _, .band a b, lim, st => do let st ← a.chk lim st; b.chk lim st
  | _, .bor a b, lim, st => do let st ← a.chk lim st; b.chk lim st
  | _, .bnot a, lim, st => a.chk lim st
  | _, .cond c a b, lim, st => do
    let st ← c.chk lim st
    let st₁ ← a.chk lim st
    let st₂ ← b.chk lim st
    pure (join st₁ st₂)
  | _, .pair a b, lim, st => do let st ← a.chk lim st; b.chk lim st
  | _, .fst p, lim, st => p.chk lim st
  | _, .snd p, lim, st => p.chk lim st
  | _, .vrepl _ x, lim, st => x.chk lim st
  | _, .mapEmpty, _, st => .ok st
  | _, .mapContains m k, lim, st => do
    let st ← use true false lim m.idx st
    k.chk lim st

def Exprs.chk {Γ : List Ty} : {σ : List Ty} → Exprs Γ σ → Option Nat → CheckSt → Except String CheckSt
  | _, .nil, _, st => .ok st
  | _, .cons e es, lim, st => do let st ← e.chk lim st; es.chk lim st

def Op.chk {Γ : List Ty} {t : Ty} : Op Γ t → Option Nat → CheckSt → Except String CheckSt
  | .iop _ a b, lim, st => do let st ← a.chk lim st; b.chk lim st
  | .vget v i, lim, st => do let st ← use true false lim v.idx st; i.chk lim st
  | .mapGet m k, lim, st => do let st ← use true false lim m.idx st; k.chk lim st

def wfTy (t : Ty) : Except String Unit :=
  need t.wf s!"type {repr t} is outside the DSL fragment (map keys/values must be int or bool, no maps in vectors, vector length > 0)"

def wfTys (σ : List Ty) : Except String Unit :=
  need (σ.all Ty.wf) s!"parameter types {repr σ} are outside the DSL fragment"

def Stmt.chk : {Γ : List Ty} → {τ : Ty} → Stmt Γ τ → Option Nat → CheckSt → Except String CheckSt
  | _, _, .ret e, lim, st => e.chk lim st
  | _, _, .throw _, _, st => .ok st
  | _, _, .op o, lim, st => o.chk lim st
  | _, _, @Stmt.call _ σ τ name body args, lim, st => do
    wfTys σ
    wfTy τ
    match body.chk none (σ.map fun _ => (false, false)) with
    | .ok _ => pure ()
    | .error msg => .error s!"in callee {name}: {msg}"
    args.chk lim st
  | _, _, @Stmt.let_ _ α _ e k, lim, st => do
    wfTy α
    let st ← e.chk lim st
    let st ← k.chk (lim.map (· + 1)) ((false, false) :: st)
    pure st.tail
  | _, _, @Stmt.letPair _ a b _ e k, lim, st => do
    wfTy a; wfTy b
    let st ← e.chk lim st
    let st ← k.chk (lim.map (· + 2)) ((false, false) :: (false, false) :: st)
    pure st.tail.tail
  | _, _, @Stmt.bind _ α _ s k, lim, st => do
    wfTy α
    let st₁ ← s.chk lim (clearMut st)
    let st₂ ← k.chk (lim.map (· + 1)) ((false, false) :: killUpdated st₁)
    pure (restoreMut st st₂.tail)
  | _, _, @Stmt.set _ α _ v e k, lim, st => do
    let st ← e.chk lim st
    let st ← update α.linear lim v.idx st
    k.chk lim st
  | _, _, .vset v i e k, lim, st => do
    let st ← use true false lim v.idx st
    let st ← i.chk lim st
    let st ← e.chk lim st
    let st ← update true lim v.idx st
    k.chk lim st
  | _, _, .mapInsert v key val k, lim, st => do
    let st ← use true false lim v.idx st
    let st ← key.chk lim st
    let st ← val.chk lim st
    let st ← update true lim v.idx st
    k.chk lim st
  | _, _, .ite c t e, lim, st => do
    let st ← c.chk lim st
    let st₁ ← t.chk lim st
    let st₂ ← e.chk lim st
    pure (join st₁ st₂)
  | _, _, @Stmt.forRange _ α n init body, lim, st => do
    wfTy α
    need (n < 2 ^ 64) s!"loop bound {n} does not fit in u64"
    let st ← init.chk lim st
    let _ ← body.chk (some 2) ((false, false) :: (false, false) :: st)
    pure st

/-- Check a function, with an explanation on rejection. -/
def FlatFn.check {σ : List Ty} {τ : Ty} (f : FlatFn σ τ) : Except String Unit := do
  wfTys σ
  wfTy τ
  match f.body.chk none (σ.map fun _ => (false, false)) with
  | .ok _ => pure ()
  | .error msg => .error s!"{f.name}: {msg}"

def FlatFn.checkB {σ : List Ty} {τ : Ty} (f : FlatFn σ τ) : Bool :=
  match f.check with
  | .ok _ => true
  | .error _ => false

/-- The fragment and affine rules hold. Assumed by the compiler theorems. -/
def FlatFn.checked {σ : List Ty} {τ : Ty} (f : FlatFn σ τ) : Prop := f.checkB = true

instance {σ : List Ty} {τ : Ty} (f : FlatFn σ τ) : Decidable f.checked :=
  inferInstanceAs (Decidable (f.checkB = true))

end DSL
