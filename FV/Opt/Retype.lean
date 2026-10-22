import FV.Opt.Basic

/-!
# `Opt.Retype`: data-movement loads and stores at another type of the same width (S12e, #36)

`retype σ f`: `f` with every plain `load`/`store` at a type `t` that `σ` maps (`σ.map t = some
t'`, a type of the same width) accessing memory at `t'` instead. The values those loads define
(`vals σ f`) then carry `t'` instead of `t`, with the same bits (`retag`). S12 retypes the
128-bit vector accesses at `i128` (`Opt.Retype.vec128`), so that the `i128` legalisation
(`Opt.Legalize128`) splits each into two `i64` accesses: the vector code cg_clif emits around
its inline-asm shims only moves vectors between memory locations (`docs/plans/simd.md` §1).

`okB σ f`: the domain on which `retype σ f` refines `f` (`Opt.Retype.retype_simX`,
`FV/Opt/Proof/RetypeSim.lean`): each retyped load defines exactly one value, those values are
read only as the stored value of retyped stores, and no other statement or block parameter
defines them. Kept free of proofs so that the driver can evaluate it.
-/

namespace Opt.Retype

open Clif

/-- A retyping of memory accesses: the types `map` changes, each to a type of the same width. -/
structure TyMap where
  map : Ty → Option Ty
  width : ∀ t t', map t = some t' → t'.width = t.width

variable (σ : TyMap)

/-- A plain `load`/`store` at a type `σ` maps accesses memory at its image. -/
def retypeInst : Inst → Inst
  | .load .load t fl p off => .load .load ((σ.map t).getD t) fl p off
  | .store .store t fl x p off => .store .store ((σ.map t).getD t) fl x p off
  | i => i

def retypeStmt (st : Stmt) : Stmt := { st with inst := retypeInst σ st.inst }

def retypeBlock (b : Block) : Block := { b with body := b.body.map (retypeStmt σ) }

/-- **The retyped function.** -/
def retype (f : Function) : Function := { f with blocks := f.blocks.map (retypeBlock σ) }

/-- A plain `load` at a type `σ` maps. -/
def isRLoad : Inst → Bool
  | .load .load t _ _ _ => (σ.map t).isSome
  | _ => false

/-- A plain `store` at a type `σ` maps. -/
def isRStore : Inst → Bool
  | .store .store t _ _ _ _ => (σ.map t).isSome
  | _ => false

/-- The values the retyped loads of `f` define. -/
def vals (f : Function) : List ValueId :=
  f.blocks.flatMap fun b => b.body.flatMap fun st => if isRLoad σ st.inst then st.results else []

/-- The stored value of a `store` (`none` for another instruction). -/
def storedVal : Inst → Option ValueId
  | .store _ _ _ x _ _ => some x
  | _ => none

/-- A statement reads and defines the values `V` only as the domain allows: a retyped load
defines one value and reads none of `V`; a retyped store reads one of `V` as its stored value
only; any other statement neither reads nor defines one. -/
def stmtOkB (V : List ValueId) (st : Stmt) : Bool :=
  if isRLoad σ st.inst then
    st.results.length == 1 && (operands st.inst).all (!V.contains ·)
  else if isRStore σ st.inst then
    match st.inst with
    | .store _ _ _ x p _ => V.contains x && !V.contains p && st.results.isEmpty
    | _ => false
  else (operands st.inst).all (!V.contains ·) && st.results.all (!V.contains ·)

/-- **The domain of the retyping** (module doc). -/
def okB (f : Function) : Bool :=
  let V := vals σ f
  f.blocks.all fun b => b.params.all (fun p => !V.contains p.1) && b.body.all (stmtOkB σ V) &&
    (termOperands b.term).all (!V.contains ·)

/-- A value retyped by `σ`: the same bits at the image of its type. -/
def retag (x : Val) : Val :=
  match h : σ.map x.ty with
  | some t' => ⟨t', x.bits.cast (σ.width _ _ h).symm⟩
  | none => x

end Opt.Retype
