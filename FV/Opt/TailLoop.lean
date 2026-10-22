import FV.Clif.Run

/-! # Self tail calls as loops (S8, #32)

`Opt.TailLoop.loop f`: a function's `return_call` of itself (`return_call fnN(args)` whose
declaration `fnN` is the function's own name, with its parameter and return types) becomes a
jump back to the function's first block, so the frame is reused and the stack does not grow per
tail call. The first block `b0` stops being the entry: a new entry block (a fresh id, fresh
parameters `q` of `b0`'s types) jumps to `b0(q)`, and every self `return_call fnN(args)` becomes
`jump b0(args)`.

`Clif.run`'s self `return_call` frees the frame's slots, leaves the activation and enters the
function again (fresh registers, fresh slots); the jump keeps the registers (a superset of the
fresh ones) and the slots. The transform applies only where the two agree on memory and on
every later step (`eligB`): no stack slots (the frame's slots are the empty list either way), no
`try_call`/`try_call_indirect` (whose result values sit at `Function.freshValue`, which the
new block's parameters raise), the first block's parameter types are the signature's parameter
types, and at least one self `return_call`. Otherwise `loop f = f`. The refinement theorem is
`Opt.TailLoop.TailRel.refines` (`FV/Opt/Proof/TailLoopSim.lean`).
-/

namespace Opt.TailLoop

open Clif

/-- `fnN` declares the function itself, with its parameter and return types. -/
def selfTail (f : Function) (fn : FnRef) : Bool :=
  match f.extern? fn with
  | some ext => ext.name == f.name && AbiParam.tys ext.sig.params == AbiParam.tys f.sig.params &&
      AbiParam.tys ext.sig.returns == AbiParam.tys f.sig.returns
  | none => false

/-- A self `return_call` becomes `jump b0(args)`. -/
def termT (f : Function) (b0 : BlockId) : Terminator → Terminator
  | .returnCall fn args => if selfTail f fn then .jump ⟨b0, args⟩ else .returnCall fn args
  | t => t

/-- The block with its self `return_call` replaced. -/
def blockT (f : Function) (b0 : BlockId) (b : Block) : Block := { b with term := termT f b0 b.term }

/-- A block id above every block id of `f`. -/
def newId (f : Function) : BlockId := f.blocks.foldl (fun m b => max m (b.id + 1)) 0

/-- The terminator is a self `return_call`. -/
def isSelfTail (f : Function) : Terminator → Bool
  | .returnCall fn _ => selfTail f fn
  | _ => false

/-- The transform applies (module doc). -/
def eligB (f : Function) : Bool :=
  f.slots.isEmpty && f.blocks.all (fun b => !b.term.isTry) &&
    f.blocks.any (fun b => isSelfTail f b.term) &&
    match f.blocks with
    | b0 :: _ => b0.params.map (·.2) == AbiParam.tys f.sig.params
    | [] => false

/-- Parameters `base`, `base + 1`, … with the types of `ps`. -/
def freshParams (base : ValueId) : List (ValueId × Ty) → List (ValueId × Ty)
  | [] => []
  | (_, t) :: ps => (base, t) :: freshParams (base + 1) ps

/-- The new entry block of `f` with first block `b0`: parameters `freshValue f + i` of `b0`'s
types, jumping to `b0` with them. -/
def entryBlock (f : Function) (b0 : Block) : Block :=
  let qs := freshParams f.freshValue b0.params
  { id := newId f, params := qs, body := [], term := .jump ⟨b0.id, qs.map (·.1)⟩ }

/-- **Self tail calls as loops** (module doc). -/
def loop (f : Function) : Function :=
  match f.blocks with
  | [] => f
  | b0 :: _ =>
    if eligB f then { f with blocks := entryBlock f b0 :: f.blocks.map (blockT f b0.id) } else f

end Opt.TailLoop
