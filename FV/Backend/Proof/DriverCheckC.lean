module

public import FV.Backend.Proof.DriverCheckTy

public section

/-!
# The typed lowering validator with typed `try_call`s (S11e6, #419)

Since S11e6 slice 2b `lowerFunction` lowers a `try_call`/`try_call_indirect` with the typed
helpers (`tryCallDataC`, `exnTableOpndC`, `tryRegsOfC`): a direct `try_call`'s callee may take
and return `f32`/`f64`, its return vregs have the returns' classes. The recorded lowering
`lowTerm` (`DriverCheck.lean`) uses the integer helpers, so `lowerCheck`/`lowerCheckT` reject
such a function. This file is the recorded lowering with the typed helpers, beside the integer
one:

* `lowTermC`, `lowBlocksC`: `lowTerm`/`lowBlocks` with `tryCallDataC`, `exnTableOpndC`,
  `tryRegsOfC` (exactly `lowerFunction`'s calls);
* `lowerCheckTC`: `lowerCheckT` over `lowBlocksC`.

On integer signatures the typed helpers are the integer ones (`TryRegsC.lean`). Executable
only (the compiler runs `lowerCheckTC`, `Backend.lowerCheckFor`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- **The lowering of a terminator, typed `try_call`s** (`lowTerm` with `lowerFunction`'s typed
helpers `tryCallDataC`, `exnTableOpndC`, `tryRegsOfC`). -/
def lowTermC (f : Clif.Function) (tcall : TermCallF) (ycall : TryCallF) (ti : Nat)
    (t : Clif.Terminator) (tst : LState) (nl : Nat) :
    Option (V × List Label × Option TryLow × LState × Nat) :=
  match t with
  | .tryCall _ _ et | .tryCallIndirect _ _ et =>
    match tryCallDataC f t, exnTableOpndC f et, tryTargets f et.dests nl with
    | .ok data, .ok (sig, items), some (targets, nl') =>
      match tryRegsOfC sig tst with
      | some (trs, st1) =>
        match tryInfoOf sig items targets with
        | some info =>
          match ycall ti data trs targets { st1 with emitted := #[] } with
          | .ok (some _, tst', _) => some (data, targets, some ⟨info, sig, items, trs, st1⟩, tst', nl')
          | _ => none
        | none => none
      | none => none
    | _, _, _ => none
  | t =>
    match termData (abiTerm f t), targetsOf f t nl with
    | .ok data, some (targets, nl') =>
      match tcall ti data t targets tst with
      | .ok (some _, tst', _) => some (data, targets, none, tst', nl')
      | _ => none
    | _, _ => none

/-- The lowering of the blocks `Bs` with typed `try_call`s (`lowBlocks` over `lowTermC`). -/
def lowBlocksC (f : Clif.Function) (call : StmtCall) (tcall : TermCallF) (ycall : TryCallF) :
    Nat → List Clif.Block → LState → Nat → Option (List BLow)
  | _, [], _, _ => some []
  | start, B :: Bs, st, nl =>
    match lowStmts call start B.body st with
    | none => none
    | some (sls, stE) =>
      let ti := start + B.body.length
      let tst : LState := { stE with emitted := #[] }
      match lowTermC f tcall ycall ti B.term tst nl with
      | some (data, targets, tl, tst', nl') =>
        (lowBlocksC f call tcall ycall (ti + 1) Bs { tst' with emitted := #[] } nl').map
          (⟨start, sls, data, targets, tst, tst', tl⟩ :: ·)
      | none => none

/-- **The typed lowering validator with typed `try_call`s** (`lowerCheckT` over `lowBlocksC`). -/
def lowerCheckTC (f : Clif.Function) (vc : VCode) : Bool :=
  match buildCtx f with
  | .error _ => false
  | .ok (ctx, _, st0) =>
    match lowBlocksC f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length with
    | none => false
    | some bl =>
      let gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))
      shapeOkT f vc ctx st0 gn bl && certOk f ctx st0 gn bl (inFix f ctx gn) && brIdxOk f ctx &&
        ((f.blocks.any (·.term.isTry) || !vc.hasTryCall) && (hasTls f || !vc.hasTls)) &&
        (callsStackOkB f vc.outgoing && entryOkBT f)

end Backend.Proof.Driver
