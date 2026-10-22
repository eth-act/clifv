import FV.Opt.Retype
import FV.Clif

/-!
# Vector data movement at the integer type of the same width (S12e, #36)

`Opt.Retype.vecInt`: the `TyMap` taking each vector type to the integer type of its width
(`i64x2`, `i32x4`, … → `i128`; `i8x8`, `i32x2`, … → `i64`). On a function whose vector values only
move from memory to memory (`okB vecInt f`, the shape of the 9 measured `examples/deps`
functions, `docs/plans/simd.md` §1), `retype vecInt f` has no vector type left in its accesses,
and the `i128` legalisation (`Opt.Legalize128`) splits its 16-byte accesses into `i64` ones.
`retypeParsedFile`: `lean-backend`'s pass before the legalisation — every parsed function in the
domain that mentions a vector access is replaced by its retyping. The refinement:
`Opt.Retype.retype_simX`; end to end: `E2E.backend_correct_retype_legal_wide*`.
-/

namespace Opt.Retype

open Clif

/-- The integer type of a vector's width (`none` for the other types). -/
def vecIntMap : Ty → Option Ty
  | .vec s => if s.width = 128 then some .i128 else some .i64
  | _ => none

/-- **Vectors at the integer type of their width.** -/
def vecInt : TyMap where
  map := vecIntMap
  width t t' h := by
    cases t <;> simp [vecIntMap, VShape.width, VShape.lanes, VShape.laneBits] at h <;> subst h <;>
      rfl

/-- `retype vecInt f` when `f` is in the domain and has a vector access, `f` otherwise. -/
def retypeVec (f : Function) : Function :=
  if okB vecInt f && retype vecInt f != f then retype vecInt f else f

/-- Retype every parsed function (`retypeVec`). -/
def retypeParsedFile (pf : ParsedFile) : ParsedFile :=
  { pf with funcs := pf.funcs.map fun p => match p.func with
    | .ok f => { p with func := .ok (retypeVec f) }
    | .error _ => p }

/-- The names of the functions `retypeParsedFile` changes. -/
def retypedNames (pf : ParsedFile) : List String :=
  pf.funcs.filterMap fun p => match p.func with
    | .ok f => if retypeVec f != f then some p.name else none
    | .error _ => none

end Opt.Retype
