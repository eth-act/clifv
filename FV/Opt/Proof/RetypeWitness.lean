module

public import FV.Opt.Proof.RetypeSim

@[expose] public section

/-!
# Non-vacuity of the retyping's refinement (S12e, #36)

`f64AsI64`: the `TyMap` taking `f64` accesses to `i64` (the same width). `copyF` loads an `f64`
from its pointer argument and stores it 8 bytes further: in the domain (`copyF_ok`), changed by
the retyping (`copyF_changed`), so `Opt.Retype.retype_simX` relates two different functions
(`copyF_sim`). The S12 instance (128-bit vectors at `i128`) is witnessed with the vector types
(`Opt.Retype.vec128`).
-/

namespace Opt.Retype.Witness

open Clif

/-- `f64` accesses at `i64`. -/
def f64AsI64 : TyMap where
  map
    | .f64 => some .i64
    | _ => none
  width t t' h := by cases t <;> simp at h <;> subst h <;> rfl

/-- `v1 = load.f64 v0; store v1, v0+8; return`. -/
def copyF : Function where
  name := "copy"
  sig := { params := [{ ty := .i64 }] }
  blocks := [{
    id := 0
    params := [(0, .i64)]
    body := [⟨[1], .load .load .f64 default 0 0⟩, ⟨[], .store .store .f64 default 1 0 8⟩]
    term := .ret [] }]

theorem copyF_ok : okB f64AsI64 copyF = true := by decide +kernel

theorem copyF_changed : retype f64AsI64 copyF ≠ copyF := by decide +kernel

/-- **`retype_simX` relates two different functions.** -/
theorem copyF_sim : FunSimX copyF (retype f64AsI64 copyF) := retype_simX copyF copyF_ok

end Opt.Retype.Witness
