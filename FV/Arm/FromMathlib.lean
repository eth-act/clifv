/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- Modified by fv-compiler-rust (2026): ported to Lean v4.34.1, module prefix FV.Arm, wrapped in namespace Arm.

namespace Arm

-- This file has definitions temporarily lifted from Mathlib.
-- We will move them into Lean shortly.

namespace Nat

/-- Induction principle starting at a non-zero number. For maps to a `Sort*` see `leRecOn`.
To use in an induction proof, the syntax is `induction n, hn using Nat.le_induction` (or the same
for `induction'`). -/
@[elab_as_elim]
theorem le_induction {m : Nat} {P : ∀ n, m ≤ n → Prop} (base : P m m.le_refl)
    (succ : ∀ n hmn, P n hmn → P (n + 1) (_root_.Nat.le_succ_of_le hmn)) :
    ∀ n hmn, P n hmn := fun n hmn ↦ by
  apply _root_.Nat.le.rec
  · exact base
  · intros n hn
    apply succ n hn

end Nat

end Arm
