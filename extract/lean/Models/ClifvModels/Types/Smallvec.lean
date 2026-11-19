/-
Handwritten executable models of the `smallvec` 1.15.1 types used by the extracted code.

A `SmallVec<A>` stores its elements inline (up to `A::size()`) or spilled on the heap. Which of the
two is used is observable only through `spilled`, `capacity` and `inline_size`; of those the
extracted code uses only `inline_size`, which is `A::size()` (taken from the `smallvec::Array`
instance at the call). So the model keeps exactly the element sequence. The operations are in
`ClifvModels.Funs.Smallvec`.
-/
module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
universe u v

/-- [smallvec::SmallVec]: the elements, in order. -/
structure smallvec.SmallVec (A : Type u) (Clause0_Item : Type v) : Type v where
  vec : alloc.vec.Vec Clause0_Item

/-- [smallvec::IntoIter]: the elements not yet yielded (`data[current..end]`), in order. -/
structure smallvec.IntoIter (A : Type u) (Clause0_Item : Type v) : Type v where
  items : List Clause0_Item

/-- [smallvec::Drain]: the drained elements not yet yielded, in order. (The drained vector
already has the range removed when `SmallVec::drain` returns: the vector is mutably borrowed for
the lifetime of the `Drain`, and its native `Drop` moves the tail back.) -/
structure smallvec.Drain (T : Type u) (Clause0_Item : Type v) : Type v where
  items : List Clause0_Item
