/-
Handwritten executable models of the `allocator-api2` 0.2.20 types used by the extracted code
(`allocator_api2::stable::vec`, a copy of `alloc::vec` parameterized by an allocator).

Memory is not modeled (as for the Aeneas `alloc.vec.Vec` model): a vector is its element sequence
plus its allocator value. The operations are in `ClifvModels.Funs.AllocatorApi2`.
-/
module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
universe u v

/-- [allocator_api2::stable::vec::Vec]: the elements, in order, and the allocator. -/
structure allocator_api2.stable.vec.Vec (T : Type u) (A : Type v) : Type (max u v) where
  vec : alloc.vec.Vec T
  alloc : A

/-- [allocator_api2::stable::vec::into_iter::IntoIter]: the elements not yet yielded. -/
structure allocator_api2.stable.vec.into_iter.IntoIter (T : Type u) (A : Type v) : Type u where
  items : List T

/-- [allocator_api2::stable::vec::drain::Drain]: the drained elements not yet yielded. (The
source vector already has the range removed when `Vec::drain` returns: it is mutably borrowed for
the lifetime of the `Drain`, and the native `Drop` moves the tail back.) -/
structure allocator_api2.stable.vec.drain.Drain (T : Type u) (A : Type v) : Type u where
  items : List T
