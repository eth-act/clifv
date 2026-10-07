import FV.Link.Image

/-! # The executable compiler (L1): the definition

`compileExe S file0`: the whole compiler as one Lean function — the input conditions
(`InScopeP`, decided on the CLIF program alone, before any compilation), then the Lean linker
`leanLink` (the compiler's pipeline `pipeT` on every function, the placement, the relocation,
the linker's checks of its own output and of rust-lld's). Its input is a `LinkSpec` (the CLIF
functions with `lean-regalloc`'s oracle answers, the placement, the outside part's addresses)
and rust-lld's executable `file0` of the outside part around the region's placeholder. Kept free
of proofs so that `lake exe lean-link` runs it; its theorems are in `FV/Link/Exe.lean`.
-/

namespace Link

open E2E.LinkCheck

/-- **The executable compiler**: the input conditions (`InScopeP`), then the Lean linker. -/
def compileExe (S : LinkSpec) (file0 : ByteArray) : Except String ByteArray :=
  if InScopeP S.input0 then leanLink S file0
  else .error "the input is outside the verified subset (InScopeP)"

end Link
