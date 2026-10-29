module

public import FV.Link.Image
public import FV.E2E.LinkScopeFast

@[expose] public section

/-! # The executable compiler (L1): the definition

`compileExe S file0`: the whole compiler as one Lean function — the input conditions
(`InScopeIn`, decided on the CLIF program alone without running any compiler stage; per function
in parallel tasks, `inScopeInPar_eq`), then the Lean linker `leanLink` (the compiler's pipeline `pipeT` on every
function, the placement, the relocation, the linker's checks of its own output and of
rust-lld's). Its input is a `LinkSpec` (the CLIF functions with `lean-regalloc`'s oracle answers,
the placement, the outside part's addresses) and rust-lld's executable `file0` of the outside part
around the region's placeholder. Kept free of proofs so that `lake exe lean-link` runs it; its
theorems are in `FV/Link/Exe.lean`, `FV/Link/ExeTotal.lean`.
-/

namespace Link

open E2E.LinkCheck

/-- `InScopeP` with the per-function conditions (`fnScopeB`: `lowerFunction` and `prepare`
accept, …) evaluated in parallel tasks, the program-level ones with hash maps of the program's
functions and of the symbols (`progScopeFastB`, `assocMap`: linear instead of quadratic, T3d). -/
def inScopePar (I : LinkInput) : Bool :=
  let sy := assocMap I.syms
  progScopeFastB I.prog (fun n => sy[n]?) && (parMap fnScopeB I.prog.funcs).all id

theorem inScopePar_eq (I : LinkInput) : inScopePar I = InScopeP I := by
  simp only [inScopePar, assocMap_fun, progScopeFastB_eq, InScopeP, parMap_eq, List.all_map,
    Function.comp_def, id]

/-- The error on an input outside `InScopeP` (`Link.DeadCleanup.compileExe`'s check). -/
def outOfScopeMsg : String := "the input is outside the verified subset (InScopeP)"

/-- `InScopeIn` with the per-function conditions (`fnScopeInB`, decided on the CLIF function
alone) evaluated in parallel tasks, the program-level ones with hash maps (`progScopeInFastB`). -/
def inScopeInPar (I : LinkInput) : Bool :=
  let sy := assocMap I.syms
  progScopeInFastB I.prog (fun n => sy[n]?) && (parMap fnScopeInB I.prog.funcs).all id

theorem inScopeInPar_eq (I : LinkInput) : inScopeInPar I = InScopeIn I := by
  simp only [inScopeInPar, assocMap_fun, progScopeInFastB_eq, InScopeIn, parMap_eq, List.all_map,
    Function.comp_def, id]

/-- `compileExe`'s error on an input outside the verified subset (`InScopeIn`). -/
def outOfScopeInMsg : String := "the input is outside the verified subset (InScopeIn)"

/-- **The executable compiler**: the input conditions (`InScopeIn`), then the Lean linker. -/
def compileExe (S : LinkSpec) (file0 : ByteArray) : Except String ByteArray :=
  if inScopeInPar S.input0 then leanLink S file0 else .error outOfScopeInMsg

end Link
