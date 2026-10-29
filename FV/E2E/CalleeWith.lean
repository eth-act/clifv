module

public import FV.E2E.LinkCheckFast

@[expose] public section

/-!
# `calleeB` with the declared names given (S11e6, #419)

The program's callees condition `calleeB` with the declared names (`calleeSet`) and "some
function has an indirect call" given (`calleeWithB_eq`); used by `compileExeT`'s std-sized checks
(`FV/Link/DeadCleanupCompileTFast.lean`, `okBCleanupTFast`) and `link-check`.
-/

namespace E2E.LinkCheck

/-- `calleeB P S g` with the declared names (`cs`) and "some function of `P` has an indirect
call" (`anyInd`) given. -/
def calleeWithB (cs : String → Bool) (anyInd : Bool) (S : String → Option Nat)
    (g : Clif.Function) : Bool :=
  cs g.name || ((S g.name).isSome && anyInd)

theorem calleeWithB_eq (P : Clif.Program) (S : String → Option Nat) (g : Clif.Function) :
    calleeWithB (fun n => (calleeSet P).contains n) (P.funcs.any (!indFreeB ·)) S g =
      calleeB P S g := by
  simp only [calleeWithB, calleeSet_contains, calleeB]

end E2E.LinkCheck
