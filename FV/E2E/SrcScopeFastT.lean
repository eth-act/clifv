import FV.E2E.SrcScopeDefsT
import FV.E2E.SrcScopeFast

/-!
# `SrcScopeTB` decided in parallel, with a hash map of the program (#1084)

`SrcScopeTB I` (`FV/E2E/SrcScopeDefsT.lean`) parses the input's functions one after the other and
looks every declaration's callee up in the program (`declSigB`: `Program.func?`, a list scan per
declaration): quadratic in the program, as `SrcScopeB` was before `SrcScopeBFast`.
`SrcScopeTBFast` parses and checks the functions in parallel tasks and looks the callees up in
`funcMap`; `SrcScopeTB_eq_fast` (`@[csimp]`) makes it the compiled code of `SrcScopeTB`.
`SrcScopeTB_withDepth`: it reads the input's functions only, so on the typed Stock route's input
(`inputProductionWith`, whose call-level stack is computed from every function's pipeline result)
it is decided on the placed spec's `input0`. No statement changes.
-/

namespace E2E.LinkCheck

open Clif Opt.Legalize128

/-- `SrcScopeTB` with the functions parsed and checked in parallel tasks and the declarations'
callees looked up in `funcMap` (`SrcScopeTB_eq_fast`). -/
def SrcScopeTBFast (I : LinkInput) : Bool :=
  let P : Clif.Program := { funcs := Link.parMap (·.src) I.funcs }
  let fm := funcMap P
  (Link.parMap (fun g => legalOkTB g && linkFreeB g && declSigWithB (fun n => fm[n]?) g)
    P.funcs).all id && helperFreeB P

private theorem srcScopeT_split (P : Clif.Program) :
    (P.funcs.all legalOkTB && P.funcs.all linkFreeB && P.funcs.all (declSigB P) && helperFreeB P) =
      ((P.funcs.map fun g => legalOkTB g && linkFreeB g && declSigWithB P.func? g).all id &&
        helperFreeB P) := by
  have hd : ∀ g, declSigWithB P.func? g = declSigB P g := fun _ => rfl
  cases helperFreeB P <;> simp only [Bool.and_false, Bool.and_true]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, List.all_eq_true, List.all_map, Function.comp_apply, id_eq, hd]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩ g hg
    exact ⟨⟨h1 g hg, h2 g hg⟩, h3 g hg⟩
  · intro h
    exact ⟨⟨fun g hg => (h g hg).1.1, fun g hg => (h g hg).1.2⟩, fun g hg => (h g hg).2⟩

@[csimp] theorem SrcScopeTB_eq_fast : @SrcScopeTB = @SrcScopeTBFast := by
  funext I
  simp only [SrcScopeTBFast, Link.parMap_eq, funcMap_fun]
  exact srcScopeT_split I.srcProg

/-- `SrcScopeTB` does not read the call-level stack. -/
theorem SrcScopeTB_withDepth (I : LinkInput) (R : Res) : SrcScopeTB (I.withDepth R) = SrcScopeTB I :=
  rfl

end E2E.LinkCheck
