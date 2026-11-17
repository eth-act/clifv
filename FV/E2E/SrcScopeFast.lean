import FV.E2E.SrcScopeDefs
import FV.E2E.LinkScopeFast

/-!
# The source domain decided in parallel, with a hash map of the program (#1071)

`SrcScopeB I` (`FV/E2E/SrcScopeDefs.lean`) parses the input's functions one after the other and
looks every declaration's callee up in the program (`declSigB`: `Program.func?`, a list scan per
declaration): quadratic in the program. `SrcScopeBFast` parses and checks the functions in
parallel tasks and looks the callees up in `funcMap`; `SrcScopeB_eq_fast` (`@[csimp]`) makes it
the compiled code of `SrcScopeB` (`lake exe lean-link --verified`). No statement changes.
-/

namespace E2E.LinkCheck

open Clif Opt.Legalize128

/-- `SrcScopeB` with the functions parsed and checked in parallel tasks and the declarations'
callees looked up in `funcMap` (`SrcScopeB_eq_fast`). -/
def SrcScopeBFast (I : LinkInput) : Bool :=
  let P : Clif.Program := { funcs := Link.parMap (·.src) I.funcs }
  let fm := funcMap P
  (Link.parMap (fun g => legalOkB g && linkFreeB g && declSigWithB (fun n => fm[n]?) g)
    P.funcs).all id && helperFreeB P

private theorem srcScope_split (P : Clif.Program) :
    (P.funcs.all legalOkB && P.funcs.all linkFreeB && P.funcs.all (declSigB P) && helperFreeB P) =
      ((P.funcs.map fun g => legalOkB g && linkFreeB g && declSigWithB P.func? g).all id &&
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

@[csimp] theorem SrcScopeB_eq_fast : @SrcScopeB = @SrcScopeBFast := by
  funext I
  simp only [SrcScopeBFast, Link.parMap_eq, funcMap_fun]
  exact srcScope_split I.srcProg

end E2E.LinkCheck
