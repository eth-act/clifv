import FV.E2E.SemanticPipelineCheckWith
import FV.E2E.SemanticPipelineCheckT

/-! # The integer and typed Stock per-function checks from one evaluation (#1062)

`link-check` evaluates, per function, the Stock checker's per-function checks
`staticChksSemanticFor extra stage I g r` and, when some function fails them, the typed Stock
checker's `staticChksWithTS stage I g r` on the same results. Both lists hold the validators
`SemanticNI.check`, `prepCheck`, `checkAlloc` and the coverage check of the same artifact. Here
both are computed from `staticChksSemanticNI stage I g r`, evaluated once:
`staticChksSemanticFor` is a map over it (`semanticForOfNI_eq`), and `staticChksWithTS` takes the
shared verdicts from it by position and computes only its own entries (`withTSOfNI_eq`).
-/

set_option autoImplicit false
namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver

/-- `staticChksSemanticFor extra` from `staticChksSemanticNI`'s list `ni`. -/
def semanticForOfNI (extra : Clif.Function → VCode → Bool) (g : Clif.Function)
    (r : Except String Art) (ni : List (String × Bool)) : List (String × Bool) :=
  ni.map fun (name,value) =>
    if name = "compiled: lowerCheck" then (name,value || extra g (getOk r).vc) else (name,value)

theorem semanticForOfNI_eq (extra : Clif.Function → VCode → Bool)
    (stage : Clif.Function → VCode → VCode) (I : LinkInput) (g : Clif.Function)
    (r : Except String Art) :
    semanticForOfNI extra g r (staticChksSemanticNI stage I g r) =
      staticChksSemanticFor extra stage I g r := rfl

/-- `staticChksWithTS` from `staticChksSemanticNI`'s list `ni` of the same stage, input, function
and result: the entries both lists share are read from `ni` (by position). -/
def withTSOfNI (g : Clif.Function) (r : Except String Art) (ni : List (String × Bool)) :
    List (String × Bool) :=
  let a := getOk r
  let v (i : Nat) : Bool := ((ni[i]?).map (·.2)).getD false
  let sret := g.sig.params.any (·.purpose == .sret)
  [("compiled: pipeline", v 0),
   ("compiled: Stock SemanticNI or lowerFunction lowerCheckT/TCF",
     (v 13 && !sret && v 1) ||
       (lowersToB g a.vc &&
         ((Compile.functionET g && lowerCheckT g a.vc) || (Compile.functionETCF g && lowerCheckTCF g a.vc)))),
   ("compiled: prepCheck", v 2),
   ("compiled: checkAlloc", v 3),
   ("covered", v 4),
   ("sretRets", v 5),
   ("argRegs: distinct", v 6),
   ("argRegs: argument registers", v 7),
   ("argRegs: width ≤ 64", v 8),
   ("entryRegs", v 9),
   ("fits", v 10),
   ("depth", v 11),
   ("free (no return_call)", v 12),
   ("subset: storeTyped", Compile.storeTypedB g),
   ("subset: ABI signatures", v 14),
   ("subset: indirect-call signatures", v 15),
   ("sret: subset E, lowerCheck, or returns in retX", !sret ||
     (v 13 && lowerCheck g a.vc) || allInsts a.vc (retsXB g.sig.returns.length))]

theorem withTSOfNI_eq (stage : Clif.Function → VCode → VCode) (I : LinkInput) (g : Clif.Function)
    (r : Except String Art) :
    withTSOfNI g r (staticChksSemanticNI stage I g r) = staticChksWithTS stage I g r := by
  simp only [withTSOfNI, staticChksSemanticNI, staticChksWithTS, lowerOkTSB,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some]

end E2E.LinkCheck
