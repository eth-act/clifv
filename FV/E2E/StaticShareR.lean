import FV.E2E.StaticShare
import FV.E2E.SemanticPipelineCheckTR

/-! # The typed Stock checks with the register-guarded calls from the integer evaluation (#753)

`withTSOfNI` for `staticChksWithTSR` (the per-function static checks of `okRWithTSR`):
`link-check` evaluates `staticChksSemanticNI stage I g r` once per function and, in its typed
Stock mode, takes the entries both lists share from it by position and computes only the others
(`withTSROfNI_eq`).
-/

set_option autoImplicit false
namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver

/-- `staticChksWithTSR` from `staticChksSemanticNI`'s list `ni` of the same stage, input, function
and result: the entries both lists share are read from `ni` (by position). -/
def withTSROfNI (g : Clif.Function) (r : Except String Art) (ni : List (String × Bool)) :
    List (String × Bool) :=
  let a := getOk r
  let v (i : Nat) : Bool := ((ni[i]?).map (·.2)).getD false
  let sret := g.sig.params.any (·.purpose == .sret)
  [("compiled: pipeline", v 0),
   ("compiled: Stock (SemanticNI without call sites, or lowerCheck) or lowerFunction lowerCheckT/TCF",
     (v 13 && !sret && ((noCallSitesB a.vcp && v 1) || lowerCheck g a.vc)) ||
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

theorem withTSROfNI_eq (stage : Clif.Function → VCode → VCode) (I : LinkInput) (g : Clif.Function)
    (r : Except String Art) :
    withTSROfNI g r (staticChksSemanticNI stage I g r) = staticChksWithTSR stage I g r := by
  simp only [withTSROfNI, staticChksSemanticNI, staticChksWithTSR, lowerOkTSRB,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some]

end E2E.LinkCheck
