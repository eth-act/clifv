import FV.Backend.Proof.StockD0Code
import FV.Backend.SemanticNICheck
import FV.E2E.LinkCheckFast
import FV.E2E.LinkIdx
import FV.E2E.LinkIdxSigI

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

def staticChksSemanticNI (stage : Clif.Function → VCode → VCode) (I : LinkInput) (g : Clif.Function) (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  [("compiled: pipeline", r.toBool),
   ("compiled: lowerCheck", SemanticNI.check g a.vc),
   ("compiled: prepCheck", prepCheck (stage g a.vc) a.vcp),
   ("compiled: checkAlloc", (checkAlloc a.vcp a.rf).toBool),
   ("covered", formsCoveredB ⟨a.fa.k, a.af.slotBase⟩ a.vcp),
   ("sretRets", allInsts a.vc (retsB g)),
   ("argRegs: distinct", decide (regLocs g.sig).Nodup),
   ("argRegs: argument registers", (regLocs g.sig).all (·.isArgReg)),
   ("argRegs: width ≤ 64", g.sig.params.all (fun p => decide (p.ty.width ≤ 64))),
   ("entryRegs", entryB g a.vcp),
   ("fits", decide (a.base.toNat + 4 * a.fb.words.size ≤ 2 ^ 64)),
   ("depth", decide (frameDrop a.af ≤ I.D)),
   ("free (no return_call)", linkFreeB g),
   ("subset: clif-subset-v2 E", Compile.functionE g),
   ("subset: ABI signatures", sigAbiOk g.sig && g.externs.all (fun e => sigAbiOk e.2.sig)),
   ("subset: indirect-call signatures", indSigsOk g)]

def chksSemanticNI (stage : Clif.Function → VCode → VCode) (I : LinkInput) (P : Clif.Program)
    (T : List (Clif.Function × Art)) (g : Clif.Function) (r : Except String Art) :
    List (String × Bool) := staticChksSemanticNI stage I g r ++ linkChks I P T g r

def okRSemanticNI (stage : Clif.Function → VCode → VCode) (I : LinkInput) (R : Res) : Bool :=
  (globalChks I (progOf R) (tabOf R)).all (·.2) &&
    R.all fun e => (chksSemanticNI stage I (progOf R) (tabOf R) e.1 e.2).all (·.2)

theorem okRSemanticNI_global (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res} (h : okRSemanticNI stage I R = true) :
    ∀ c ∈ globalChks I (progOf R) (tabOf R), c.2 = true := by
  simp only [okRSemanticNI, chksSemanticNI, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1

theorem okRSemanticNI_names (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res} (h : okRSemanticNI stage I R = true) :
    ((progOf R).funcs.map (·.name)).Nodup := by
  have := okRSemanticNI_global stage h _ (by simp [globalChks]; exact Or.inl rfl)
  simpa using this

/-- The image check is unchanged by semantic lowering validation. -/
theorem okRSemanticNI_img (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res}
    (checked : okRSemanticNI stage I R = true) : imgB (tabOf R) = true :=
  okRSemanticNI_global stage checked ("imgCode: the image reads back",imgB (tabOf R))
    (by simp [globalChks])

/-- `okRSemanticNI` with the lookups of `linkChks`/`globalChks` computed once
(`LinkCtx.of`, `linkChksWith_of`, `globalChksWith_of`), the program's scans per call site
indexed (`LinkIdx.of`, #1062), the signatures a `blr` site or an indirect call may enter indexed
(`sigIdx`, `linkChksWithIX_of`, #1108) and the per-function checks in parallel tasks
(`Link.parMap`). The compiler evaluates this in place of `okRSemanticNI`
(`okRSemanticNI_eq_fast`, `@[csimp]`): the list lookups per call site made the Stock routes'
checks hours long on 15k-function programs (#683), the scans of the candidates and the
sequential evaluation hours long on ruint's 227k functions (#1108). No statement changes. -/
def okRSemanticNIFast (stage : Clif.Function → VCode → VCode) (I : LinkInput) (R : Res) : Bool :=
  let P := progOf R
  let T := tabOf R
  let C := LinkCtx.of I P T
  let X := LinkIdx.of P C.ents
  let SI := sigIdx P C.S
  (globalChksWith C I P T).all (·.2) &&
    (Link.parMap (fun e => (staticChksSemanticNI stage I e.1 e.2 ++ linkChksWithIX C X SI e.1 e.2).all
      (·.2)) R).all id

@[csimp] theorem okRSemanticNI_eq_fast : @okRSemanticNI = @okRSemanticNIFast := by
  funext stage I R
  simp only [okRSemanticNIFast, okRSemanticNI, chksSemanticNI, linkChksWithIX_of, linkChksWith_of,
    globalChksWith_of, Link.parMap_eq, List.all_map, Function.comp_def, id]

end E2E.LinkCheck
