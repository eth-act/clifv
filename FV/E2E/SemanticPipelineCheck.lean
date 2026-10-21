import FV.E2E.PreparedPipeline
import FV.E2E.LinkSemanticNI

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

def staticChksSemanticNI (stage : VCode → VCode) (I : LinkInput) (g : Clif.Function) (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  [("compiled: pipeline", r.toBool),
   ("compiled: lowerCheck", SemanticNI.check g a.vc),
   ("compiled: prepCheck", prepCheck (stage a.vc) a.vcp),
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

def chksSemanticNI (stage : VCode → VCode) (I : LinkInput) (P : Clif.Program)
    (T : List (Clif.Function × Art)) (g : Clif.Function) (r : Except String Art) :
    List (String × Bool) := staticChksSemanticNI stage I g r ++ linkChks I P T g r

def okRSemanticNI (stage : VCode → VCode) (I : LinkInput) (R : Res) : Bool :=
  (globalChks I (progOf R) (tabOf R)).all (·.2) &&
    R.all fun e => (chksSemanticNI stage I (progOf R) (tabOf R) e.1 e.2).all (·.2)

theorem okRSemanticNI_global (stage : VCode → VCode) {I : LinkInput} {R : Res} (h : okRSemanticNI stage I R = true) :
    ∀ c ∈ globalChks I (progOf R) (tabOf R), c.2 = true := by
  simp only [okRSemanticNI, chksSemanticNI, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1

theorem okRSemanticNI_names (stage : VCode → VCode) {I : LinkInput} {R : Res} (h : okRSemanticNI stage I R = true) :
    ((progOf R).funcs.map (·.name)).Nodup := by
  have := okRSemanticNI_global stage h _ (by simp [globalChks]; exact Or.inl rfl)
  simpa using this

/-- The image check is unchanged by semantic lowering validation. -/
theorem okRSemanticNI_img (stage : VCode → VCode) {I : LinkInput} {R : Res}
    (checked : okRSemanticNI stage I R = true) : imgB (tabOf R) = true :=
  okRSemanticNI_global stage checked ("imgCode: the image reads back",imgB (tabOf R))
    (by simp [globalChks])

end E2E.LinkCheck
