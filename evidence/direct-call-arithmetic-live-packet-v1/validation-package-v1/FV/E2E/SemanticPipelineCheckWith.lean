import FV.E2E.SemanticPipelineCheck

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Extend only the existing lowering verdict. Every other check stays in the original list. -/
def staticChksSemanticFor (extra : Clif.Function → VCode → Bool)
    (stage : Clif.Function → VCode → VCode) (I : LinkInput) (g : Clif.Function)
    (r : Except String Art) : List (String × Bool) :=
  (staticChksSemanticNI stage I g r).map fun (name,value) =>
    if name = "compiled: lowerCheck" then (name,value || extra g (getOk r).vc) else (name,value)

def chksSemanticFor (extra : Clif.Function → VCode → Bool)
    (stage : Clif.Function → VCode → VCode) (I : LinkInput) (P : Clif.Program)
    (T : List (Clif.Function × Art)) (g : Clif.Function) (r : Except String Art) :
    List (String × Bool) := staticChksSemanticFor extra stage I g r ++ linkChks I P T g r

def okRSemanticFor (extra : Clif.Function → VCode → Bool)
    (stage : Clif.Function → VCode → VCode) (I : LinkInput) (R : Res) : Bool :=
  (globalChks I (progOf R) (tabOf R)).all (·.2) &&
    R.all fun e => (chksSemanticFor extra stage I (progOf R) (tabOf R) e.1 e.2).all (·.2)

/-- The original checker is the exact instance with no added lowering class. -/
theorem staticChksSemanticFor_previous (stage : Clif.Function → VCode → VCode)
    (I : LinkInput) (g : Clif.Function) (r : Except String Art) :
    staticChksSemanticFor (fun _ _ => false) stage I g r = staticChksSemanticNI stage I g r := by
  simp [staticChksSemanticFor,staticChksSemanticNI]

theorem okRSemanticFor_previous (stage : Clif.Function → VCode → VCode) (I : LinkInput) (R : Res) :
    okRSemanticFor (fun _ _ => false) stage I R = okRSemanticNI stage I R := by
  simp only [okRSemanticFor,okRSemanticNI,chksSemanticFor,chksSemanticNI,staticChksSemanticFor_previous]

theorem okRSemanticFor_global (extra : Clif.Function → VCode → Bool)
    (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res}
    (checked : okRSemanticFor extra stage I R = true) :
    ∀ c ∈ globalChks I (progOf R) (tabOf R),c.2 = true := by
  simp only [okRSemanticFor,Bool.and_eq_true,List.all_eq_true] at checked
  exact checked.1

theorem okRSemanticFor_names (extra : Clif.Function → VCode → Bool)
    (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res}
    (checked : okRSemanticFor extra stage I R = true) : ((progOf R).funcs.map (·.name)).Nodup := by
  have names := okRSemanticFor_global extra stage checked _ (by simp [globalChks]; exact Or.inl rfl)
  simpa using names

/-- Retain the existing cached link context for the extended validator. -/
def okRSemanticForFast (extra : Clif.Function → VCode → Bool)
    (stage : Clif.Function → VCode → VCode) (I : LinkInput) (R : Res) : Bool :=
  let P := progOf R
  let T := tabOf R
  let C := LinkCtx.of I P T
  (globalChksWith C I P T).all (·.2) &&
    R.all fun e => (staticChksSemanticFor extra stage I e.1 e.2 ++ linkChksWith C P e.1 e.2).all (·.2)

@[csimp] theorem okRSemanticFor_eq_fast : @okRSemanticFor = @okRSemanticForFast := by
  funext extra stage I R
  simp only [okRSemanticForFast,okRSemanticFor,chksSemanticFor,linkChksWith_of,globalChksWith_of]

/-- Expanding the extended list changes only its lowering verdict. -/
theorem staticChksSemanticFor_expanded (extra : Clif.Function → VCode → Bool)
    (stage : Clif.Function → VCode → VCode) (I : LinkInput) (g : Clif.Function)
    (r : Except String Art) : staticChksSemanticFor extra stage I g r =
    (let a := getOk r
  [("compiled: pipeline", r.toBool),
   ("compiled: lowerCheck", (SemanticNI.check g a.vc || extra g a.vc)),
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
   ("subset: indirect-call signatures", indSigsOk g)]) := by rfl

end E2E.LinkCheck
