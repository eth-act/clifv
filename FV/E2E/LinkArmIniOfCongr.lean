import FV.E2E.LinkArmIniOf

/-!
# The machine's own slot table depends only on the machine (SEM1 #537, executable level)

`LinkSys.iniOf` (`LinkArmIniOf`) is read off the linked machine's run: it depends on the linked
system only through the compiled functions `A`, the program `P`, the base symbols `Xb` and the
machine `mach`. The executable-level theorems use systems that differ only in the exterior `F`,
the image `Img`/`imgMem` (`ofInputCleanup … F`, `extImg`), whose machines are equal
(`mach_F`, `mach_extImg`) but not definitionally.

* `callsTo_congr`, `calleeAt_congr`, `retIdx_congr`, `callStep_congr`, `callE_congr`,
  `owns_congr`, `tabB_congr`, **`iniOf_congr`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable {L₁ L₂ : LinkSys}

theorem callsTo_congr (hA : L₁.A = L₂.A) (hP : L₁.P = L₂.P) (hX : L₁.Xb = L₂.Xb) :
    L₁.CallsTo = L₂.CallsTo := by
  funext g t h
  simp only [CallsTo, hA, hP, hX]

theorem calleeAt_congr (hA : L₁.A = L₂.A) (hP : L₁.P = L₂.P) (hX : L₁.Xb = L₂.Xb) :
    L₁.calleeAt = L₂.calleeAt := by
  funext g t
  unfold calleeAt
  rw [callsTo_congr hA hP hX]

theorem retIdx_congr (hA : L₁.A = L₂.A) (hm : L₁.mach = L₂.mach) :
    L₁.retIdx = L₂.retIdx := by
  funext M h t
  unfold retIdx
  rw [hA, hm]

theorem callStep_congr (hA : L₁.A = L₂.A) (hm : L₁.mach = L₂.mach) :
    L₁.callStep = L₂.callStep := by
  funext M g s c
  unfold callStep
  rw [hA, hm]

theorem callE_congr (hA : L₁.A = L₂.A) (hP : L₁.P = L₂.P) (hX : L₁.Xb = L₂.Xb)
    (hm : L₁.mach = L₂.mach) : L₁.callE = L₂.callE := by
  funext M
  induction M with
  | zero => rfl
  | succ M ih =>
    funext g s c
    simp only [callE]
    rw [ih, hA, hm, calleeAt_congr hA hP hX, retIdx_congr hA hm, callStep_congr hA hm]

theorem owns_congr (hA : L₁.A = L₂.A) (hP : L₁.P = L₂.P) (hX : L₁.Xb = L₂.Xb)
    (hm : L₁.mach = L₂.mach) : L₁.Owns = L₂.Owns := by
  funext M g s k c x
  unfold Owns
  rw [hA, hm, callsTo_congr hA hP hX, callE_congr hA hP hX hm]

theorem tabB_congr (hA : L₁.A = L₂.A) (hP : L₁.P = L₂.P) (hX : L₁.Xb = L₂.Xb)
    (hm : L₁.mach = L₂.mach) : L₁.tabB = L₂.tabB := by
  funext M
  induction M with
  | zero => rfl
  | succ M ih =>
    funext g s k x
    simp only [tabB]
    rw [ih, hA, hm, owns_congr hA hP hX hm, calleeAt_congr hA hP hX, callStep_congr hA hm,
      callE_congr hA hP hX hm]

/-- **The machine's own table depends only on `A`, `P`, `Xb` and the machine.** -/
theorem iniOf_congr (hA : L₁.A = L₂.A) (hP : L₁.P = L₂.P) (hX : L₁.Xb = L₂.Xb)
    (hm : ∀ M g, L₁.mach M g = L₂.mach M g) : L₁.iniOf = L₂.iniOf := by
  have hm' : L₁.mach = L₂.mach := funext fun M => funext fun g => hm M g
  funext M g s
  unfold iniOf
  rw [tabB_congr hA hP hX hm']

end LinkSys

end E2E
