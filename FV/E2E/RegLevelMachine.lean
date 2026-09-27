import FV.E2E.Statement
import FV.E2E.RegLevelEmit
import FV.Backend.Proof.RegallocCSem
import FV.Backend.Proof.RegallocFwd

/-!
# The Arm machine of the register-level theorem (M6)

`RegLevelCorrect` is stated for an Arm machine `astep`. The function's code calls externs and
uses link-time symbol addresses, which are outside the laid-out function: `ArmStepX X H fa` is
`Arm.stepi`, except at

* `bl name` / `blr xn`: the callee runs (`H.call (some name)` / `H.call none`: the state at its
  return; its contract is `CalleeOk`),
* `adrp xd, :got:sym` / `adrp xd, sym+off` (the first instruction of `loadExtNameGot/Near`):
  `xd := X.sym sym off` (the linker's resolved address), and the paired `ldr xd, [xd,
  :got_lo12:sym]` / `add xd, xd, :lo12:sym+off`: no further effect (the pair computes the
  address). Both advance the pc by 4.

The instruction at the pc is found from the function's line list `fa`; the load address `base`
is the address of the first word of the program (`progBase`: `AbiEntry.program` puts the
function's words there, the program never changes).
-/

namespace Backend.Proof

open Backend

/-- The callee: the Arm state at the return of `bl name` (`some name`) or `blr` (`none`). -/
structure ArmHooks where
  call : Option String → Arm.ArmState → Arm.ArmState

/-- Address of the first word of the loaded program. -/
def progBase (s : Arm.ArmState) : BitVec 64 :=
  match s.program with
  | (a, _) :: _ => a
  | [] => 0

open Classical in
/-- The instruction of the laid-out function `fa` (loaded at `base`) at address `pc`. -/
noncomputable def insnAt (fa : FnAsm) (base pc : BitVec 64) : Option Insn :=
  if h : ∃ j i t, fa.lines.toList[j]? = some (.ins i t) ∧
      base + BitVec.ofNat 64 (lineOffset fa.lines.toList j) = pc then
    some (Classical.choose (Classical.choose_spec h))
  else none

/-- One step of the Arm machine with the external hooks. -/
noncomputable def ArmStepX (X : ExtSem) (H : ArmHooks) (fa : FnAsm) (s : Arm.ArmState) :
    Arm.ArmState :=
  let pc := Arm.r .PC s
  match insnAt fa (progBase s) pc with
  | some (.bl n) => H.call (some n) s
  | some (.blr _) => H.call none s
  | some (.adrpGot rd n) =>
    Arm.w .PC (pc + 4) (Arm.w (.GPR (rd.encZR.toOption.getD 31#5)) (X.sym n 0) s)
  | some (.ldrGotLo12 _ _ _) => Arm.w .PC (pc + 4) s
  | some (.adrp rd n off) =>
    Arm.w .PC (pc + 4) (Arm.w (.GPR (rd.encZR.toOption.getD 31#5)) (X.sym n off) s)
  | some (.addLo12 _ _ _ _) => Arm.w .PC (pc + 4) s
  | _ => Arm.stepi s

/-! ## Finding the instruction at the pc -/

theorem lineOffset_succ (L : List Line) (j : Nat) (ln : Line) (h : L[j]? = some ln) :
    lineOffset L (j + 1) = lineOffset L j + ln.size := by
  unfold lineOffset
  rw [List.take_add_one, h]
  simp

theorem lineOffset_mono (L : List Line) {j j' : Nat} (h : j ≤ j') :
    lineOffset L j ≤ lineOffset L j' := by
  unfold lineOffset
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.map_append, List.sum_append]
  omega

theorem sum_take_le : ∀ (l : List Nat) (j : Nat), (l.take j).sum ≤ l.sum
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | a :: l, j + 1 => by simp only [List.take_succ_cons, List.sum_cons]; have := sum_take_le l j; omega

theorem lineOffset_le_size (L : List Line) (j : Nat) :
    lineOffset L j ≤ (L.map Line.size).sum := by
  unfold lineOffset
  rw [List.map_take]
  exact sum_take_le _ j

/-- Distinct instruction lines have distinct offsets. -/
theorem lineOffset_inj {L : List Line} {j j' : Nat} {i i' : Insn} {t t' : Option Clif.TrapCode}
    (hj : L[j]? = some (.ins i t)) (hj' : L[j']? = some (.ins i' t'))
    (he : lineOffset L j = lineOffset L j') : j = j' := by
  rcases Nat.lt_trichotomy j j' with h | h | h
  · have h1 := lineOffset_succ L j _ hj
    have h2 := lineOffset_mono L (show j + 1 ≤ j' by omega)
    simp [Line.size] at h1
    omega
  · exact h
  · have h1 := lineOffset_succ L j' _ hj'
    have h2 := lineOffset_mono L (show j' + 1 ≤ j by omega)
    simp [Line.size] at h1
    omega

/-- The instruction at the offset of an instruction line is that line's instruction. -/
theorem insnAt_line {fa : FnAsm} {base : BitVec 64} {j : Nat} {i : Insn} {t : Option Clif.TrapCode}
    (hsz : (fa.lines.toList.map Line.size).sum ≤ 2 ^ 64)
    (hj : fa.lines.toList[j]? = some (.ins i t)) :
    insnAt fa base (base + BitVec.ofNat 64 (lineOffset fa.lines.toList j)) = some i := by
  have hex : ∃ j' i' t', fa.lines.toList[j']? = some (.ins i' t') ∧
      base + BitVec.ofNat 64 (lineOffset fa.lines.toList j') =
        base + BitVec.ofNat 64 (lineOffset fa.lines.toList j) := ⟨j, i, t, hj, rfl⟩
  unfold insnAt
  rw [dite_cond_eq_true (eq_true hex)]
  congr 1
  obtain ⟨t'', h1, h2⟩ := Classical.choose_spec (Classical.choose_spec hex)
  generalize Classical.choose (Classical.choose_spec hex) = I at h1 ⊢
  generalize Classical.choose hex = J at h1 h2
  have h2' := (BitVec.add_right_inj _).mp h2
  have hl1 := lineOffset_le_size fa.lines.toList (J + 1)
  have hl2 := lineOffset_le_size fa.lines.toList (j + 1)
  have hs1 := lineOffset_succ fa.lines.toList J _ h1
  have hs2 := lineOffset_succ fa.lines.toList j _ hj
  simp only [Line.size] at hs1 hs2
  have he : lineOffset fa.lines.toList J = lineOffset fa.lines.toList j := by
    have := congrArg BitVec.toNat h2'
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  have := lineOffset_inj h1 hj he
  rw [this, hj] at h1
  cases h1
  rfl

theorem progBase_eq {s : Arm.ArmState} {base : BitVec 64} {ws : List (BitVec 32)}
    (h : s.program = wordsAt base 0 ws) (hne : ws ≠ []) : progBase s = base := by
  cases ws with
  | nil => exact absurd rfl hne
  | cons w ws => simp [progBase, h, wordsAt]

end Backend.Proof

namespace Backend.Proof

open Backend

/-- Instructions the machine hooks (calls, relocated address computations). -/
def _root_.Backend.Insn.hooked : Insn → Bool
  | .bl _ | .blr _ | .adrpGot .. | .ldrGotLo12 .. | .adrp .. | .addLo12 .. => true
  | _ => false

theorem codeLines_sizes : ∀ L : List Line, (L.map Line.size).sum = 4 * (codeLines L).length
  | [] => rfl
  | ln :: L => by
    have := codeLines_sizes L
    cases ln <;> simp [codeLines, Line.isLabel, Line.size] at this ⊢ <;> omega

/-- The function's lines laid out: total size as a byte count. -/
theorem layout_sum {fa : FnAsm} {fb : FnBin} (hl : fa.layout = .ok fb) :
    (fa.lines.toList.map Line.size).sum = 4 * fb.words.size := by
  rw [codeLines_sizes, (FnAsm.layout_size hl).2]

/-- **One machine step at an instruction line** that is not hooked: the model executes the
instruction the encoder specified at that offset. -/
theorem armStepX_ins {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {fb : FnBin}
    {lm : Std.HashMap Lbl Nat} {base : BitVec 64} {s : Arm.ArmState} {j : Nat} {i : Insn}
    {t : Option Clif.TrapCode}
    (hl : fa.layout = .ok fb) (hm : labelOffsets fa.lines = .ok lm)
    (hfit : 4 * fb.words.size ≤ 2 ^ 64)
    (hj : fa.lines.toList[j]? = some (.ins i t)) (hi : i.hooked = false)
    (hprog : s.program = fb.program base)
    (hpc : Arm.r .PC s = base + BitVec.ofNat 64 (lineOffset fa.lines.toList j))
    (herr : Arm.r .ERR s = .None) :
    ∃ a, i.toArmInst ⟨lineOffset fa.lines.toList j, (lm[·]?)⟩ = .ok a ∧
      ArmStepX X H fa s = Arm.exec_inst a s := by
  have hsem := FnAsm.stepi_eq_sem hl hm hj (by have := (FnAsm.layout_size hl).1; omega) hprog hpc herr
  obtain ⟨_, w, hw, hk⟩ := FnAsm.layout_word hl hm hj rfl
  have hne : fb.words.toList ≠ [] := by
    intro h
    have : fb.words.size = 0 := by simpa using congrArg List.length h
    simp [this] at hk
  have hb : progBase s = base := progBase_eq (by rw [hprog]; rfl) hne
  have hsum := layout_sum hl
  have hins : insnAt fa (progBase s) (Arm.r .PC s) = some i := by
    rw [hb, hpc]; exact insnAt_line (by omega) hj
  have hst : ArmStepX X H fa s = Arm.stepi s := by
    unfold ArmStepX
    simp only [hins]
    cases i <;> simp_all [Insn.hooked]
  simp only [Insn.sem, Functor.map, Except.map] at hsem
  split at hsem
  · cases hsem
  · rename_i a ha
    simp only [Except.ok.injEq] at hsem
    exact ⟨a, ha, by rw [hst, hsem]⟩

end Backend.Proof

namespace Backend.Proof

open Backend

/-- The states between the lines of a straight-line run are error-free and keep the program
(needed only for expansions of more than one instruction). -/
def InterOk (env : Env) (ls : List Line) (s : Arm.ArmState) : Prop :=
  ∀ k, 0 < k → k < ls.length → ∀ s1, execLines env (ls.take k) s = some s1 →
    Arm.r .ERR s1 = .None ∧ s1.program = s.program

/-- **Straight-line code on the machine**: lines `ls` placed at line `j` (instructions, not
hooked) run by `execLines` at the offsets of the layout are `ls.length` machine steps. -/
theorem iterN_execLines {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {fb : FnBin}
    {lm : Std.HashMap Lbl Nat} {base : BitVec 64}
    (hl : fa.layout = .ok fb) (hm : labelOffsets fa.lines = .ok lm)
    (hfit : 4 * fb.words.size ≤ 2 ^ 64) :
    ∀ (ls : List Line) (j : Nat) (s s' : Arm.ArmState),
      (∀ k ln, ls[k]? = some ln → fa.lines.toList[j + k]? = some ln) →
      (∀ i t, Line.ins i t ∈ ls → i.hooked = false) →
      s.program = fb.program base →
      Arm.r .PC s = base + BitVec.ofNat 64 (lineOffset fa.lines.toList j) →
      Arm.r .ERR s = .None →
      InterOk ⟨lineOffset fa.lines.toList j, (lm[·]?)⟩ ls s →
      execLines ⟨lineOffset fa.lines.toList j, (lm[·]?)⟩ ls s = some s' →
      iterN (ArmStepX X H fa) ls.length s = s'
  | [], _, s, s', _, _, _, _, _, _, h => by simp [execLines] at h; exact h
  | .label _ :: _, _, _, _, _, _, _, _, _, _, h => by simp [execLines] at h
  | .word _ _ :: _, _, _, _, _, _, _, _, _, _, h => by simp [execLines] at h
  | .ins i t :: ls, j, s, s', hat, hhook, hprog, hpc, herr, hinter, h => by
    have hj : fa.lines.toList[j]? = some (.ins i t) := by simpa using hat 0 _ rfl
    obtain ⟨a, ha, hstep⟩ := armStepX_ins (X := X) (H := H) hl hm hfit hj
      (hhook i t (by simp)) hprog hpc herr
    simp only [execLines, ha] at h
    split at h
    · rename_i hpc'
      have hoff := lineOffset_succ fa.lines.toList j _ hj
      simp only [Line.size] at hoff
      simp only [List.length_cons, iterN]
      rw [hstep]
      cases ls with
      | nil => simpa [execLines, iterN] using h
      | cons ln ls' =>
        have h1 := hinter 1 (by omega) (by simp) (Arm.exec_inst a s)
          (by simp [execLines, ha, hpc'])
        refine iterN_execLines (base := base) hl hm hfit (ln :: ls') (j + 1) _ s' ?_ ?_ ?_ ?_ h1.1 ?_ ?_
        · intro k ln' hk
          have := hat (k + 1) ln' (by simpa using hk)
          rwa [show j + (k + 1) = j + 1 + k by omega] at this
        · intro i' t' hm'
          exact hhook i' t' (List.mem_cons_of_mem _ hm')
        · rw [h1.2, hprog]
        · rw [hpc', hpc, hoff, BitVec.add_assoc]
          congr 1
          apply BitVec.eq_of_toNat_eq
          simp
        · intro k hk0 hk s1 hs1
          have := hinter (k + 1) (by omega) (by simp at hk ⊢; omega) s1
            (by simp [execLines, ha, hpc']; simpa [hoff] using hs1)
          exact ⟨this.1, by rw [this.2, h1.2]⟩
        · simpa [hoff] using h
    · cases h

end Backend.Proof
