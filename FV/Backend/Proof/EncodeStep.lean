import FV.Backend.Proof.EncodeLayout

/-!
# M5 → M7: executing a laid-out function on the Arm model

`FnBin.program base b` loads the function's words at `base` (word `k` at `base + 4k`, the
model's `Program` association list). `FnAsm.stepi_eq_sem`: on an error-free state running that
program with `PC = base + off j`, where line `j` is instruction `i`, one `stepi` is
`Insn.sem i` at offset `off j` with the function's label map, i.e.
`exec_inst (i.toArmInst ⟨off j, labels⟩)`. Together with `FnAsm.layout_branch`
(PC-relative offsets are `off target - off j`) and `signExtend_append_zero`, this is what M7
needs from M5 (the object writer, linker and loader that put the words at `base` are trusted,
PLAN.md §5).
-/

namespace Backend

open Arm

/-- `ws` at consecutive words from `base + 4k`. -/
def wordsAt (base : BitVec 64) : Nat → List (BitVec 32) → Program
  | _, [] => []
  | k, w :: ws => (base + BitVec.ofNat 64 (4 * k), w) :: wordsAt base (k + 1) ws

/-- The function's code words loaded at `base`. -/
def FnBin.program (base : BitVec 64) (b : FnBin) : Program := wordsAt base 0 b.words.toList

theorem wordsAt_find {base : BitVec 64} {ws : List (BitVec 32)} {k j : Nat} {w : BitVec 32}
    (hsz : 4 * (k + ws.length) ≤ 2 ^ 64) (hj : ws[j]? = some w) :
    (wordsAt base k ws).find? (base + BitVec.ofNat 64 (4 * (k + j))) = some w := by
  induction ws generalizing k j with
  | nil => simp at hj
  | cons w0 ws ih =>
    simp only [wordsAt, Map.find?]
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      simp [hj]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      have hne : base + BitVec.ofNat 64 (4 * k) ≠ base + BitVec.ofNat 64 (4 * (k + (j + 1))) := by
        intro heq
        have := congrArg BitVec.toNat ((BitVec.add_right_inj base).mp heq)
        have hlen : j < ws.length := (List.getElem?_eq_some_iff.mp hj).1
        simp only [List.length_cons] at hsz
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        omega
      rw [ite_eq_right_iff.mpr (fun h => absurd h hne)]
      have := @ih (k + 1) j (by simp only [List.length_cons] at hsz; omega) hj
      rwa [show k + 1 + j = k + (j + 1) by omega] at this

theorem FnBin.program_find {base : BitVec 64} {b : FnBin} {k : Nat} {w : BitVec 32}
    (hsz : 4 * b.words.size ≤ 2 ^ 64) (hk : b.words[k]? = some w) :
    (b.program base).find? (base + BitVec.ofNat 64 (4 * k)) = some w := by
  have := @wordsAt_find base b.words.toList 0 k w (by simpa using hsz) (by simpa using hk)
  simpa [FnBin.program] using this

/-- **Executing laid-out code.** Line `j` of a laid-out function is instruction `i`; on an
error-free state whose program is the function loaded at `base` (smaller than the address
space) and whose `PC` is `base + off j`, one `stepi` executes `Insn.sem i` at offset `off j`
with the function's label map. -/
theorem FnAsm.stepi_eq_sem {f : FnAsm} {b : FnBin} {m : Std.HashMap Lbl Nat} {j : Nat}
    {i : Insn} {t : Option Clif.TrapCode} {s : ArmState} {base : BitVec 64}
    (h : f.layout = .ok b) (hm : labelOffsets f.lines = .ok m)
    (hj : f.lines.toList[j]? = some (.ins i t)) (hsz : f.size ≤ 2 ^ 64)
    (hprog : s.program = b.program base)
    (hpc : r .PC s = base + BitVec.ofNat 64 (lineOffset f.lines.toList j))
    (herr : r .ERR s = .None) :
    i.sem ⟨lineOffset f.lines.toList j, (m[·]?)⟩ s = .ok (stepi s) := by
  obtain ⟨h4, w, hw, hk⟩ := FnAsm.layout_word h hm hj rfl
  have hfetch : fetch_inst (r .PC s) s = some w := by
    rw [fetch_inst_from_program, hprog, hpc]
    have := FnBin.program_find (base := base) (by have := (FnAsm.layout_size h).1; omega) hk
    rwa [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h4)] at this
  exact Insn.stepi_eq_sem herr hfetch hw

end Backend
