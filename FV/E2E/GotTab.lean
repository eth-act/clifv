import FV.E2E.SemanticExecGot
import FV.E2E.DeadCleanupExecGot
import Std.Data.HashSet.Lemmas

/-! # The GOT premise `GotOk` decided on a result table (#1093)

The executable-word theorems the binary check names (`E2E.ReturnPinExecBytes.binary_correct_exec_proven`,
`E2E.SemanticExecBytes.binary_correct_exec_provenTS`, `E2E.DeadCleanupExecBytes.binary_correct_exec_provenT`
and their `_peak_` siblings) take `hgot : GotOk I file`: the 8 bytes of every GOT slot that a GOT
pair of the program addresses (an `adrGotPage` relocation whose words in the file are
`adrp`/`ldr`, `GotSlot`) are loaded, `ro`/`relro`, and no relocated instruction byte.

`gotTabB T ex` decides it on the result table `T` the checker holds (`link-check`'s `tabOf keep`)
and an excerpt of the file: `gotB` of `FV/E2E/SemanticExecGot.lean` restricted to the pairs whose
second word is an `ldr` (`ldrFormB`). `gotB` checks the slot of every `adrGotPage` relocation,
also where the linker relaxed the pair to `adrp`/`add` (then no GOT slot is read and the "slot"
is the target itself, which may be writable data), so it can fail where `GotOk` holds; `GotSlot`
takes only the `ldr` form (`ldrFormB_ldrW`), so `gotTabB` is sound for both `GotOk`s
(`SemanticExecBytes.gotTabB_sound`, `DeadCleanupExecBytes.gotTabB_sound`).

`link-check` evaluates it as `gotTabFastB` (`@[csimp] gotTabB_eq_fast`, #1145): `relocAtB` scans
every relocation of the table for each byte of each slot, so `gotTabB` takes GOT pairs ×
relocations steps (serde_json's release test executable, 18,614 GOT pairs: not done after an
hour); `gotTabFastB` puts the relocated bytes in a hash set once (`relocAtB_eq_contains`).
-/

namespace E2E.GotTab

open Backend E2E.LinkCheck E2E.BinCheck Elf

/-- `x` is a 64-bit `ldr` with an unsigned offset (the form of `ldrW`). -/
def ldrFormB (x : BitVec 32) : Bool := x.toNat / 2 ^ 22 == 0x3e5

theorem ldrFormB_ldrW {rd k : Nat} (hrd : rd < 32) (hk : k < 512) : ldrFormB (ldrW rd rd k) = true := by
  simp only [ldrFormB, ldrW, BitVec.toNat_ofNat, beq_iff_eq]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- `a` is a byte of a relocated word of the images `T`. -/
def relocAtB (T : List (Clif.Function × Art)) (a : BitVec 64) : Bool :=
  T.any fun e => e.2.fb.relocs.any fun r => (List.range 4).any fun i => a == wAt e.2 (r.offset + i)

/-- **`GotOk` on the result table `T`**: for every `adrGotPage` relocation of `T` whose words in
the excerpt are an `adrp` and an `ldr`, the 8 bytes of the slot they address (`gotOf`) are loaded,
`ro` or `relro`, and no relocated instruction byte. -/
def gotTabB (T : List (Clif.Function × Art)) (ex : Excerpt) : Bool :=
  match phdrs (exRd ex) with
  | some phs =>
    let m := memIn (exRd ex) phs
    T.all fun e => e.2.fb.relocs.all fun rl =>
      !decide (rl.type = .adrGotPage) ||
      match readN m 4 (wAt e.2 rl.offset), readN m 4 (wAt e.2 (rl.offset + 4)) with
      | some x0, some x1 =>
        !ldrFormB x1 ||
        (List.range 8).all fun i =>
          let a := BitVec.ofNat 64 (BinCheck.gotOf (wAt e.2 rl.offset).toNat x0 x1) + BitVec.ofNat 64 i
          (roB phs a || relroB phs a) && (m a).isSome && !relocAtB T a
      | _, _ => false
  | none => false

/-- The addresses of the relocated instruction bytes of the images `T` (`relocAtB`'s). -/
def relocAddrs (T : List (Clif.Function × Art)) : List Nat :=
  T.flatMap fun e => e.2.fb.relocs.flatMap fun r =>
    (List.range 4).map fun i => (wAt e.2 (r.offset + i)).toNat

theorem relocAtB_eq_contains (T : List (Clif.Function × Art)) (a : BitVec 64) :
    relocAtB T a = (Std.HashSet.ofList (relocAddrs T)).contains a.toNat := by
  rw [Std.HashSet.contains_ofList, Bool.eq_iff_iff, List.contains_iff_mem]
  simp only [relocAtB, relocAddrs, List.any_eq_true, List.mem_flatMap, List.mem_map,
    List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨e, he, r, hr, i, hi, rfl⟩
    exact ⟨e, he, r, hr, i, hi, rfl⟩
  · rintro ⟨e, he, r, hr, i, hi, h⟩
    exact ⟨e, he, r, hr, i, hi, (BitVec.eq_of_toNat_eq h).symm⟩

/-- `gotTabB` as the compiler runs it (`gotTabB_eq_fast`, `@[csimp]`, #1145): the relocated
bytes of `T` in a hash set built once (`relocAtB_eq_contains`), so that each byte of a slot is one
lookup instead of a scan of every relocation of the table. -/
def gotTabFastB (T : List (Clif.Function × Art)) (ex : Excerpt) : Bool :=
  match phdrs (exRd ex) with
  | some phs =>
    let m := memIn (exRd ex) phs
    let S := Std.HashSet.ofList (relocAddrs T)
    T.all fun e => e.2.fb.relocs.all fun rl =>
      !decide (rl.type = .adrGotPage) ||
      match readN m 4 (wAt e.2 rl.offset), readN m 4 (wAt e.2 (rl.offset + 4)) with
      | some x0, some x1 =>
        !ldrFormB x1 ||
        (List.range 8).all fun i =>
          let a := BitVec.ofNat 64 (BinCheck.gotOf (wAt e.2 rl.offset).toNat x0 x1) + BitVec.ofNat 64 i
          (roB phs a || relroB phs a) && (m a).isSome && !S.contains a.toNat
      | _, _ => false
  | none => false

@[csimp] theorem gotTabB_eq_fast : @gotTabB = @gotTabFastB := by
  funext T ex
  simp only [gotTabB, gotTabFastB, relocAtB_eq_contains]

/-- The number of GOT pairs (`adrGotPage` relocations whose second word is an `ldr`) `gotTabB`
checks (report only). -/
def gotPairs (T : List (Clif.Function × Art)) (ex : Excerpt) : Nat :=
  match phdrs (exRd ex) with
  | some phs =>
    let m := memIn (exRd ex) phs
    T.foldl (fun n e => e.2.fb.relocs.foldl (fun n rl =>
      if rl.type = .adrGotPage then
        match readN m 4 (wAt e.2 (rl.offset + 4)) with
        | some x1 => if ldrFormB x1 then n + 1 else n
        | none => n
      else n) n) 0
  | none => 0

end E2E.GotTab

namespace E2E.SemanticExecBytes

open Backend E2E.LinkCheck E2E.BinCheck Elf E2E.GotTab

/-- **`gotTabB` decides `GotOk`** of the typed Stock and return-pin exec-word theorems. -/
theorem gotTabB_sound {I : SemanticStackBound.CompilerInput} {file : ByteArray} {ex : Excerpt}
    (h : gotTabB (tabOf I.results) ex = true) (hA : Agrees file ex) : GotOk I file := by
  unfold gotTabB at h
  split at h
  · rename_i phs hp
    have hm := memIn_ext hA hp
    rintro a ⟨e, he, rl, hrl, ht, rd, G, hrd, h8, hin, hw0, hw1, i, hi, rfl⟩
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 h e he) rl hrl
    simp only [ht, decide_true, Bool.not_true, Bool.false_or] at h1
    split at h1
    · rename_i x0 x1 e0 e1
      have e0' : x0 = adrpW rd (BinCheck.pageOf G - BinCheck.pageOf (wAt e.2 rl.offset).toNat) := by
        have := readN_ext hm e0
        rw [show readN (loadMem file) 4 (wAt e.2 rl.offset) = fileWord file (wAt e.2 rl.offset)
          from rfl, hw0] at this
        cases this; rfl
      have e1' : x1 = ldrW rd rd (G % 4096 / 8) := by
        have := readN_ext hm e1
        rw [show readN (loadMem file) 4 (wAt e.2 (rl.offset + 4)) =
          fileWord file (wAt e.2 (rl.offset + 4)) from rfl, hw1] at this
        cases this; rfl
      subst e0' e1'
      rw [ldrFormB_ldrW (by omega) (by omega), Bool.not_true, Bool.false_or] at h1
      have h2 := List.all_eq_true.1 h1 i (List.mem_range.2 hi)
      rw [gotOf_pair (rd := rd) (by omega) h8 hin] at h2
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h2
      obtain ⟨⟨hro, hsome⟩, hrel⟩ := h2
      refine ⟨?_, ?_, not_relocAt_of hrel⟩
      · rcases hro with hro | hro
        · exact .inl (roB_sound hA hp hro)
        · exact .inr (relroB_sound hA hp hro)
      · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hsome
        simp [hm _ _ hb]
    · cases h1
  · cases h

end E2E.SemanticExecBytes

namespace E2E.DeadCleanupExecBytes

open Backend E2E.LinkCheck E2E.BinCheck Elf E2E.GotTab

/-- **`gotTabB` decides `GotOk`** of the typed cleanup exec-word theorems. -/
theorem gotTabB_sound {I : LinkInput} {file : ByteArray} {ex : Excerpt}
    (h : gotTabB (tabOf I.resultsCleanup) ex = true) (hA : Agrees file ex) : GotOk I file := by
  unfold gotTabB at h
  split at h
  · rename_i phs hp
    have hm := memIn_ext hA hp
    rintro a ⟨e, he, rl, hrl, ht, rd, G, hrd, h8, hin, hw0, hw1, i, hi, rfl⟩
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 h e he) rl hrl
    simp only [ht, decide_true, Bool.not_true, Bool.false_or] at h1
    split at h1
    · rename_i x0 x1 e0 e1
      have e0' : x0 = adrpW rd (BinCheck.pageOf G - BinCheck.pageOf (wAt e.2 rl.offset).toNat) := by
        have := readN_ext hm e0
        rw [show readN (loadMem file) 4 (wAt e.2 rl.offset) = fileWord file (wAt e.2 rl.offset)
          from rfl, hw0] at this
        cases this; rfl
      have e1' : x1 = ldrW rd rd (G % 4096 / 8) := by
        have := readN_ext hm e1
        rw [show readN (loadMem file) 4 (wAt e.2 (rl.offset + 4)) =
          fileWord file (wAt e.2 (rl.offset + 4)) from rfl, hw1] at this
        cases this; rfl
      subst e0' e1'
      rw [ldrFormB_ldrW (by omega) (by omega), Bool.not_true, Bool.false_or] at h1
      have h2 := List.all_eq_true.1 h1 i (List.mem_range.2 hi)
      rw [gotOf_pair (rd := rd) (by omega) h8 hin] at h2
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h2
      obtain ⟨⟨hro, hsome⟩, hrel⟩ := h2
      refine ⟨?_, ?_, not_relocAt_of hrel⟩
      · rcases hro with hro | hro
        · exact .inl (roB_sound hA hp hro)
        · exact .inr (relroB_sound hA hp hro)
      · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hsome
        simp [hm _ _ hb]
    · cases h1
  · cases h

end E2E.DeadCleanupExecBytes
