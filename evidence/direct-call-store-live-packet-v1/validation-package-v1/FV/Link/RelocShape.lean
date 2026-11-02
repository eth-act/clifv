import FV.Link.Reloc

/-! # The linker's relocation check split: shapes and ranges (L1)

`relocOkB I tp a r` (`FV/Link/Reloc.lean`) is a conjunction of

* **the shape** `relocShapeB a r`: properties of the compiled code alone — the relocation is at a
  word of `a`, the compiled words it patches have the resolved form's shape with zero immediates
  (`bl 0`, `adrp rd, 0` with `rd < 31` followed by `ldr rd, [rd]`/`add rd, rd, #0`), its partners
  are there (the pair's second word with the same symbol and addend, the four words of the TLS
  descriptor sequence);
* **the range** `relocRangeB I tp a r`: properties of the addresses — a call's target within
  `bl`'s ±128 MiB, a page pair's target page within `adrp`'s ±4 GiB, a TLS symbol's
  thread-pointer offset known and below `2 ^ 32`.

`relocOkB_of`: shape and range give `relocOkB`; `relocsOkB_of`: with one relocation per offset
(`relocShapesB`), for all of `a`'s relocations.
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck Backend

/-- **The shape of a relocation** of `a` (the part of `relocOkB` about the compiled code). -/
def relocShapeB (a : Art) (r : Reloc) : Bool :=
  let o := r.offset
  let n := a.fb.words.size
  o % 4 == 0 && decide (o / 4 < n) && match r.type with
  | .call26 => wordOf a (o / 4) == blW 0
  | .adrGotPage | .adrPrelPgHi21 =>
    let got := decide (r.type = .adrGotPage)
    let rd := rd5 (wordOf a (o / 4))
    decide (rd < 31) && decide (o / 4 + 1 < n) && wordOf a (o / 4) == adrpW rd 0 &&
      wordOf a (o / 4 + 1) == (if got then ldrW rd rd 0 else addW rd rd 0) &&
      a.fb.relocs.any (fun r' => r'.offset == o + 4 && decide (r'.type = loOf r.type) &&
        r'.sym == r.sym && r'.addend == r.addend)
  | .ld64GotLo12Nc | .addAbsLo12Nc =>
    a.fb.relocs.any fun r' => r'.offset + 4 == o &&
      decide (r'.type = .adrGotPage ∨ r'.type = .adrPrelPgHi21)
  | .tlsDescAdrPage21 =>
    decide (o / 4 + 3 < n) && hasAt a (o + 4) .tlsDescLd64Lo12 && hasAt a (o + 8) .tlsDescAddLo12 &&
      hasAt a (o + 12) .tlsDescCall
  | .tlsDescLd64Lo12 => hasAt a (o - 4) .tlsDescAdrPage21 && decide (4 ≤ o)
  | .tlsDescAddLo12 => hasAt a (o - 8) .tlsDescAdrPage21 && decide (8 ≤ o)
  | .tlsDescCall => hasAt a (o - 12) .tlsDescAdrPage21 && decide (12 ≤ o)

/-- **The shapes of `a`'s relocations**: one per offset, each `relocShapeB`. -/
def relocShapesB (a : Art) : Bool :=
  decide (a.fb.relocs.map (·.offset)).Nodup && a.fb.relocs.all (relocShapeB a)

/-- **The range of a relocation** of `a` (the part of `relocOkB` about the addresses). -/
def relocRangeB (I : LinkInput) (tp : Nat → Option Nat) (a : Art) (r : Reloc) : Bool :=
  match r.type with
  | .call26 => blRange ((I.baseOf r.sym : Int) - (wAt a r.offset).toNat)
  | .adrGotPage | .adrPrelPgHi21 =>
    inR (-2 ^ 20) (2 ^ 20) (pageOf (target I r) - pageOf (wAt a r.offset).toNat)
  | .tlsDescAdrPage21 =>
    match tp (I.addrOf r.sym) with
    | some v => decide (v < 2 ^ 32)
    | none => false
  | _ => true

theorem relocOkB_of {I : LinkInput} {tp : Nat → Option Nat} {a : Art} {r : Reloc}
    (hs : relocShapeB a r = true) (hr : relocRangeB I tp a r = true) : relocOkB I tp a r = true := by
  obtain ⟨o, ty, sym, add⟩ := r
  cases ty <;> dsimp only [relocShapeB, relocRangeB, relocOkB] at hs hr ⊢ <;>
    simp only [Bool.and_eq_true] at hs hr ⊢ <;> first | exact ⟨hs.1, hs.2, hr⟩ | exact hs

theorem relocsOkB_of {I : LinkInput} {tp : Nat → Option Nat} {a : Art}
    (hs : relocShapesB a = true) (hr : ∀ r ∈ a.fb.relocs, relocRangeB I tp a r = true) :
    relocsOkB I tp a = true := by
  simp only [relocShapesB, relocsOkB, Bool.and_eq_true, List.all_eq_true] at hs ⊢
  exact ⟨hs.1, fun r h => relocOkB_of (hs.2 r h) (hr r h)⟩

end Link
