import FV.Link.DeadCleanupImage
import FV.Link.OutsideProof
namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec
abbrev placedArts (S : LinkSpec) : List Art :=
  ((tabOf S.inputCleanup.resultsCleanupT).take S.funcs.length).map (·.2)

/-- The region's bytes the linker writes. -/
abbrev regionOf (S : LinkSpec) (tp : Nat → Option Nat) : ByteArray :=
  ByteArray.mk (regionBytes S.inputCleanup tp (placedArts S)).toArray

/-- `leanLink`'s checks and result, unfolded (`S.inputCleanup` is the input `leanLink` builds from one
run of the pipeline). -/
theorem leanLink_spec {S : LinkSpec} {file0 file : ByteArray} (h : leanLink S file0 = .ok file) :
    ∃ phs, phdrs (fileRd file0) = some phs ∧ S.placeOkB = true ∧
      S.inputCleanup.resultsCleanupT.all (·.2.toBool) = true ∧
      S.namesOkB (tabOf S.inputCleanup.resultsCleanupT) = true ∧
      S.sizesOkB (tabOf S.inputCleanup.resultsCleanupT) = true ∧
      (tabOf S.inputCleanup.resultsCleanupT).all (fun e => relocsOkB S.inputCleanup (tpOff phs) e.2) = true ∧
      codeMapB S.inputCleanup (tabOf S.inputCleanup.resultsCleanupT) = true ∧
      regionOkB file0 S.R (regionOf S (tpOff phs)).size (offsetOf phs S.R) = true ∧
      outsideOkB S.inputCleanup S.data file = true ∧
      file = patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs)) := by
  unfold leanLink at h
  split at h
  · cases h
  rename_i phs hph
  dsimp only at h
  rw [parResultsCleanupT_eq] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hp hr hn hs hv hcm hok hout
  cases h
  exact ⟨phs, hph, of_not_not hp, of_not_not hr, of_not_not hn, of_not_not hs, of_not_not hv,
    of_not_not hcm, of_not_not hok, of_not_not hout, rfl⟩

/-- **`leanLink`'s output is a static executable** (its headers are checked: `outsideOkB`). -/
theorem leanLink_static' {S : LinkSpec} {file0 file : ByteArray}
    (h : leanLink S file0 = .ok file) : Static file := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hout, -⟩ := leanLink_spec h
  exact outsideOkB_static hout


end Link.DeadCleanup
