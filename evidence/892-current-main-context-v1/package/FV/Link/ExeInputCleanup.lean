import FV.Link.ExeInput
import FV.Link.DeadCleanupExeTotal

/-! # The shipped compiler is total on decidable input conditions (L1e)

`Link.compileExe_total_input` (`FV/Link/ExeInput.lean`) for the compiler `lean-link` ships by
default, `Link.DeadCleanup.compileExe` (dead-instruction cleanup before preparation): its layout is
`DeadCleanup.placed S` (the CLIF functions' names, the cleanup pipeline's sizes `DeadCleanup.sizesOf`),
the conditions on the inputs are the same (`layoutOkB`, `file0OkB` of that layout), the remaining
premise is the `bl`/`adrp` reach of its compiled relocations (`DeadCleanup.CallPageReach`).
Composes `Link.DeadCleanup.compileExe_total`; the cleanup files are unchanged.
-/

namespace Link.DeadCleanup

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec

/-- **The shipped compiler's layout**: the CLIF functions' names, the cleanup pipeline's sizes. -/
def placed (S : LinkSpec) : LinkSpec := S.withSizes (sizesOf S)

/-- The cleanup pipeline's compiled code is nonempty. -/
theorem pipeCleanupT_words_pos {g : Clif.Function} {k : Nat} {b : BitVec 64} {o : Lean.Json}
    {a : Art} (h : pipeCleanupT g k b o = .ok a) (hc : checkAlloc a.vcp a.rf = .ok ()) :
    0 < a.fb.words.size := by
  obtain ⟨-, -, -, hal, hem, hla, -⟩ := pipeCleanupT_spec h
  exact words_pos_of hc hal hem hla

/-- **The placement's conditions hold for the shipped compiler's layout.** -/
theorem placeOkB_placed {S : LinkSpec} (hin : InScopeP (placed S).input0 = true)
    (hl : (placed S).layoutOkB = true) : (placed S).placeOkB = true := by
  refine placeOkB_withSizes (nodup_of_inScope hin) (by simp [sizesOf]) ?_ hl
  intro n hn
  simp only [sizesOf, List.mem_map] at hn
  obtain ⟨fi, hfi, rfl⟩ := hn
  obtain ⟨a, ha, -, -, hc, -⟩ := pipeCleanupT_ok (fnScope_of_inScope hin hfi) spillDefinedHyp
    fi.k 0 (raJ fi.ra fi.j)
  rw [ha]
  exact pipeCleanupT_words_pos ha hc

/-- **The remaining premise**: the `bl` and `adrp` targets of the shipped compiler's code are in
reach. -/
def CallPageReach (S : LinkSpec) (phs : List Phdr) : Prop :=
  ∀ e ∈ tabOf (placed S).inputCleanup.resultsCleanupT, ∀ r ∈ e.2.fb.relocs,
    r.type ≠ .tlsDescAdrPage21 → relocRangeB (placed S).inputCleanup (tpOff phs) e.2 r = true

/-- The region's size is the layout's span. -/
theorem regionOf_placed_size (S : LinkSpec) (tp : Nat → Option Nat) :
    (regionOf (placed S) tp).size = (placed S).size := by
  have hsz := sizes_of (S := placed S) rfl
  simp only [sizesOkB, decide_eq_true_eq] at hsz
  show (regionBytes (placed S).inputCleanup tp (placedArts (placed S))).toArray.size = _
  rw [List.size_toArray, regionBytes_length, placedArts]
  simp only [List.map_map, Function.comp_def] at hsz ⊢
  rw [hsz]
  rfl

/-- **The shipped compiler succeeds on decidable input conditions** (`compileExe_total_input`
for `DeadCleanup.compileExe`). -/
theorem compileExe_total_input {S : LinkSpec} {file0 : ByteArray} {phs : List Phdr}
    (hin : InScopeP (placed S).input0 = true) (hl : (placed S).layoutOkB = true)
    (hph : phdrs (fileRd file0) = some phs) (hf : (placed S).file0OkB file0 phs = true)
    (hreach : CallPageReach S phs) :
    compileExe (placed S) file0 =
      .ok (patch file0 (offsetOf phs S.R) (regionOf (placed S) (tpOff phs))) := by
  simp only [file0OkB, Bool.and_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨hreg, hh⟩, hd⟩, hs⟩, hft⟩, ht⟩ := hf
  have hsz := regionOf_placed_size S (tpOff phs)
  refine compileExe_total hin (placeOkB_placed hin hl) rfl rfl (fun e he r hr => ?_) hph
    (hsz ▸ hreg) (outsideOkB_patch (hsz ▸ hreg) hh (hsz ▸ hd) (by exact hs) (hsz ▸ hft))
  by_cases htls : r.type = .tlsDescAdrPage21
  · exact tls_range rfl ht e.2 htls
  · exact hreach e he r hr htls

/-- **A successful link has the shipped compiler's layout.** -/
theorem placed_of_compileExe {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) : placed S = S := by
  simp only [compileExe, inScopePar_eq] at h
  split at h
  · obtain ⟨-, -, -, -, hn, hs, -⟩ := leanLink_spec h
    simp only [namesOkB, tabOf, LinkInput.resultsCleanupT, inputCleanup_funcs, List.map_map,
      ← List.map_take, List.take_length, Function.comp_def, decide_eq_true_eq] at hn
    simp only [sizesOkB, tabOf, LinkInput.resultsCleanupT, inputCleanup_funcs, List.map_map,
      ← List.map_take, List.take_length, Function.comp_def, decide_eq_true_eq] at hs
    have hs' : sizesOf S = S.sizes := by
      rw [← hs, sizesOf]
      exact List.map_congr_left fun fi _ => by rw [pipeT_fb]
    cases S
    simp only [placed, LinkSpec.withSizes, LinkSpec.mk.injEq] at hn hs' ⊢
    simp only [hn, hs', and_self]
  · cases h

end Link.DeadCleanup
