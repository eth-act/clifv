import FV.Link.ExeInputReach
import FV.Link.ExeInputCleanup

/-! # The shipped compiler is total on decidable input conditions, relocation reach included (L1e)

`Link.compileExe_total_reach` (`FV/Link/ExeInputReach.lean`) for the compiler `lean-link` ships,
`Link.DeadCleanup.compileExe`: its layout is `DeadCleanup.placed S`, its relocations have their
function's references through the cleanup pipeline too (`DeadCleanup.prune` only drops
instructions), and `reachOkB` of that layout gives `DeadCleanup.CallPageReach`. Composes
`Link.DeadCleanup.compileExe_total_input`; the cleanup files are unchanged.
-/

namespace Link.DeadCleanup

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec

/-- **`DeadCleanup.CallPageReach` from provenance and reach** (`callPageReach_of_prov` for the
shipped compiler). -/
theorem callPageReach_of_prov {S : LinkSpec} {phs : List Phdr} (hin : InScopeP (placed S).input0 = true)
    (hl : (placed S).layoutOkB = true) (hreach : (placed S).reachOkB = true)
    (hprov : ∀ e ∈ tabOf (placed S).inputCleanup.resultsCleanupT, ∀ r ∈ e.2.fb.relocs,
      Proof.RelocProv.RelocOk e.1 r) :
    CallPageReach S phs := by
  intro e he r hr htls
  have hp := placeOkB_placed hin hl
  have hP := placeOk_of hp
  have hpc := pc_of_placed hP (tab_length _)
    (fun i hi => by
      obtain ⟨e, h1, h2, h3, -, -⟩ :=
        tab_placed hp (results_of hin) (names_of rfl) (sizes_of rfl) i hi
      exact ⟨e, h1, h2, h3⟩)
    (shapes_of hin) e he r hr
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
  obtain ⟨fi, hfi, h1, -⟩ := mem_resultsCleanupT he0
  have hf : (placed S).refsReachB fi.func = true := List.all_eq_true.1 hreach fi hfi
  rw [← h1] at hf
  exact range_of_refs rfl rfl hf hpc.1 hpc.2.1 hpc.2.2 (hprov _ he r hr) _ htls

/-- **The shipped compiler's code relocates against its CLIF function's declarations**
(`relocOk_tab` through the cleanup stage `cleanupStage`, `cleanupStage_insts`). -/
theorem relocOk_tab {S : LinkSpec} (hin : InScopeP (placed S).input0 = true) :
    ∀ e ∈ tabOf (placed S).inputCleanup.resultsCleanupT, ∀ r ∈ e.2.fb.relocs,
      Proof.RelocProv.RelocOk e.1 r := by
  have hr := results_of hin
  intro e he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
  obtain ⟨fi, hfi, h1, h2⟩ := mem_resultsCleanupT he0
  have hok := getOk_eq (List.all_eq_true.1 hr e0 he0)
  rw [h2] at hok
  obtain ⟨hlf, hpr, -, hal, hem, hla, -⟩ := pipeCleanupT_spec hok
  have hv := Proof.RelocProv.lowerFunction_refs
    (lowerScope_of_fnScope (fnScope_of_inScope (S := S) hin hfi)) hlf
  have hv' := Proof.RelocProv.prepare_allInsts (fun _ => trivial)
    (fun _ _ _ h => Proof.RelocProv.refsOk_setTargets h) hpr (Proof.Driver.cleanupStage_insts _ hv)
  show ∀ r ∈ (getOk e0.2).fb.relocs, Proof.RelocProv.RelocOk e0.1 r
  rw [h1, h2]
  exact Proof.RelocProv.relocs_of_alloc hv' hal hem hla

/-- **`DeadCleanup.CallPageReach` holds under `reachOkB`.** -/
theorem callPageReach_of {S : LinkSpec} {phs : List Phdr} (hin : InScopeP (placed S).input0 = true)
    (hl : (placed S).layoutOkB = true) (hreach : (placed S).reachOkB = true) : CallPageReach S phs :=
  callPageReach_of_prov hin hl hreach (relocOk_tab hin)

/-- **The shipped compiler succeeds on decidable input conditions** (`compileExe_total_reach` for
`DeadCleanup.compileExe`). -/
theorem compileExe_total_reach {S : LinkSpec} {file0 : ByteArray} {phs : List Phdr}
    (hin : InScopeP (placed S).input0 = true) (hl : (placed S).layoutOkB = true)
    (hph : phdrs (fileRd file0) = some phs) (hf : (placed S).file0OkB file0 phs = true)
    (hreach : (placed S).reachOkB = true) :
    compileExe (placed S) file0 =
      .ok (patch file0 (offsetOf phs S.R) (regionOf (placed S) (tpOff phs))) :=
  compileExe_total_input hin hl hph hf (callPageReach_of hin hl hreach)

end Link.DeadCleanup
