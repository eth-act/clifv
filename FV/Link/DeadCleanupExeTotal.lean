import FV.Link.DeadCleanupTotal
import FV.Link.DeadCleanupRelocShapeProof
namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec

theorem shapes_of {S : LinkSpec} (hin : InScopeP S.input0 = true) :
    ∀ e ∈ tabOf S.inputCleanup.resultsCleanupT, relocShapesB e.2 = true := by
  have hr := results_of hin
  intro e he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
  obtain ⟨fi, -, -, h2⟩ := mem_resultsCleanupT he0
  have hok := getOk_eq (List.all_eq_true.1 hr e0 he0)
  show relocShapesB (getOk e0.2) = true
  rw [h2] at hok ⊢
  exact relocShapes_of_pipeCleanupT hok

/-- **The executable compiler succeeds on its scope.** -/
theorem compileExe_total {S : LinkSpec} {file0 : ByteArray} {phs : List Phdr}
    (hin : InScopeP S.input0 = true) (hp : S.placeOkB = true)
    (hn : S.names = S.funcs.map (·.func.name)) (hs : S.sizes = sizesOf S)
    (hrange : ∀ e ∈ tabOf S.inputCleanup.resultsCleanupT, ∀ r ∈ e.2.fb.relocs,
      relocRangeB S.inputCleanup (tpOff phs) e.2 r = true)
    (hph : phdrs (fileRd file0) = some phs)
    (hreg : regionOkB file0 S.R (regionOf S (tpOff phs)).size (offsetOf phs S.R) = true)
    (hout : outsideOkB S.inputCleanup S.data (patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs))) =
      true) :
    compileExe S file0 = .ok (patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs))) := by
  have h := leanLink_total_of hph hin hp hn hs (shapes_of hin) hrange hreg hout
  simp only [compileExe, inScopePar_eq, hin, ↓reduceIte]
  exact h


end Link.DeadCleanup
