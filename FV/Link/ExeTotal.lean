import FV.Link.Total
import FV.Link.RelocShapeProof

/-! # The executable compiler is total on its scope (L1)

**`compileExe_total`**: `compileExe S file0` succeeds — with the executable `leanLink` writes —
on every input satisfying

* the input conditions `InScopeP` (decided on the CLIF program alone; `compileExe` checks them);
* the driver's data: the placement's conditions (`placeOkB`), the names and sizes are the CLIF
  functions' and their compiled code's (`LinkSpec.sizesOf`);
* the addresses: every relocation's target in its instruction's reach (`relocRangeB`: `bl`
  ±128 MiB, `adrp` ±4 GiB, a TLS symbol's thread-pointer offset below `2 ^ 32`);
* rust-lld's output: program headers, `regionOkB` on `file0`, `outsideOkB` on the written file.

The compiler's own outputs need nothing: the pipeline succeeds (`pipeT_ok`, definite assignment
proven), the relocations have their shapes (`relocShapes_of_pipeT`), the code map holds by
construction (`codeMap_place`).
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec

/-- The compiled code's relocations have their shapes (`relocShapes_of_pipeT`). -/
theorem shapes_of {S : LinkSpec} (hin : InScopeP S.input0 = true) :
    ∀ e ∈ tabOf S.input.resultsT, relocShapesB e.2 = true := by
  have hr := results_of hin
  intro e he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
  obtain ⟨fi, -, -, h2⟩ := mem_resultsT he0
  have hok := getOk_eq (List.all_eq_true.1 hr e0 he0)
  show relocShapesB (getOk e0.2) = true
  rw [h2] at hok ⊢
  exact relocShapes_of_pipeT hok

/-- **The executable compiler succeeds on its scope.** -/
theorem compileExe_total {S : LinkSpec} {file0 : ByteArray} {phs : List Phdr}
    (hin : InScopeP S.input0 = true) (hp : S.placeOkB = true)
    (hn : S.names = S.funcs.map (·.func.name)) (hs : S.sizes = S.sizesOf)
    (hrange : ∀ e ∈ tabOf S.input.resultsT, ∀ r ∈ e.2.fb.relocs,
      relocRangeB S.input (tpOff phs) e.2 r = true)
    (hph : phdrs (fileRd file0) = some phs)
    (hreg : regionOkB file0 S.R (regionOf S (tpOff phs)).size (offsetOf phs S.R) = true)
    (hout : outsideOkB S.input S.data (patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs))) =
      true) :
    compileExe S file0 = .ok (patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs))) := by
  have h := leanLink_total_of hph hin hp hn hs (shapes_of hin) hrange hreg hout
  simp only [compileExe, inScopePar_eq, hin, ↓reduceIte]
  exact h

end Link
