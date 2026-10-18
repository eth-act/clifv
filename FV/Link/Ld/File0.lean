import FV.Link.Ld.WriteProof
import FV.Link.Ld.Syms
import FV.Link.ExeInput

/-! # `file0OkB` of the Lean linker's output (L2b stage 3b)

`LinkSpec.file0OkB` (`FV/Link/ExeInput.lean`) is what the totality theorems
(`compileExe_total_input`, `compileExe_total_reach`, …) ask of the executable `file0` the
outside part was linked into. On a file written by `Img.write` (`lean-ld`'s writer) it reduces to
conditions on the image description and the link map:

* `hdrB_write`: the headers are a static AArch64 executable's iff `staticB` holds of the image's
  program headers;
* `regionOkB_write`: the region condition is `regionPhsB` of the program headers;
* `symFootB_write`: everything a symbol lookup reads lies after the segments' bytes, for every
  bound `hi` up to the end of the body (always: the writer puts the tables after it);
* `file0OkB_write`: `file0OkB` is `regionPhsB`, `staticB`, the data check and the symbol check
  (on the file), and `tlsOkB` (on the program headers);
* `file0OkB_write_syms`: with every link-map entry a written symbol (`symsOkB_write`,
  `FV/Link/Ld/Syms.lean`), `file0OkB` is `regionPhsB`, `staticB`, the data check and `tlsOkB`.
-/

namespace Link.Ld

open E2E E2E.Elf E2E.BinCheck E2E.LinkCheck Link

/-- **The region condition on program headers**: `regionOkB`'s body with the ELF header
`lean-ld` writes (`e_phoff = 64`). -/
def regionPhsB (phs : List Phdr) (R n off size : Nat) : Bool :=
  decide (64 ≤ off) && decide (64 + 56 * phs.length ≤ off) && decide (off + n ≤ size) &&
    match segIn phs R with
    | some p => notW p && decide (R + n ≤ p.vaddr + p.filesz) && decide (p.filesz ≤ p.memsz) &&
        decide (off = p.offset + (R - p.vaddr)) &&
        phs.all fun q => q == p || q.type != 1 || decide (q.vaddr + q.memsz ≤ R) ||
          decide (R + n ≤ q.vaddr)
    | none => false

theorem hdrB_write {img : Img} (h : img.hdrFitsB = true) :
    hdrB [(0, img.write)] = staticB ⟨2, 183, img.entry, 64, img.tabs.shoff, img.phs.length,
      img.secs.size + 4⟩ img.phs := by
  simp only [hdrB, exRd_self, ehdr_write h, phdrs_write h]

theorem regionOkB_write {img : Img} (h : img.hdrFitsB = true) (R n off : Nat) :
    regionOkB img.write R n off = regionPhsB img.phs R n off img.write.size := by
  simp only [regionOkB, ehdr_write h, phdrs_write h, regionPhsB]
  cases segIn img.phs R <;> rfl

/-- **The symbol tables lie after the body.** -/
theorem symFootB_write {img : Img} (h : img.hdrFitsB = true) (ht : img.tabsFitB = true) {hi : Nat}
    (hhi : hi ≤ img.tabs.symOff) : symFootB img.write hi = true := by
  have hge := tabs_shoff_ge img
  have hsym : img.tabs.symOff ≤ img.tabs.shoff := by simp only [Img.tabs] at hge ⊢; omega
  have hstr : img.tabs.symOff ≤ img.tabs.strOff := by simp only [Img.tabs]; omega
  have hty : ∀ k (hk : k < img.secs.size), img.secs[k].type ≠ 2 := by
    simp only [Img.tabsFitB, Bool.and_eq_true, Array.all_eq_true] at ht
    intro k hk
    have := ht.1.2 k hk
    simpa using this
  unfold symFootB
  simp only [ehdr_write h, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨by omega, fun s hs => ?_⟩
  obtain ⟨o3, h3⟩ := shdrList_str img img.tabs
  rcases (show s = 0 ∨ (1 ≤ s ∧ s ≤ img.secs.size) ∨ s = img.secs.size + 1 ∨
      s = img.secs.size + 2 ∨ s = img.secs.size + 3 by omega) with
    rfl | ⟨h1, h2⟩ | rfl | rfl | rfl
  · rw [shdr_write h ht (shdrList_zero img img.tabs)]; rfl
  · obtain ⟨o, ho⟩ := shdrList_sec img img.tabs (k := s - 1) (by omega)
    rw [show s = s - 1 + 1 by omega, shdr_write h ht ho]
    simp [hty (s - 1) (by omega)]
  · obtain ⟨o, ho⟩ := shdrList_sym img img.tabs
    rw [shdr_write h ht ho]
    simp only [shdr_write h ht h3]
    simp; omega
  · rw [shdr_write h ht h3]; simp
  · obtain ⟨o, ho⟩ := shdrList_shs img img.tabs
    rw [shdr_write h ht ho]; simp

/-- **`file0OkB` of `lean-ld`'s output**: the region and header conditions on the program
headers, the data and symbol checks, `tlsOkB`; `symFootB` holds (the tables follow the body). -/
theorem file0OkB_write {img : Img} (h : img.hdrFitsB = true) (ht : img.tabsFitB = true)
    (P : LinkSpec) (hhi : offsetOf img.phs P.R + P.size ≤ img.tabs.symOff) :
    P.file0OkB img.write img.phs =
      (regionPhsB img.phs P.R P.size (offsetOf img.phs P.R) img.write.size &&
        staticB ⟨2, 183, img.entry, 64, img.tabs.shoff, img.phs.length, img.secs.size + 4⟩ img.phs &&
        dataFastB P.input0 P.data (maskEx img.write (offsetOf img.phs P.R) P.size) &&
        symsOkB P.input0 img.write && tlsOkB P img.phs) := by
  simp only [LinkSpec.file0OkB, regionOkB_write h, hdrB_write h, symFootB_write h ht hhi,
    Bool.and_true]

/-- **`file0OkB` of `lean-ld`'s output, the symbol check discharged**: every link-map entry is a
written symbol (name and value). -/
theorem file0OkB_write_syms {img : Img} (h : img.hdrFitsB = true) (ht : img.tabsFitB = true)
    (P : LinkSpec) (hhi : offsetOf img.phs P.R + P.size ≤ img.tabs.symOff)
    (hP : ∀ p ∈ P.addrs, ∃ k, ∃ hk : k < img.syms.size,
      img.syms[k].name = symName p.1 ∧ img.syms[k].value = p.2) :
    P.file0OkB img.write img.phs =
      (regionPhsB img.phs P.R P.size (offsetOf img.phs P.R) img.write.size &&
        staticB ⟨2, 183, img.entry, 64, img.tabs.shoff, img.phs.length, img.secs.size + 4⟩ img.phs &&
        dataFastB P.input0 P.data (maskEx img.write (offsetOf img.phs P.R) P.size) &&
        tlsOkB P img.phs) := by
  rw [file0OkB_write h ht P hhi, symsOkB_write h ht P.input0 fun p hp => Or.inr (hP p hp),
    Bool.and_true]

/-! ## Non-vacuity -/

theorem tinyImg_tabsFit : tinyImg.tabsFitB = true := by decide +kernel

theorem symFootB_write_witness : symFootB tinyImg.write tinyImg.tabs.symOff = true :=
  symFootB_write tinyImg_hdrFits tinyImg_tabsFit (Nat.le_refl _)

theorem file0OkB_write_witness (P : LinkSpec) (hR : P.R = 0) (hs : P.size = 0) :
    P.file0OkB tinyImg.write tinyImg.phs =
      (regionPhsB tinyImg.phs P.R P.size (offsetOf tinyImg.phs P.R) tinyImg.write.size &&
        staticB ⟨2, 183, tinyImg.entry, 64, tinyImg.tabs.shoff, tinyImg.phs.length,
          tinyImg.secs.size + 4⟩ tinyImg.phs &&
        dataFastB P.input0 P.data (maskEx tinyImg.write (offsetOf tinyImg.phs P.R) P.size) &&
        symsOkB P.input0 tinyImg.write && tlsOkB P tinyImg.phs) :=
  file0OkB_write tinyImg_hdrFits tinyImg_tabsFit P (by rw [hR, hs]; decide +kernel)

theorem file0OkB_write_syms_witness (P : LinkSpec) (hR : P.R = 0) (hs : P.size = 0)
    (hA : P.addrs = [("f", 0x200078)]) :
    P.file0OkB tinySymImg.write tinySymImg.phs =
      (regionPhsB tinySymImg.phs P.R P.size (offsetOf tinySymImg.phs P.R) tinySymImg.write.size &&
        staticB ⟨2, 183, tinySymImg.entry, 64, tinySymImg.tabs.shoff, tinySymImg.phs.length,
          tinySymImg.secs.size + 4⟩ tinySymImg.phs &&
        dataFastB P.input0 P.data (maskEx tinySymImg.write (offsetOf tinySymImg.phs P.R) P.size) &&
        tlsOkB P tinySymImg.phs) :=
  file0OkB_write_syms tinySymImg_hdrFits tinySymImg_tabsFit P (by rw [hR, hs]; decide +kernel)
    fun p hp => by
      rw [hA, List.mem_singleton] at hp
      subst hp
      exact ⟨0, by decide, by native_decide, rfl⟩

end Link.Ld
