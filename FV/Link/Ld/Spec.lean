import FV.Link.Ld.Data

/-! # `file0OkB` of `lean-ld`'s output from its plan (L2b stage 3e)

`LinkSpec.file0OkB` is what the executable compiler's totality theorems ask of the executable
`file0` the outside part was linked into. On `lean-ld`'s output it holds whenever the link
succeeds and the link spec agrees with the plan (`Plan.specOkB`, decided on the plan and the
spec, reading no byte of the output):

* the region `[R, R + size)` lies in the `R E` segment's file bytes (`Plan.regionInB`);
* every link-map entry is one of the plan's symbols (`symsPlanB`);
* every link-map address has a thread-pointer offset below `2 ^ 32` (`tlsBoundB`);
* the CLIF data objects are in the plan (`dataPlanB`, `FV/Link/Ld/Data.lean`).

The plan's own conditions (`Plan.okB`), checked by `assemble`, and the writer give the rest:
`staticB_phdrs`, `regionPhsB_plan`, `tpOff_phdrs` (`FV/Link/Ld/PlanProof.lean`),
`symsOkB_write` (`FV/Link/Ld/Syms.lean`), `dataFastB_plan`.

* **`file0OkB_assemble`**: `file0OkB` of the written image of a plan;
* **`file0OkB_ld`**: `file0OkB` of `lean-ld`'s output (`link o ins = .ok r`).
-/

namespace Link.Ld

open E2E E2E.Elf E2E.BinCheck E2E.LinkCheck Link

/-- The index of the first symbol of each name and value. -/
def symHint (syms : Array OutSym) : Std.HashMap (String × Nat) Nat :=
  (List.range syms.size).foldl (fun m k => match syms[k]? with
    | some s => m.insertIfNew (s.name, s.value) k
    | none => m) {}

/-- **Every link-map entry is a symbol of the plan** (name and value; self-call aliases
excepted). -/
def symsPlanB (I : LinkInput) (pl : Plan) : Bool :=
  let idx := symHint pl.syms
  I.addrs.all fun p => (I.aliases.lookup p.1).isSome ||
    match idx[(symName p.1, p.2)]?.bind (pl.syms[·]?) with
    | some s => s.name == symName p.1 && s.value == p.2
    | none => false

/-- **The link map's addresses have thread-pointer offsets below `2 ^ 32`.** -/
def tlsBoundB (P : LinkSpec) (pl : Plan) : Bool :=
  (0 :: P.addrs.map (·.2)).all fun v => decide (tlsBase pl.tlsAlign + v < 2 ^ 32)

/-- **The link spec's conditions on `lean-ld`'s plan**: the region in the `R E` segment's file
bytes, the link map's symbols, the TLS offsets, the CLIF data objects. -/
def Plan.specOkB (pl : Plan) (P : LinkSpec) : Bool :=
  pl.regionInB P.R P.size && symsPlanB P.input0 pl && tlsBoundB P pl &&
    dataPlanB P.input0 P.data pl (offsetOf pl.phdrs P.R) P.size

theorem symsPlanB_sound {I : LinkInput} {pl : Plan} (h : symsPlanB I pl = true) :
    ∀ p ∈ I.addrs, (I.aliases.lookup p.1).isSome = true ∨
      ∃ k, ∃ hk : k < pl.syms.size, pl.syms[k].name = symName p.1 ∧ pl.syms[k].value = p.2 := by
  intro p hp
  have := List.all_eq_true.1 h p hp
  simp only [Bool.or_eq_true] at this
  rcases this with ha | hs
  · exact .inl ha
  · refine .inr ?_
    revert hs
    cases hb : (symHint pl.syms)[(symName p.1, p.2)]?.bind (pl.syms[·]?) with
    | none => intro hs; cases hs
    | some s =>
      intro hs
      simp only [Bool.and_eq_true, beq_iff_eq] at hs
      obtain ⟨k, -, hk⟩ := Option.bind_eq_some_iff.1 hb
      obtain ⟨hkl, rfl⟩ := Array.getElem?_eq_some_iff.1 hk
      exact ⟨k, hkl, hs.1, hs.2⟩

theorem tlsOkB_plan {P : LinkSpec} {pl : Plan} (h : tlsBoundB P pl = true) : tlsOkB P pl.phdrs = true := by
  unfold tlsOkB
  simp only [List.all_eq_true, tpOff_phdrs]
  exact fun v hv => List.all_eq_true.1 h v hv

/-- **`file0OkB` of the written image of a plan** satisfying the link spec's conditions. -/
theorem file0OkB_assemble {pl : Plan} {img : Img} (ha : assemble pl = .ok img)
    (hfit : img.hdrFitsB = true) (htab : img.tabsFitB = true) {P : LinkSpec}
    (hP : pl.specOkB P = true) : P.file0OkB img.write img.phs = true := by
  obtain ⟨hok, hbody, hphs, -, -, hsyms⟩ := assemble_ok ha
  simp only [Plan.specOkB, Bool.and_eq_true] at hP
  obtain ⟨⟨⟨hreg, hsy⟩, htl⟩, hdat⟩ := hP
  have hbs := buildBody_size hbody
  have hoff := offsetOf_plan hok hreg
  have hws : img.body.size ≤ img.write.size := by rw [write_size, pad8_size]; omega
  have hhi : offsetOf img.phs P.R + P.size ≤ img.tabs.symOff := by
    rw [tabs_symOff, pad8_size, hphs]; omega
  rw [file0OkB_write hfit htab P hhi]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hphs]; exact regionPhsB_plan hok hreg (by omega)
  · rw [hphs]; exact staticB_phdrs hok rfl rfl
  · rw [hphs]; exact dataFastB_plan ha hfit hoff.1 hdat
  · exact symsOkB_write hfit htab P.input0 (hsyms ▸ symsPlanB_sound hsy)
  · rw [hphs]; exact tlsOkB_plan htl

/-- **`file0OkB` of `lean-ld`'s output**: a successful link whose plan satisfies the link spec's
conditions (`Plan.specOkB`). -/
theorem file0OkB_ld {o : Opts} {ins : List Input} {r : LinkOut} (h : link o ins = .ok r)
    {P : LinkSpec} (hP : r.plan.specOkB P = true) : P.file0OkB r.img.write r.img.phs = true :=
  have ⟨ha, hfit, htab⟩ := link_ok h
  file0OkB_assemble ha hfit htab hP

/-! ## Non-vacuity

A plan of one `R E` segment with the headers, an empty region, and a piece holding a CLIF data
object of eight bytes and an address item (patched by an `ABS64`). -/

/-- The data object's piece: 16 input bytes, an `ABS64` at offset 8 against `0x200180`. -/
def tinyDataPiece : Piece :=
  { addr := 0x200180, fo := 0x180, bytes := ⟨Array.replicate 16 7⟩,
    rels := [{ off := 8, ty := 257, ri := { S := 0x200180, A := 0, P := 0x200188 } }] }

def tinyPlan : Plan :=
  { base := 0x200000, entry := 0x200160,
    segs := [{ kind := 1, vaddr := 0x200000, offset := 0, filesz := 0x200, memsz := 0x200 }],
    tlsAddr := 0x200200, tlsOff := 0x200, tlsFilesz := 0, tlsMemsz := 0, tlsAlign := 1,
    ehOff := 0, ehAddr := 0, ehSize := 0, size := 0x200, pieces := [tinyDataPiece], secs := #[],
    syms := #[{ name := "d", value := 0x200180, info := 17, shndx := 0xfff1 }] }

/-- The CLIF data object `d`: eight bytes `7`, then its own address. -/
def tinyData : Clif.DataObject := { name := "d", items := List.replicate 8 (.byte 7) ++ [.addr "d" 0] }

/-- A link spec without program functions: the region `[0x200160, 0x200160)`, the object `d`. -/
def tinySpec : LinkSpec :=
  { funcs := [], names := [], sizes := [], outside := [("d", 0x200180)], data := [tinyData],
    symNames := [], R := 0x200160 }

theorem tinyPlan_okB : tinyPlan.okB = true := by decide +kernel

theorem staticB_phdrs_witness :
    staticB ⟨2, 183, 0x200160, 64, 0, 5, 4⟩ tinyPlan.phdrs = true :=
  staticB_phdrs tinyPlan_okB rfl rfl

theorem tinyPlan_regionIn : tinyPlan.regionInB 0x200160 0 = true := by decide +kernel

theorem regionPhsB_plan_witness :
    regionPhsB tinyPlan.phdrs 0x200160 0 (offsetOf tinyPlan.phdrs 0x200160) 0x200 = true :=
  regionPhsB_plan tinyPlan_okB tinyPlan_regionIn (Nat.le_refl _)

theorem tinyPlan_specOkB : tinyPlan.specOkB tinySpec = true := by native_decide

/-- **`file0OkB_assemble`'s premises hold together**: the tiny plan assembles into an image whose
headers and tables fit, and its written file passes `file0OkB` (the data object checked through
`dataPlanB`). -/
theorem file0OkB_assemble_witness :
    ∃ img, assemble tinyPlan = .ok img ∧ tinySpec.file0OkB img.write img.phs = true := by
  have h : (match assemble tinyPlan with
    | .ok img => img.hdrFitsB && img.tabsFitB
    | .error _ => false) = true := by native_decide
  split at h
  · rename_i img ha
    simp only [Bool.and_eq_true] at h
    exact ⟨img, ha, file0OkB_assemble ha h.1 h.2 tinyPlan_specOkB⟩
  · cases h

/-- **`dataFastB_plan`'s premises hold together** (a data object with byte and address items). -/
theorem dataFastB_plan_witness :
    ∃ img, assemble tinyPlan = .ok img ∧
      dataFastB tinySpec.input0 [tinyData] (maskEx img.write 0x160 0) = true := by
  have h : (match assemble tinyPlan with
    | .ok img => img.hdrFitsB
    | .error _ => false) = true := by native_decide
  split at h
  · rename_i img ha
    exact ⟨img, ha, dataFastB_plan ha h (by decide +kernel) (by native_decide)⟩
  · cases h

end Link.Ld
