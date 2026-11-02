import FV.Link.ExeInput
import FV.Backend.Proof.RelocProvDriver
import FV.Backend.Proof.RelocProvEmit

/-! # The executable compiler is total on decidable input conditions, relocation reach included (L1e)

`Link.compileExe_total_input` (`FV/Link/ExeInput.lean`) has one premise not decided on the
inputs: `CallPageReach`, the `bl`/`adrp` reach of the compiled relocations. Here it follows from
a condition on the CLIF functions and the link map, `reachOkB`:

* **name provenance** (`relocOk_tab`): a relocation of the compiled code of `f` relocates against
  `f`'s own declarations (`Backend.Proof.RelocProv.RelocOk`): a `bl` against the name of an
  external function declaration (`fnN = %name(sig)`), an `adrp` pair against a declared name
  (external function or `symbol` global value) with a declared offset (`0` or a global value's
  offset). Proven through the whole pipeline: the ISLE lowering (an abstract interpretation of
  the rules, `RelocProvDriver`), `prepare`, the allocation, emission and layout
  (`RelocProvEmit`);
* **reach** (`reachOkB`, on the layout `P`, decided on the inputs): every external function name
  of every function has a word-aligned link-map address that `bl` reaches from anywhere in the
  region `[R, R + size)` (`callReachB`: within `2 ^ 27` bytes), every declared name with every
  declared offset an address whose page `adrp` reaches from every page of the region
  (`pageReachB`: within `2 ^ 20` pages). A name outside the link map has address `0`.

**`compileExe_total_reach`**: `compileExe_total_input` with `reachOkB` in place of
`CallPageReach` — every premise is decided on the CLIF input, the link map and `file0`. The
shipped compiler: `FV/Link/ExeInputReachCleanup.lean`.
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec
open Backend.Proof.RelocProv (externNames refNames refOffs)

/-! ## The reach conditions -/

/-- **`bl` reaches `t` from the region**: `t` is word-aligned and within `2 ^ 27` bytes of every
address of `[R, R + size)`. -/
def LinkSpec.callReachB (P : LinkSpec) (t : Nat) : Bool :=
  t % 4 == 0 && decide (P.R + P.size ≤ t + 2 ^ 27) && decide (t < P.R + 2 ^ 27)

/-- **`adrp` reaches the page of `T` from the region**: within `2 ^ 20` pages of every page of
`[R, R + size)`. -/
def LinkSpec.pageReachB (P : LinkSpec) (T : Nat) : Bool :=
  decide (pageOf (P.R + P.size) ≤ pageOf T + 2 ^ 20) && decide (pageOf T < pageOf P.R + 2 ^ 20)

/-- **The reach of `f`'s references from the region of `P`**: every external function name of
`f` has a link-map address `bl` reaches, every declared name with every declared offset an
address whose page `adrp` reaches. -/
def LinkSpec.refsReachB (P : LinkSpec) (f : Clif.Function) : Bool :=
  (externNames f).all (fun n => P.callReachB (P.input0.addrOf n)) &&
  (refNames f).all fun n => (refOffs f).all fun o => P.pageReachB (P.input0.symAddr n o).toNat

/-- **The reach condition of the layout `P`**: `refsReachB` for every function. -/
def LinkSpec.reachOkB (P : LinkSpec) : Bool := P.funcs.all fun fi => P.refsReachB fi.func

/-! ## Reach from provenance -/

theorem pageOf_le {x y : Nat} (h : x ≤ y) : pageOf x ≤ pageOf y := by
  unfold pageOf
  exact Int.ofNat_le.2 (Nat.div_le_div_right h)

/-- **A relocation with `f`'s references, at an aligned address of the region, is in range**
under `refsReachB` (any input `I` with the layout's link map and no aliases). -/
theorem range_of_refs {P : LinkSpec} {I : LinkInput} (hI : I.addrs = P.addrs)
    (hal : I.aliases = []) {f : Clif.Function} (hf : P.refsReachB f = true) {a : Art} {r : Reloc}
    (hlo : P.R ≤ (wAt a r.offset).toNat) (hhi : (wAt a r.offset).toNat < P.R + P.size)
    (h4 : (wAt a r.offset).toNat % 4 = 0) (hr : Proof.RelocProv.RelocOk f r) (tp : Nat → Option Nat)
    (htls : r.type ≠ .tlsDescAdrPage21) : relocRangeB I tp a r = true := by
  simp only [LinkSpec.refsReachB, Bool.and_eq_true, List.all_eq_true] at hf
  obtain ⟨hc, hp⟩ := hf
  have haddr : ∀ n, I.addrOf n = P.input0.addrOf n := fun n => by
    simp only [LinkInput.addrOf, hI]; rfl
  have hbase : ∀ n, I.baseOf n = P.input0.addrOf n := fun n => by
    simp only [LinkInput.baseOf, hal, List.lookup_nil, Option.getD_none, haddr]
  have hsym : ∀ n o, I.symAddr n o = P.input0.symAddr n o := fun n o => by
    simp only [LinkInput.symAddr, haddr]
  obtain ⟨o, ty, sym, add⟩ := r
  dsimp only at hlo hhi h4 ⊢
  cases ty <;> simp only [Proof.RelocProv.RelocOk] at hr <;> simp only [relocRangeB] <;> try rfl
  · -- call26
    have := hc sym hr
    simp only [LinkSpec.callReachB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    obtain ⟨⟨ha, h1⟩, h2⟩ := this
    simp only [blRange, inR, hbase, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hlo hhi h4 ⊢
    omega
  all_goals first
    | exact absurd rfl htls
    | (obtain ⟨hn, ho⟩ := hr
       have := hp sym hn add ho
       simp only [LinkSpec.pageReachB, Bool.and_eq_true, decide_eq_true_eq] at this
       obtain ⟨h1, h2⟩ := this
       have e1 := pageOf_le hlo
       have e2 := pageOf_le (Nat.le_of_lt hhi)
       simp only [inR, target, hsym, Bool.and_eq_true, decide_eq_true_eq]
       omega)

/-- **The relocations of a placed table are at aligned addresses of the region**: entry `i` is
loaded at the `i`-th placed address with `sizes[i]` words, and a relocation's offset is a word of
its function (`relocShapesB`). -/
theorem pc_of_placed {P : LinkSpec} (hP : PlaceOk P) {T : List (Clif.Function × Art)}
    (hlen : T.length = P.funcs.length)
    (hT : ∀ i < P.funcs.length, ∃ e, T[i]? = some e ∧
      e.2.base = BitVec.ofNat 64 (P.R + (offs P.sizes 0)[i]!) ∧ e.2.fb.words.size = P.sizes[i]!)
    (hsh : ∀ e ∈ T, relocShapesB e.2 = true) :
    ∀ e ∈ T, ∀ r ∈ e.2.fb.relocs, P.R ≤ (wAt e.2 r.offset).toNat ∧
      (wAt e.2 r.offset).toNat < P.R + P.size ∧ (wAt e.2 r.offset).toNat % 4 = 0 := by
  intro e he r hr
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 he
  have hil : i < P.funcs.length := hlen ▸ (List.getElem?_eq_some_iff.1 hi).1
  obtain ⟨e', he', hb, hw⟩ := hT i hil
  rw [hi, Option.some.injEq] at he'
  subst he'
  have hs := hsh e he
  simp only [relocShapesB, Bool.and_eq_true, List.all_eq_true] at hs
  have hrs := hs.2 r hr
  simp only [relocShapeB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrs
  obtain ⟨⟨h4, hlt⟩, -⟩ := hrs
  have hend := off_end hP hil
  have hmod := offs_mod4 (ns := P.sizes) (o := 0) rfl (i := i) (by rw [hP.sizesLen]; exact hil)
  have hfit := hP.fits
  have hal := hP.align
  rw [hw] at hlt
  have hpc : (wAt e.2 r.offset).toNat = P.R + (offs P.sizes 0)[i]! + r.offset := by
    unfold wAt
    rw [hb]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [hpc]
  omega

/-- **`CallPageReach` from provenance and reach**: if every relocation of the Lean compiler's
table has its function's references (`hprov`), `reachOkB` gives every non-TLS relocation's
range. -/
theorem callPageReach_of_prov {S : LinkSpec} {phs : List Phdr} (hin : InScopeP S.placed.input0 = true)
    (hl : S.placed.layoutOkB = true) (hreach : S.placed.reachOkB = true)
    (hprov : ∀ e ∈ tabOf S.placed.input.resultsT, ∀ r ∈ e.2.fb.relocs, Proof.RelocProv.RelocOk e.1 r) :
    CallPageReach S phs := by
  intro e he r hr htls
  have hp := placeOkB_placed hin hl
  have hP := placeOk_of hp
  have hpc := pc_of_placed hP (tab_length _)
    (fun i hi => by
      obtain ⟨e, h1, h2, h3, -, -⟩ := tab_placed hp (results_of hin) (names_of rfl) (sizes_of rfl) i hi
      exact ⟨e, h1, h2, h3⟩)
    (shapes_of hin) e he r hr
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
  obtain ⟨fi, hfi, h1, -⟩ := mem_resultsT he0
  have hf : S.placed.refsReachB fi.func = true :=
    List.all_eq_true.1 hreach fi hfi
  rw [← h1] at hf
  exact range_of_refs rfl rfl hf hpc.1 hpc.2.1 hpc.2.2 (hprov _ he r hr) _ htls

/-! ## Provenance of the compiled relocations -/

/-- The lowering conditions of an in-scope function (`fnScopeB`). -/
theorem lowerScope_of_fnScope {g : Clif.Function} (h : fnScopeB g = true) :
    Proof.Driver.LowerScope g := by
  obtain ⟨-, -, -, -, -, -, -, -, hls, -⟩ := fnScope_parts h
  exact Proof.Driver.lowerScope_of hls

/-- **The compiled code relocates against its CLIF function's declarations**: every relocation of
the Lean compiler's table has `RelocOk` for its function (`lowerFunction_refs`, `prepare_allInsts`,
`relocs_of_alloc`). -/
theorem relocOk_tab {S : LinkSpec} (hin : InScopeP S.placed.input0 = true) :
    ∀ e ∈ tabOf S.placed.input.resultsT, ∀ r ∈ e.2.fb.relocs, Proof.RelocProv.RelocOk e.1 r := by
  have hr := results_of hin
  intro e he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
  obtain ⟨fi, hfi, h1, h2⟩ := mem_resultsT he0
  have hok := getOk_eq (List.all_eq_true.1 hr e0 he0)
  rw [h2] at hok
  obtain ⟨hlf, hpr, -, hal, hem, hla, -⟩ := pipeT_spec hok
  have hv := Proof.RelocProv.lowerFunction_refs
    (lowerScope_of_fnScope (fnScope_of_inScope (S := S) hin hfi)) hlf
  have hv' := Proof.RelocProv.prepare_allInsts (fun _ => trivial)
    (fun _ _ _ h => Proof.RelocProv.refsOk_setTargets h) hpr hv
  show ∀ r ∈ (getOk e0.2).fb.relocs, Proof.RelocProv.RelocOk e0.1 r
  rw [h1, h2]
  exact Proof.RelocProv.relocs_of_alloc hv' hal hem hla

/-- **`CallPageReach` holds under `reachOkB`.** -/
theorem callPageReach_of {S : LinkSpec} {phs : List Phdr} (hin : InScopeP S.placed.input0 = true)
    (hl : S.placed.layoutOkB = true) (hreach : S.placed.reachOkB = true) : CallPageReach S phs :=
  callPageReach_of_prov hin hl hreach (relocOk_tab hin)

/-! ## Totality -/

/-- **The executable compiler succeeds on decidable input conditions**: on the CLIF input
(`InScopeIn`: conditions on the CLIF functions alone, no compiler stage run), the layout (`layoutOkB`), the reach of the CLIF functions' references from the
region (`reachOkB`, on the link map), rust-lld's executable `file0` (`file0OkB`), with the Lean
compiler's layout (`S.placed`). -/
theorem compileExe_total_reach {S : LinkSpec} {file0 : ByteArray} {phs : List Phdr}
    (hin : InScopeIn S.placed.input0 = true) (hl : S.placed.layoutOkB = true)
    (hph : phdrs (fileRd file0) = some phs) (hf : S.placed.file0OkB file0 phs = true)
    (hreach : S.placed.reachOkB = true) :
    compileExe S.placed file0 =
      .ok (patch file0 (offsetOf phs S.R) (regionOf S.placed (tpOff phs))) :=
  compileExe_total_input hin hl hph hf (callPageReach_of (inScopeP_of_input hin) hl hreach)

end Link
