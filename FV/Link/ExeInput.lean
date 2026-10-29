module

public import FV.Link.ExeTotal
public import FV.Link.ImageProof
public import FV.E2E.RegLevelFrame

@[expose] public section

/-! # The executable compiler is total on decidable input conditions (L1e)

`compileExe_total` (`FV/Link/ExeTotal.lean`) takes conditions on what the tools produce: the
driver's names and sizes are the compiled code's (`S.sizes = S.sizesOf`), the placement's
conditions (`placeOkB`, which include the compiled sizes), the ranges of the compiled
relocations, and rust-lld's checks on the *patched* file (`regionOkB` of the compiled region's
size, `outsideOkB`). **`compileExe_total_input`** replaces them by conditions decided on the
inputs `S` and `file0`:

* **the layout is the Lean compiler's** (`LinkSpec.placed`: the names are the CLIF functions',
  the sizes `sizesOf`, the compiled code's at any load address); the placement's conditions follow
  from `InScopeP` (distinct names; every compiled function is nonempty, `pipeT_words_pos`: its
  entry block starts with the prologue) and `layoutOkB` (the region's base `R` and the outside
  part's addresses against the layout's span);
* **rust-lld's checks on `file0`** (`file0OkB`): the region is a read-only part of one `PT_LOAD`
  segment (`regionOkB`, of the layout's span), the headers (`hdrB`), the data objects read
  outside the region (`dataFastB` on `maskEx`, the file without the region's bytes), the symbol
  table (`symsOkB`) with the section headers, the symbol tables and their string tables after
  the region (`symFootB`): writing the region changes none of the bytes these checks read
  (`outsideOkB_patch`);
* **TLS offsets**: `file0` has a `PT_TLS` segment and every link-map address (and `0`, the
  address of a name outside the link map) has a thread-pointer offset below `2 ^ 32`
  (`tlsOkB`, in `file0OkB`): every TLS relocation's offset is one of these.

`placed_of_compileExe`: a successful `compileExe S file0` has `S.placed = S` (the driver's names
and sizes are checked), so the theorem is about the compilation the driver runs whenever the
driver's sizes are the Lean compiler's; the driver must link `file0` with this layout (rust-lld
places the region's placeholder of the layout's span and the functions at their offsets, which
`symsOkB` checks).

**Remaining premise** `CallPageReach`: the `bl` (±128 MiB, 4-aligned) and `adrp` (±4 GiB) targets
of the compiled code are in reach. A target is the link-map address of the relocation's symbol
(plus its addend for `adrp`). `FV/Link/ExeInputReach.lean` derives it from a condition on the CLIF
functions and the link map (`reachOkB`) by a name-provenance analysis of the compiler
(`compileExe_total_reach`).

The shipped compiler `Link.DeadCleanup.compileExe`: `FV/Link/ExeInputCleanup.lean`.
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec

/-! ## The layout from the compiler -/

/-- `S` with the names of its CLIF functions and the sizes `sz`. -/
def LinkSpec.withSizes (S : LinkSpec) (sz : List Nat) : LinkSpec :=
  { S with names := S.funcs.map (·.func.name), sizes := sz }

/-- **The Lean compiler's layout**: the CLIF functions' names, the compiled code's sizes. -/
def LinkSpec.placed (S : LinkSpec) : LinkSpec := S.withSizes S.sizesOf

/-- **The layout's conditions on the base and the outside part**: `R` is nonzero, word-aligned,
the region `[R, R + size)` is in the address space and holds no outside symbol. -/
def LinkSpec.layoutOkB (P : LinkSpec) : Bool :=
  decide (0 < P.R) && P.R % 4 == 0 && decide (P.R + P.size < 2 ^ 64) && clearOfB P.R P.size P.outside

/-- `l` is the sum's term: a member is at most the sum. -/
theorem le_sum_of_mem {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons y l ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

/-- **Compiled code is nonempty**: the entry block starts with the prologue (any allocation
`checkAlloc` accepts, lowered and emitted). -/
theorem words_pos_of {vcp : VCode} {rf : RFunc} {af : AFunc} {k : Nat} {fa : FnAsm} {fb : FnBin}
    (hc : checkAlloc vcp rf = .ok ()) (hal : lowerRFunc vcp rf = .ok af)
    (hem : emitFunc k af = .ok fa) (hla : fa.layout = .ok fb) : 0 < fb.words.size := by
  obtain ⟨c, ins, a0, hc', -⟩ := Backend.Proof.allocChecked_of_checkAlloc hc
  have h0 : 0 < vcp.blocks.size := Nat.pos_of_ne_zero hc'.nonempty
  obtain ⟨vb, hvb⟩ : ∃ vb, vcp.blocks[0]? = some vb := ⟨_, Array.getElem?_eq_getElem h0⟩
  obtain ⟨items, hit⟩ : ∃ items, rf.blocks[0]? = some items :=
    ⟨_, Array.getElem?_eq_getElem (by rw [hc'.size]; exact h0)⟩
  have hframe := lowerRFunc_frame hal
  obtain ⟨⟨-, -, -, hbl⟩, -⟩ := lowerRFunc_ok hal
  obtain ⟨code, -, haf⟩ := hbl 0 vb items hvb hit
  obtain ⟨body, psF, -, -, hblk⟩ := emit_block hem
  obtain ⟨j0, lsA, ps1, ps2, T, -, hdrop, hls, -, -⟩ := hblk 0 _ _ haf
  simp only [ite_true] at hls
  obtain ⟨ls1, ls2, psm, h1, h2, rfl⟩ := Backend.Proof.codeLinesE_append _ _ _ _ _ hls
  simp only [codeLinesE, ainstLines, hframe, ite_true, bind, Except.bind, pure, Except.pure,
    List.append_nil, Except.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  have hZ : ∀ n, (ls2 ++ Backend.nxtOf af 0)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact Backend.Proof.codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [Backend.nxtOf] at hm
      split at hm <;> simp at hm
  rw [List.append_assoc, ftR_plain_append _ _ _ (fun ln h => by
    obtain ⟨_, _, _, hp⟩ := Backend.Proof.prologueLines_ins _ ln h; exact hp) hZ] at hdrop
  have hmem : Line.ins (.stp Reg.fp Reg.lr (.spPreIndexed (-16))) ∈ fa.lines.toList := by
    apply List.mem_of_mem_drop (i := j0 + 1)
    rw [hdrop]
    simp [prologueLines]
  have hs := Backend.Proof.layout_sum hla
  have := le_sum_of_mem (List.mem_map_of_mem (f := Line.size) hmem)
  simp only [Line.size] at this
  omega

theorem pipeT_words_pos {g : Clif.Function} {k : Nat} {b : BitVec 64} {o : Lean.Json} {a : Art}
    (h : pipeT g k b o = .ok a) (hc : checkAlloc a.vcp a.rf = .ok ()) : 0 < a.fb.words.size := by
  obtain ⟨-, -, -, hal, hem, hla, -⟩ := pipeT_spec h
  exact words_pos_of hc hal hem hla

/-- `nodupGo` is complete. -/
theorem nodupGo_complete : ∀ {l : List String} {s : Std.HashSet String}, l.Nodup →
    (∀ x ∈ l, s.contains x = false) → nodupGo l s = true
  | [], _, _, _ => rfl
  | x :: xs, s, hn, hs => by
    obtain ⟨hx, hxs⟩ := List.nodup_cons.1 hn
    simp only [nodupGo, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨hs x List.mem_cons_self, nodupGo_complete hxs fun y hy => ?_⟩
    rw [Std.HashSet.contains_insert, Bool.or_eq_false_iff]
    refine ⟨?_, hs y (List.mem_cons_of_mem _ hy)⟩
    rw [beq_eq_false_iff_ne]
    rintro rfl
    exact hx hy

theorem nodupB_complete {l : List String} (h : l.Nodup) : nodupB l = true :=
  nodupGo_complete h fun _ _ => by simp

/-- `InScopeP` asks for distinct function names. -/
theorem nodup_of_inScope {S : LinkSpec} {sz : List Nat} (hin : InScopeP (S.withSizes sz).input0 = true) :
    (S.funcs.map (·.func.name)).Nodup := by
  simp only [InScopeP, progScopeB, Bool.and_eq_true, decide_eq_true_eq] at hin
  simpa [LinkInput.prog, LinkSpec.withSizes, input0, List.map_map, Function.comp_def] using hin.1.1.1

/-- `InScopeP` gives every function's `fnScopeB`. -/
theorem fnScope_of_inScope {S : LinkSpec} {sz : List Nat} (hin : InScopeP (S.withSizes sz).input0 = true)
    {fi : FnInput} (hfi : fi ∈ S.funcs) : fnScopeB fi.func = true := by
  simp only [InScopeP, Bool.and_eq_true, List.all_eq_true] at hin
  exact hin.2 fi.func (by
    simp only [LinkInput.prog, LinkSpec.withSizes, input0, List.mem_map]; exact ⟨fi, hfi, rfl⟩)

/-- **The placement's conditions hold for a layout of the CLIF functions' names and positive
sizes, one per function**, under `layoutOkB`. -/
theorem placeOkB_withSizes {S : LinkSpec} {sz : List Nat} (hnd : (S.funcs.map (·.func.name)).Nodup)
    (hlen : sz.length = S.funcs.length) (hpos : ∀ n ∈ sz, 0 < n) (hl : (S.withSizes sz).layoutOkB = true) :
    (S.withSizes sz).placeOkB = true := by
  simp only [layoutOkB, Bool.and_eq_true, decide_eq_true_eq] at hl
  obtain ⟨⟨⟨hR, hal⟩, hfit⟩, hclr⟩ := hl
  simp only [placeOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨nodupB_complete hnd, by simp [LinkSpec.withSizes]⟩, hlen⟩, hpos⟩, hR⟩, hal⟩, hfit⟩, hclr⟩

/-- **The placement's conditions hold for the Lean compiler's layout.** -/
theorem placeOkB_placed {S : LinkSpec} (hin : InScopeP S.placed.input0 = true)
    (hl : S.placed.layoutOkB = true) : S.placed.placeOkB = true := by
  refine placeOkB_withSizes (nodup_of_inScope hin) (by simp [LinkSpec.sizesOf]) ?_ hl
  intro n hn
  simp only [LinkSpec.sizesOf, List.mem_map] at hn
  obtain ⟨fi, hfi, rfl⟩ := hn
  obtain ⟨a, ha, -, -, hc, -⟩ := pipeT_ok (fnScope_of_inScope hin hfi) spillDefinedHyp fi.k 0
    (raJ fi.ra fi.j)
  rw [ha]
  exact pipeT_words_pos ha hc

/-! ## rust-lld's checks on `file0` -/

/-- `file` without its bytes `[off, off + n)` (the region's). -/
def maskEx (file : ByteArray) (off n : Nat) : Excerpt :=
  [(0, file.extract 0 off), (off + n, file.extract (off + n) file.size)]

/-- **What `symIndex` and `symsOkB` read lies at or after `hi`**: the section header table, every
symbol table (`SHT_SYMTAB`, 24-byte entries) and its string table (they read the ELF header too,
below the region: `regionOkB`). -/
def symFootB (file : ByteArray) (hi : Nat) : Bool :=
  let r := fileRd file
  match ehdr r with
  | none => true
  | some e =>
    decide (hi ≤ e.shoff) && (List.range e.shnum).all fun s =>
      match shdr r e s with
      | none => true
      | some sh => !(decide (sh.type = 2 ∧ sh.entsize = 24)) || (decide (hi ≤ sh.offset) &&
          match shdr r e sh.link with
          | some st => decide (hi ≤ st.offset)
          | none => true)

/-- **The TLS offsets**: every address of the layout's link map, and `0` (the address of a name
outside it), has a thread-pointer offset (`file0` has a `PT_TLS` segment) below `2 ^ 32`. -/
def tlsOkB (P : LinkSpec) (phs : List Phdr) : Bool :=
  (0 :: P.addrs.map (·.2)).all fun v => match tpOff phs v with
    | some x => decide (x < 2 ^ 32)
    | none => false

/-- **The conditions on rust-lld's executable `file0`** (program headers `phs`) for the layout `P`:
the region of `P`'s size at `R` is a read-only part of one `PT_LOAD` segment (`regionOkB`), the
headers are a static AArch64 executable's (`hdrB`), the data objects are in place in the bytes
outside the region (`dataFastB` on `maskEx`), the symbol table is the link map (`symsOkB`) and
lies after the region with the section headers (`symFootB`), and the TLS offsets fit
(`tlsOkB`). -/
def LinkSpec.file0OkB (P : LinkSpec) (file0 : ByteArray) (phs : List Phdr) : Bool :=
  let off := offsetOf phs P.R
  regionOkB file0 P.R P.size off && hdrB [(0, file0)] &&
    dataFastB P.input0 P.data (maskEx file0 off P.size) && symsOkB P.input0 file0 &&
    symFootB file0 (off + P.size) && tlsOkB P phs

theorem exRd_self (f : ByteArray) : exRd [(0, f)] = fileRd f := by
  funext o
  unfold exRd fileRd
  by_cases h : o < f.size
  · simp [h]
  · simp [h]

theorem byte_eq {p f : ByteArray} {o : Nat} (h : p[o]? = f[o]?) (hp : o < p.size) (hf : o < f.size) :
    p.data[o] = f.data[o] := by
  rw [byteArray_getElem?, byteArray_getElem?, Array.getElem?_eq_getElem hp,
    Array.getElem?_eq_getElem hf] at h
  exact Option.some.inj h

theorem extract_getElem? (a : ByteArray) (s e i : Nat) :
    (a.extract s e)[i]? = if i < min e a.size - s then a[s + i]? else none := by
  rw [byteArray_getElem?, ByteArray.data_extract, Array.getElem?_extract, byteArray_getElem?]
  rfl

/-- The masked file's bytes are the patched file's. -/
theorem mask_ext {file0 b : ByteArray} {off : Nat} (hf : off + b.size ≤ file0.size) :
    Ext (exRd (maskEx file0 off b.size)) (fileRd (patch file0 off b)) := by
  intro o x hx
  unfold exRd maskEx at hx
  by_cases h1 : o < off
  · rw [List.find?_cons_of_pos (by simp [ByteArray.size_extract]; omega)] at hx
    simp only [extract_getElem?, Nat.sub_zero, Nat.zero_add,
      show o < min off file0.size by omega, ↓reduceIte] at hx
    rw [fileRd_patch_lt h1]
    exact hx
  · rw [List.find?_cons_of_neg (by simp [ByteArray.size_extract]; omega)] at hx
    by_cases h2 : off + b.size ≤ o ∧ o < file0.size
    · rw [List.find?_cons_of_pos (by simp [ByteArray.size_extract]; omega)] at hx
      simp only [extract_getElem?, Nat.min_self,
        show o - (off + b.size) < file0.size - (off + b.size) by omega, ↓reduceIte,
        show off + b.size + (o - (off + b.size)) = o by omega] at hx
      simp only [fileRd, patch_getElem?]
      rw [ite_eq_right (by omega)]
      exact hx
    · rw [List.find?_cons_of_neg (by simp [ByteArray.size_extract]; omega)] at hx
      cases hx

theorem objB_ext {I : LinkInput} {r r' : Rd} {phs : List Phdr} {o : Clif.DataObject}
    (h : objB I r phs o = true) (hx : Ext r r') : objB I r' phs o = true := by
  simp only [objB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h ⊢
  exact ⟨h.1, fun i hi => ⟨loadIn_ext hx (h.2 i hi).1, (h.2 i hi).2⟩⟩

/-- `dataB` holds on every extension of an excerpt it holds on. -/
theorem dataB_ext {I : LinkInput} {D : List Clif.DataObject} {ex ex' : Excerpt}
    (h : dataB I D ex = true) (hx : Ext (exRd ex) (exRd ex')) : dataB I D ex' = true := by
  unfold dataB at h ⊢
  split at h
  · rename_i phs hp
    rw [phdrs_ext hx hp]
    exact List.all_eq_true.2 fun o ho => objB_ext (List.all_eq_true.1 h o ho) hx
  · cases h

/-! ### Reads after the region -/

section Above

variable {p f : ByteArray} {lo hi : Nat} (hsz : p.size = f.size)
  (hlo : ∀ o < lo, p[o]? = f[o]?) (hhi : ∀ o, hi ≤ o → p[o]? = f[o]?) (h64 : 64 ≤ lo)

include hhi in
theorem rd_hi {o : Nat} (ho : hi ≤ o) : fileRd p o = fileRd f o := by
  simp only [fileRd, hhi o ho]

include hhi in
theorem fields_above {o : Nat} (ho : hi ≤ o) (spec : List (Nat × Nat)) :
    fields (fileRd p) o spec = fields (fileRd f) o spec :=
  mapM_congr_mem fun _ _ => le_congr _ _ fun _ _ => rd_hi hhi (by omega)

include hlo h64 in
theorem ehdr_above : ehdr (fileRd p) = ehdr (fileRd f) :=
  ehdr_congr h64 fun o ho => by simp only [fileRd, hlo o ho]

include hhi in
theorem shdr_above {e : Ehdr} (he : hi ≤ e.shoff) (s : Nat) :
    shdr (fileRd p) e s = shdr (fileRd f) e s := by
  unfold Elf.shdr
  split
  · rw [fields_above hhi (by omega)]
  · rfl

/-- `symFootB`, unfolded at the file's header. -/
def FootOk (r : Rd) (e : Ehdr) (hi : Nat) : Prop :=
  hi ≤ e.shoff ∧ ∀ s sh, shdr r e s = some sh → sh.type = 2 → sh.entsize = 24 →
    hi ≤ sh.offset ∧ ∀ st, shdr r e sh.link = some st → hi ≤ st.offset

theorem footOk_of {e : Ehdr} (h : symFootB f hi = true) (he : ehdr (fileRd f) = some e) :
    FootOk (fileRd f) e hi := by
  simp only [symFootB, he, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  refine ⟨h.1, fun s sh hs ht hes => ?_⟩
  have hlt : s < e.shnum := by
    unfold Elf.shdr at hs; split at hs
    · assumption
    · cases hs
  have := h.2 s hlt
  rw [hs] at this
  simp only [ht, hes, and_self, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    decide_eq_true_eq] at this
  refine ⟨this.1, fun st hst => ?_⟩
  have h2 := this.2
  rw [hst] at h2
  simpa using h2

include hlo hhi h64 in
theorem symEntry_above {e : Ehdr} (he : ehdr (fileRd f) = some e) (hF : FootOk (fileRd f) e hi)
    (s i : Nat) : symEntry (fileRd p) s i = symEntry (fileRd f) s i := by
  unfold symEntry
  rw [ehdr_above hlo h64, he, Option.bind_some, Option.bind_some, shdr_above hhi hF.1]
  cases hs : shdr (fileRd f) e s with
  | none => rfl
  | some sh =>
    simp only [Option.bind_some]
    by_cases hc : sh.type = 2 ∧ sh.entsize = 24 ∧ 24 * (i + 1) ≤ sh.size
    · simp only [hc, and_self, ↓reduceIte]
      rw [shdr_above hhi hF.1,
        fields_above hhi (by have := (hF.2 s sh hs hc.1 hc.2.1).1; omega)]
    · simp only [hc, ↓reduceIte]

theorem symEntry_off {e : Ehdr} (he : ehdr (fileRd f) = some e) (hF : FootOk (fileRd f) e hi)
    {s i o v : Nat} (h : symEntry (fileRd f) s i = some (o, v)) : hi ≤ o := by
  simp only [symEntry, he, Option.bind_some, Option.bind_eq_some_iff] at h
  obtain ⟨sh, hs, h⟩ := h
  split at h
  · rename_i hc
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨st, hst, l, -, h⟩ := h
    have := (hF.2 s sh hs hc.1 hc.2.1).2 st hst
    split at h
    · split at h
      · cases h; omega
      · cases h
    · cases h
  · cases h

include hsz hhi in
theorem nulFrom_above : ∀ (d j : Nat), f.size - j = d → hi ≤ j → nulFrom p j = nulFrom f j
  | d, j, hd, hj => by
    conv => lhs; rw [nulFrom]
    conv => rhs; rw [nulFrom]
    by_cases hjf : j < f.size
    · have hjp : j < p.size := hsz ▸ hjf
      simp only [hjp, hjf, ↓reduceDIte]
      have hb : p[j] = f[j] := byte_eq (hhi j hj) hjp hjf
      rw [hb]
      split
      · exact nulFrom_above (d - 1) (j + 1) (by omega) (by omega)
      · rfl
    · have hjp : ¬ j < p.size := hsz ▸ hjf
      simp only [hjp, hjf, ↓reduceDIte]

include hsz hhi in
theorem extract_above {o : Nat} (ho : hi ≤ o) (e : Nat) : p.extract o e = f.extract o e := by
  apply ByteArray.ext
  rw [ByteArray.data_extract, ByteArray.data_extract]
  refine Array.ext (by simp [Array.size_extract, ByteArray.size_data, hsz]) fun i h1 h2 => ?_
  rw [Array.getElem_extract, Array.getElem_extract]
  simp only [Array.size_extract] at h1 h2
  exact byte_eq (hhi (o + i) (by omega)) (by simp only [ByteArray.size_data] at h1; omega)
    (by simp only [ByteArray.size_data] at h2; omega)

include hsz hlo hhi h64 in
theorem entryKey_above {e : Ehdr} (he : ehdr (fileRd f) = some e) (hF : FootOk (fileRd f) e hi)
    (s i : Nat) : entryKey p s i = entryKey f s i := by
  unfold entryKey
  rw [symEntry_above hlo hhi h64 he hF]
  cases hse : symEntry (fileRd f) s i with
  | none => rfl
  | some ov =>
    obtain ⟨o, v⟩ := ov
    have ho := symEntry_off he hF hse
    simp only
    rw [nulFrom_above hsz hhi _ o rfl ho, extract_above hsz hhi ho]

include hsz hlo hhi h64 in
theorem symIndex_above (hft : symFootB f hi = true) : symIndex p = symIndex f := by
  unfold symIndex
  simp only
  rw [ehdr_above hlo h64]
  cases he : ehdr (fileRd f) with
  | none => rfl
  | some e =>
    have hF := footOk_of hft he
    simp only [shdr_above hhi hF.1, entryKey_above hsz hlo hhi h64 he hF]

include hhi in
theorem cstrB_above {o : Nat} (ho : hi ≤ o) (n : String) :
    cstrB (fileRd p) o n = cstrB (fileRd f) o n := by
  have h : ∀ j, fileRd p (o + j) = fileRd f (o + j) := fun j => rd_hi hhi (by omega)
  simp only [cstrB, h]

include hsz hlo hhi h64 in
/-- **`symsOkB` reads nothing below `hi` but the ELF header.** -/
theorem symsOkB_above (hft : symFootB f hi = true) (I : LinkInput) :
    symsOkB I p = symsOkB I f := by
  unfold symsOkB
  simp only
  rw [symIndex_above hsz hlo hhi h64 hft]
  cases he : ehdr (fileRd f) with
  | none =>
    have hn : ∀ s i, symEntry (fileRd p) s i = none ∧ symEntry (fileRd f) s i = none := by
      intro s i
      simp [symEntry, he, ehdr_above hlo h64]
    simp only [fun s i => (hn s i).1, fun s i => (hn s i).2]
  | some e =>
    have hF := footOk_of hft he
    simp only [symEntry_above hlo hhi h64 he hF]
    congr 1
    funext q
    congr 1
    split
    · rename_i s i _
      cases hse : symEntry (fileRd f) s i with
      | none => rfl
      | some ov =>
        obtain ⟨o, v⟩ := ov
        simp only
        rw [cstrB_above hhi (symEntry_off he hF hse)]
    · rfl

end Above

/-- **rust-lld's checks on the patched file are its checks on `file0`**: patching the region
changes none of the bytes they read. -/
theorem outsideOkB_patch {I : LinkInput} {D : List Clif.DataObject} {file0 b : ByteArray}
    {R off : Nat} (hreg : regionOkB file0 R b.size off = true) (hh : hdrB [(0, file0)] = true)
    (hd : dataFastB I D (maskEx file0 off b.size) = true) (hs : symsOkB I file0 = true)
    (hft : symFootB file0 (off + b.size) = true) : outsideOkB I D (patch file0 off b) = true := by
  obtain ⟨e, phs, p, he, hp, h1, h2, h3, -⟩ := regionOkB_spec hreg
  simp only [outsideOkB, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold hdrB at hh ⊢
    rw [exRd_self] at hh ⊢
    rw [ehdr_patch hreg, phdrs_patch hreg]
    exact hh
  · rw [dataFastB_eq] at hd ⊢
    exact dataB_ext hd (by rw [exRd_self]; exact mask_ext h3)
  · have hsz := patch_size file0 off b
    have hlo : ∀ o < off, (patch file0 off b)[o]? = file0[o]? := fun o ho => by
      rw [patch_getElem?]; split <;> first | omega | rfl
    have hhi : ∀ o, off + b.size ≤ o → (patch file0 off b)[o]? = file0[o]? := fun o ho => by
      rw [patch_getElem?]; split <;> first | omega | rfl
    rw [symsOkB_above hsz hlo hhi h1 hft]
    exact hs

/-! ## TLS offsets -/

/-- **Every TLS relocation is in range** under `tlsOkB`: its symbol's address is in the link
map, or `0`. -/
theorem tls_range {P : LinkSpec} {I : LinkInput} (hI : I.addrs = P.addrs) {phs : List Phdr}
    (ht : tlsOkB P phs = true) (a : Art) {r : Reloc} (hr : r.type = .tlsDescAdrPage21) :
    relocRangeB I (tpOff phs) a r = true := by
  have hmem : I.addrOf r.sym ∈ 0 :: P.addrs.map (·.2) := by
    unfold LinkInput.addrOf
    rw [hI]
    cases hl : P.addrs.lookup r.sym with
    | none => exact List.mem_cons_self
    | some v =>
      obtain ⟨l1, l2, he, -⟩ := List.lookup_eq_some_iff.1 hl
      refine List.mem_cons_of_mem _ (List.mem_map.2 ⟨(r.sym, v), ?_, rfl⟩)
      rw [he]; simp
  have := List.all_eq_true.1 ht _ hmem
  unfold relocRangeB
  rw [hr]
  exact this

/-! ## Totality -/

/-- **The remaining premise**: the `bl` and `adrp` targets of the compiled code are in reach
(every relocation but the TLS sequence's first, whose range `tlsOkB` gives). -/
def CallPageReach (S : LinkSpec) (phs : List Phdr) : Prop :=
  ∀ e ∈ tabOf S.placed.input.resultsT, ∀ r ∈ e.2.fb.relocs, r.type ≠ .tlsDescAdrPage21 →
    relocRangeB S.placed.input (tpOff phs) e.2 r = true

/-- The region's size is the layout's span. -/
theorem regionOf_placed_size (S : LinkSpec) (tp : Nat → Option Nat) :
    (regionOf S.placed tp).size = S.placed.size := by
  have hsz := sizes_of (S := S.placed) rfl
  simp only [sizesOkB, decide_eq_true_eq] at hsz
  show (regionBytes S.placed.input tp (placedArts S.placed)).toArray.size = _
  rw [List.size_toArray, regionBytes_length, placedArts]
  simp only [List.map_map, Function.comp_def] at hsz ⊢
  rw [hsz]
  rfl

/-- **The executable compiler succeeds on decidable input conditions**: on the CLIF input
(`InScopeIn`), the layout (`layoutOkB`), rust-lld's executable `file0` (`file0OkB`), with the
Lean compiler's layout (`S.placed`), and the remaining premise `CallPageReach`. -/
theorem compileExe_total_input {S : LinkSpec} {file0 : ByteArray} {phs : List Phdr}
    (hin : InScopeIn S.placed.input0 = true) (hl : S.placed.layoutOkB = true)
    (hph : phdrs (fileRd file0) = some phs) (hf : S.placed.file0OkB file0 phs = true)
    (hreach : CallPageReach S phs) :
    compileExe S.placed file0 =
      .ok (patch file0 (offsetOf phs S.R) (regionOf S.placed (tpOff phs))) := by
  simp only [file0OkB, Bool.and_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨hreg, hh⟩, hd⟩, hs⟩, hft⟩, ht⟩ := hf
  have hsz := regionOf_placed_size S (tpOff phs)
  refine compileExe_total hin (placeOkB_placed (inScopeP_of_input hin) hl) rfl rfl
    (fun e he r hr => ?_) hph (hsz ▸ hreg)
    (outsideOkB_patch (hsz ▸ hreg) hh (hsz ▸ hd) (by exact hs) (hsz ▸ hft))
  by_cases htls : r.type = .tlsDescAdrPage21
  · exact tls_range rfl ht e.2 htls
  · exact hreach e he r hr htls

/-- **A successful link has the Lean compiler's layout**: `compileExe` checks the driver's names
and sizes against the compiled code (`namesOkB`, `sizesOkB`), so whenever `compileExe S file0`
succeeds, `S` is `S.placed` and `compileExe_total_input` is about the same compilation. -/
theorem placed_of_compileExe {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) : S.placed = S := by
  simp only [compileExe, inScopeInPar_eq] at h
  split at h
  · obtain ⟨-, -, -, -, hn, hs, -⟩ := leanLink_spec h
    simp only [namesOkB, tabOf, LinkInput.resultsT, input_funcs, List.map_map, ← List.map_take,
      List.take_length, Function.comp_def, decide_eq_true_eq] at hn
    simp only [sizesOkB, tabOf, LinkInput.resultsT, input_funcs, List.map_map, ← List.map_take,
      List.take_length, Function.comp_def, decide_eq_true_eq] at hs
    have hs' : S.sizesOf = S.sizes := by
      rw [← hs, sizesOf]
      exact List.map_congr_left fun fi _ => by rw [pipeT_fb]
    cases S
    simp only [LinkSpec.placed, LinkSpec.withSizes, LinkSpec.mk.injEq] at hn hs' ⊢
    simp only [hn, hs', and_self]
  · cases h

end Link
