import FV.Unw.EhFrameHdr
import FV.E2E.LinkCheck
import FV.E2E.Elf
import FV.Backend.Proof.UnwindTables
import FV.Backend.Proof.EhFrameDecode

/-!
# The linked executable's unwind tables are the compiled functions' (S10f)

`cargo fv --lean-link`'s region object carries lean-backend's `.eh_frame` entries for the
Lean-compiled functions; rust-lld merges them into the executable's `.eh_frame` and builds
`.eh_frame_hdr`; `lake exe lean-link` patches only the code. So the tables the unwinder reads
for the region come from rust-lld. `ehOkR` decides, on the written executable, that they are the
tables the theorems with unwinding use, and `ehOkR_sound` proves what it means.

* `memRd file a n`: the executable's memory, the `n` bytes at address `a` of the file-backed
  part of `a`'s `PT_LOAD` segment (a static executable's image; `Elf.loadIn`'s segments).
* `ehHdrOf`: the `.eh_frame_hdr` address, from the (only) `PT_GNU_EH_FRAME` program header.
* `unwTables file pc`: **the unwinder's lookup** (`Unw.hdrTables`, libunwind's
  `.eh_frame_hdr` search, `FV/Unw/EhFrameHdr.lean`), for a `pc` in a `PT_LOAD` segment.
* `tabsOf a`: the tables of a compiled function (the emitted CIE, the FDE rows `unwindRows`,
  the LSDA call-site table `callSites`), `E2E.Art.tables` (`FV/E2E/LinkArmU.lean`).
* `ehOkR R file`: the search table is sorted; for every function of the program, its tables
  exist, its code `[s, s + n)` lies in one `PT_LOAD` segment, the table entry of `s` (the next
  entry at or past `s + n`) points at an FDE starting at `s`, covering `[s, s + n)` and decoding
  to its tables.
* `ehOkR_sound`: then at every `pc` of the function's code the unwinder's lookup gives its
  address and tables.

The linear scan of `.eh_frame` (`Unw.tablesAt`, libunwind's fallback when the search fails) is
not checked: its model decodes the whole section and real executables hold CIEs outside it (std's
`zPLR` and code alignment 1 CIEs), and the fallback is not taken where the search succeeds.
-/

deriving instance DecidableEq for Unw.FnTables

namespace Link.EhCheck

set_option autoImplicit false

open E2E E2E.Elf E2E.LinkCheck Backend Backend.Proof.UnwindTables Unw

/-! ## The executable's memory and the unwinder's lookup -/

/-- **The executable's memory**: the `n` bytes at address `a` (fewer where the file-backed part
of its `PT_LOAD` segment ends; none outside). -/
def memRd (file : ByteArray) (a n : Nat) : List UInt8 :=
  match phdrs (fileRd file) with
  | some phs => match segIn phs a with
    | some p =>
      if a - p.vaddr < p.filesz then
        let o := p.offset + (a - p.vaddr)
        (file.extract o (min (o + n) (p.offset + p.filesz))).data.toList
      else []
    | none => []
  | none => []

theorem take_prefix {α : Type} (L : List α) {k k' : Nat} (h : k ≤ k') :
    ∃ rest, L.take k' = L.take k ++ rest :=
  ⟨(L.take k').drop k, by
    conv => lhs; rw [← List.take_append_drop k (L.take k')]
    rw [List.take_take, Nat.min_eq_left h]⟩

/-- Reading more bytes extends the read. -/
theorem memRd_prefix (file : ByteArray) (a : Nat) {n m : Nat} (h : n ≤ m) :
    ∃ rest, memRd file a m = memRd file a n ++ rest := by
  unfold memRd
  split
  · split
    · split
      · simp only [ByteArray.data_extract, Array.toList_extract, List.extract_eq_drop_take]
        exact take_prefix _ (by omega)
      · exact ⟨[], rfl⟩
    · exact ⟨[], rfl⟩
  · exact ⟨[], rfl⟩

/-- `PT_GNU_EH_FRAME`. -/
def ehHdrType : Nat := 0x6474e550

/-- The `.eh_frame_hdr` address: the only `PT_GNU_EH_FRAME` program header's. -/
def ehHdrOf (phs : List Phdr) : Option Nat :=
  match phs.filter (·.type == ehHdrType) with
  | [p] => some p.vaddr
  | _ => none

/-- **The tables the unwinder uses at `pc` in the executable `file`**: libunwind's
`.eh_frame_hdr` search (`Unw.hdrTables`), for a `pc` in a `PT_LOAD` segment
(`findUnwindSections`). -/
def unwTables (file : ByteArray) (pc : Nat) : Option (Nat × FnTables) :=
  match phdrs (fileRd file) with
  | some phs =>
    if (segIn phs pc).isSome then (ehHdrOf phs).bind fun h => hdrTables (memRd file) h pc
    else none
  | none => none

/-! ## The check -/

/-- The tables of a compiled function (`E2E.Art.tables` when `callSites`/`unwindRows`
succeed). -/
def tabsOf (a : Art) : Option FnTables :=
  match callSites a.af a.fa, unwindRows a.af a.fa with
  | .ok l, .ok rows => some ⟨cieInsns, insnsFrom 0 rows, l.map (List.map (·.entry))⟩
  | _, _ => none

theorem tabsOf_spec {a : Art} {T : FnTables} (h : tabsOf a = some T) :
    ∃ l rows, callSites a.af a.fa = .ok l ∧ unwindRows a.af a.fa = .ok rows ∧
      T = ⟨cieInsns, insnsFrom 0 rows, l.map (List.map (·.entry))⟩ := by
  unfold tabsOf at h
  split at h
  · rename_i l rows h1 h2
    exact ⟨l, rows, h1, h2, (Option.some.inj h).symm⟩
  · cases h

/-- The search table's initial locations increase. -/
def sortedB (loc : Nat → Option Nat) (cnt : Nat) : Bool :=
  (List.range (cnt - 1)).all fun i => match loc i, loc (i + 1) with
    | some x, some y => decide (x < y)
    | _, _ => false

/-- `Unw.fdeTables` with the LSDA decoded from the `w` bytes at its address (the check's fast
path: `fdeTablesW_sound`). -/
def fdeTablesW (rd : Nat → Nat → List UInt8) (w : Nat) (f : Fde) : Option FnTables := do
  let lsda ← match f.lsda with
    | none => some none
    | some a => (decodeLsda? (rd a (min w (2 ^ 64 - a)))).map some
  pure ⟨f.cieInsns, f.insns, lsda⟩

/-- An LSDA that decodes from a prefix of the memory decodes from all of it. -/
theorem fdeTablesW_sound {rd : Nat → Nat → List UInt8}
    (hrd : ∀ a n m, n ≤ m → ∃ rest, rd a m = rd a n ++ rest) {w : Nat} {f : Fde}
    {T : FnTables} (h : fdeTablesW rd w f = some T) : fdeTables rd f = some T := by
  unfold fdeTablesW at h
  unfold fdeTables
  cases hl : f.lsda with
  | none => simpa [hl] using h
  | some a =>
    rw [hl] at h
    cases hd : decodeLsda? (rd a (min w (2 ^ 64 - a))) with
    | none => simp [hd] at h
    | some es =>
      obtain ⟨rest, hr⟩ := hrd a (min w (2 ^ 64 - a)) (2 ^ 64 - a) (Nat.min_le_right _ _)
      have : decodeLsda? (rdAll rd a) = some es := by
        rw [rdAll, hr]
        exact Backend.Proof.EhFrameDecode.decodeLsda?_append rest hd
      simpa [hd, this] using h

/-- The LSDA window the check reads first. -/
def lsdaWin : Nat := 1024

/-- **The check of one compiled function `a`** (start `s`, `n` code bytes): see the module
doc. `cnt` table entries at `h`. -/
def fnEhOkB (rd : Nat → Nat → List UInt8) (phs : List Phdr) (h cnt : Nat) (a : Art) : Bool :=
  match tabsOf a with
  | none => false
  | some T =>
    let s := a.base.toNat
    let n := a.fb.size
    let loc := fun i => (hdrEntry rd h i).map (·.1)
    (match segIn phs s with
      | some p => decide (s + n ≤ p.vaddr + p.memsz)
      | none => false) &&
    (match search loc s 0 cnt with
      | some j => decide (j < cnt) &&
        (match hdrEntry rd h j with
          | some (l, fx) => decide (l = s) &&
            (decide (j + 1 = cnt) || match loc (j + 1) with
              | some y => decide (s + n ≤ y)
              | none => false) &&
            (match fdeAt rd fx with
              | some f => decide (f.pcBegin = s) && decide (n ≤ f.pcRange) &&
                  decide (f.pcBegin + f.pcRange < 2 ^ 64) &&
                  (fdeTablesW rd lsdaWin f == some T || fdeTables rd f == some T)
              | none => false)
          | none => false)
      | none => false)

/-- **The unwind tables check of the executable `file`** for the compiled functions `R`. -/
def ehOkR (R : Res) (file : ByteArray) : Bool :=
  match phdrs (fileRd file) with
  | none => false
  | some phs => match ehHdrOf phs with
    | none => false
    | some h =>
      match parseHdr h (memRd file h 12) with
      | some hd =>
        decide (hd.count ≠ 0) && sortedB (fun i => (hdrEntry (memRd file) h i).map (·.1)) hd.count &&
          (progOf R).funcs.all fun g => fnEhOkB (memRd file) phs h hd.count (artOf R g)
      | none => false

/-! ## Soundness -/

theorem sortedB_lt {loc : Nat → Option Nat} {cnt : Nat} (h : sortedB loc cnt = true) :
    ∀ k, k < cnt → ∀ i < k, ∃ x y, loc i = some x ∧ loc k = some y ∧ x < y := by
  intro k
  induction k with
  | zero => intro _ i hi; omega
  | succ k ih =>
    intro hk i hi
    have hm := List.all_eq_true.1 h k (List.mem_range.2 (by omega))
    cases h1 : loc k with
    | none => simp [h1] at hm
    | some x' =>
      cases h2 : loc (k + 1) with
      | none => simp [h1, h2] at hm
      | some y' =>
        simp only [h1, h2, decide_eq_true_eq] at hm
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · obtain ⟨x, y, hx, hy, hxy⟩ := ih (by omega) i hi
          rw [h1] at hy
          cases hy
          exact ⟨x, y', hx, rfl, by omega⟩
        · exact ⟨x', y', h1, rfl, hm⟩

/-- **The binary search lands on the entry `j`** whose initial location is at most `pc` and
whose next entry's is past it, in a sorted table. -/
theorem search_eq {loc : Nat → Option Nat} {pc cnt j xj : Nat}
    (hs : ∀ k, k < cnt → ∀ i < k, ∃ x y, loc i = some x ∧ loc k = some y ∧ x < y)
    (hj : j < cnt) (hl : loc j = some xj) (hle : xj ≤ pc)
    (hn : j + 1 < cnt → ∃ y, loc (j + 1) = some y ∧ pc < y) :
    ∀ len low, low ≤ j → j < low + len → low + len ≤ cnt → search loc pc low len = some j := by
  intro len
  induction len using Nat.strongRecOn with
  | ind len ih =>
    intro low h1 h2 h3
    rw [search]
    by_cases hlen : len ≤ 1
    · rw [if_pos hlen]
      congr 1
      omega
    · rw [if_neg hlen]
      have hmid : low + len / 2 < cnt := by omega
      rcases Nat.lt_trichotomy (low + len / 2) j with hlt | heq | hgt
      · obtain ⟨x, y, hx, hy, hxy⟩ := hs j hj _ hlt
        rw [hl] at hy
        cases hy
        rw [hx]
        simp only
        rw [if_neg (by omega), if_pos (by omega)]
        exact ih (len - len / 2) (by omega) _ (by omega) (by omega) (by omega)
      · rw [heq, hl]
        simp only
        by_cases he : xj = pc
        · rw [if_pos he]
        · rw [if_neg he, if_pos (by omega)]
          exact ih (len - len / 2) (by omega) _ (by omega) (by omega) (by omega)
      · obtain ⟨y, hy, hpy⟩ := hn (by omega)
        obtain ⟨s, hs'⟩ : ∃ s, loc (low + len / 2) = some s ∧ pc < s := by
          by_cases hm : low + len / 2 = j + 1
          · exact ⟨y, by rw [hm]; exact hy, hpy⟩
          · obtain ⟨x, z, hx, hz, hxz⟩ := hs _ hmid (j + 1) (by omega)
            rw [hy] at hx
            cases hx
            exact ⟨z, hz, by omega⟩
        rw [hs'.1]
        simp only
        rw [if_neg (by omega), if_neg (by omega)]
        exact ih (len / 2) (by omega) _ h1 (by omega) (by omega)

/-- **One function's check is sound**: at every `pc` of its code, the `.eh_frame_hdr` search
finds an FDE starting at `s` with its tables `T`. -/
theorem fnEhOkB_sound {rd : Nat → Nat → List UInt8} {phs : List Phdr} {h : Nat} {hd : Hdr}
    {a : Art} (hok : fnEhOkB rd phs h hd.count a = true)
    (hhd : parseHdr h (rd h 12) = some hd) (hc : hd.count ≠ 0)
    (hs : sortedB (fun i => (hdrEntry rd h i).map (·.1)) hd.count = true)
    (hrd : ∀ a n m, n ≤ m → ∃ rest, rd a m = rd a n ++ rest)
    {pc : Nat} (h1 : a.base.toNat ≤ pc) (h2 : pc < a.base.toNat + a.fb.size) :
    ∃ T, tabsOf a = some T ∧ (segIn phs pc).isSome ∧
      hdrTables rd h pc = some (a.base.toNat, T) := by
  unfold fnEhOkB at hok
  cases hT : tabsOf a with
  | none => rw [hT] at hok; cases hok
  | some T =>
    rw [hT] at hok
    simp only [Bool.and_eq_true] at hok
    obtain ⟨hseg, hsr⟩ := hok
    refine ⟨T, rfl, ?_, ?_⟩
    · -- the segment
      cases hp : segIn phs a.base.toNat with
      | none => rw [hp] at hseg; cases hseg
      | some p =>
        rw [hp] at hseg
        simp only [decide_eq_true_eq] at hseg
        have hl : isLoad a.base.toNat p = true := List.find?_some hp
        have hl' : isLoad pc p = true := by
          simp only [isLoad, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hl ⊢
          omega
        cases hq : segIn phs pc with
        | none =>
          exact absurd (List.find?_eq_none.1 hq p (List.mem_of_find?_eq_some hp)) (by simp [hl'])
        | some _ => rfl
    · -- the `.eh_frame_hdr` search
      cases hj : search (fun i => (hdrEntry rd h i).map (·.1)) a.base.toNat 0 hd.count with
      | none => rw [hj] at hsr; cases hsr
      | some j =>
        rw [hj] at hsr
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hsr
        obtain ⟨hjc, hsr⟩ := hsr
        cases he : hdrEntry rd h j with
        | none => rw [he] at hsr; cases hsr
        | some e =>
          obtain ⟨l, fx⟩ := e
          rw [he] at hsr
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hsr
          obtain ⟨⟨hl, hnext⟩, hf⟩ := hsr
          cases hfa : fdeAt rd fx with
          | none => rw [hfa] at hf; cases hf
          | some f =>
            rw [hfa] at hf
            simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true] at hf
            obtain ⟨⟨⟨hb, hr⟩, hw⟩, htab⟩ := hf
            replace htab : fdeTables rd f = some T :=
              htab.elim (fdeTablesW_sound hrd) id
            have hsrch : search (fun i => (hdrEntry rd h i).map (·.1)) pc 0 hd.count = some j :=
              search_eq (xj := l) (sortedB_lt hs) hjc (by rw [he]; rfl) (by omega)
                (fun hj1 => by
                  rcases hnext with hn | hn
                  · omega
                  · cases hy : (hdrEntry rd h (j + 1)).map (·.1) with
                    | none => rw [hy] at hn; cases hn
                    | some y =>
                      rw [hy] at hn
                      simp only [decide_eq_true_eq] at hn
                      exact ⟨y, rfl, by omega⟩)
                hd.count 0 (Nat.zero_le _) (by omega) (by omega)
            have hcond : f.pcBegin ≤ pc ∧ pc < f.pcBegin + f.pcRange ∧
                f.pcBegin + f.pcRange < 2 ^ 64 := by omega
            simp only [hdrTables, hdrFde, hhd, hsrch, he, hfa, bind, Option.bind, guard,
              pure, hc, ne_eq, not_false_eq_true, hcond, and_self, ↓reduceIte, htab]
            simp [hb]

/-- **The check is sound**: for a function `g` of the program and a `pc` of its code, the
unwinder's lookup in the executable (`unwTables`) gives its address and tables. -/
theorem ehOkR_sound {R : Res} {file : ByteArray} (hok : ehOkR R file = true)
    {g : Clif.Function} (hg : g ∈ (progOf R).funcs) {pc : Nat}
    (h1 : (artOf R g).base.toNat ≤ pc) (h2 : pc < (artOf R g).base.toNat + (artOf R g).fb.size) :
    ∃ T, tabsOf (artOf R g) = some T ∧
      unwTables file pc = some ((artOf R g).base.toNat, T) := by
  unfold ehOkR at hok
  cases hp : phdrs (fileRd file) with
  | none => simp [hp] at hok
  | some phs =>
    simp only [hp] at hok
    cases hh : ehHdrOf phs with
    | none => simp [hh] at hok
    | some h =>
      simp only [hh] at hok
      cases hhd : parseHdr h (memRd file h 12) with
      | none => simp [hhd] at hok
      | some hd =>
        simp only [hhd] at hok
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
        obtain ⟨⟨hc, hs⟩, hall⟩ := hok
        obtain ⟨T, hT, hseg, hhdr⟩ :=
          fnEhOkB_sound (hall g hg) hhd hc hs (fun a _ _ h => memRd_prefix file a h) h1 h2
        refine ⟨T, hT, ?_⟩
        simp only [unwTables, hp, hseg, ↓reduceIte, hh, Option.bind_some, hhdr]

end Link.EhCheck
