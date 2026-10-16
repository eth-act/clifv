import FV.Backend.Obj
import FV.Unw.Dwarf

/-!
# The emitted unwind tables are correct by construction (S10c, #230)

`docs/plans/unwinding.md`, "What is proven about the emitted code". The unwinder model
(`FV/Unw/Dwarf.lean`) reads what the backend writes:

* LEB128: `uleb?_uleb`, `sleb?_sleb` (decode ∘ encode).
* CFI programs: `decodeCfa?_cfiProgram` — the bytes of `cfiProgram rows` decode to the rows'
  instructions (`insnsOf rows`) for rows at increasing offsets that are multiples of 4, with
  CFA offsets that are multiples of 8 (what `unwindRows` produces).
* LSDA: `decodeLsda?_lsdaBytes` — the call-site table of `lsdaBytes sites` decodes to `sites`.
-/

namespace Backend.Proof.UnwindTables

open Backend

/-! ## LEB128 -/

theorem uleb?_uleb (n : Nat) (rest : List UInt8) :
    Unw.uleb? ((uleb n).data.toList ++ rest) = some (n, rest) := by
  induction n using Nat.strongRecOn generalizing rest with
  | ind n ih =>
    rw [uleb]
    by_cases h : n < 128
    · simp only [h, ite_true]
      simp [Unw.uleb?, UInt8.toNat_ofNat, Nat.mod_eq_of_lt (show n < 256 by omega), h]
    · simp only [h, ite_false, ByteArray.toList_data_append, List.append_assoc]
      have h1 : (UInt8.ofNat (n % 128 + 128)).toNat = n % 128 + 128 := by
        simp [UInt8.toNat_ofNat]; omega
      simp only [List.singleton_append, Unw.uleb?, h1]
      rw [if_neg (by omega), ih (n / 128) (by omega) rest]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
      omega

theorem sleb?_sleb (n : Int) (rest : List UInt8) :
    Unw.sleb? ((sleb n).data.toList ++ rest) = some (n, rest) := by
  induction h : n.natAbs using Nat.strongRecOn generalizing n rest with
  | ind k ih =>
    rw [sleb]
    have hb : (n % 128).toNat < 128 := by omega
    by_cases ht : ((n / 128 == 0 && !decide ((n % 128).toNat ≥ 64)) ||
        (n / 128 == -1 && decide ((n % 128).toNat ≥ 64))) = true
    · simp only [ht, ite_true]
      have h1 : (UInt8.ofNat (n % 128).toNat).toNat = (n % 128).toNat := by
        simp [UInt8.toNat_ofNat]; omega
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not, decide_eq_true_eq] at ht
      simp [Unw.sleb?, h1, show (n % 128).toNat < 128 from hb]
      omega
    · simp only [ht, ite_false, Bool.false_eq_true, ByteArray.toList_data_append,
        List.append_assoc]
      have h1 : (UInt8.ofNat ((n % 128).toNat + 128)).toNat = (n % 128).toNat + 128 := by
        simp [UInt8.toNat_ofNat]; omega
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not, decide_eq_true_eq, not_or, not_and] at ht
      have hb2 : ((n % 128).toNat : Int) = n % 128 :=
        Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
      have h1' : n / 128 ≠ 0 ∨ n % 128 ≥ 64 := by
        by_cases hz : n / 128 = 0
        · have := ht.1 hz; omega
        · exact Or.inl hz
      have h2' : n / 128 ≠ -1 ∨ n % 128 < 64 := by
        by_cases hz : n / 128 = -1
        · have := ht.2 hz; omega
        · exact Or.inl hz
      have hlt : (n / 128).natAbs < k := by omega
      simp only [List.singleton_append, Unw.sleb?, h1]
      rw [if_neg (by omega), ih _ hlt (n / 128) rest rfl]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
      omega

/-! ## CFI programs -/

/-- The decoded instruction of a row's `Cfi`. -/
def _root_.Backend.Cfi.insn : Cfi → Unw.CfaInsn
  | .defCfaOffset o => .defCfaOffset o
  | .defCfaRegister r => .defCfaRegister r
  | .offset r off => .offset r off

/-- A `Cfi` the encoding round-trips: CFA offsets are multiples of the data alignment 8. -/
def _root_.Backend.Cfi.Ok : Cfi → Prop
  | .offset _ off => off % 8 = 0
  | _ => True

theorem decodeCfa1?_bytes (i : Cfi) (hi : i.Ok) (rest : List UInt8) :
    Unw.decodeCfa1? (i.bytes.data.toList ++ rest) = some (i.insn, rest) := by
  cases i with
  | defCfaOffset o =>
    simp only [Cfi.bytes, ByteArray.toList_data_append, List.append_assoc]
    simp [Unw.decodeCfa1?, uleb?_uleb, Cfi.insn]
  | defCfaRegister r =>
    simp only [Cfi.bytes, ByteArray.toList_data_append, List.append_assoc]
    simp [Unw.decodeCfa1?, uleb?_uleb, Cfi.insn]
  | offset r off =>
    simp only [Cfi.Ok] at hi
    simp only [Cfi.bytes]
    by_cases hle : off ≤ 0
    · have hc : (decide (off ≤ 0) && off % 8 == 0) = true := by simp [hle, hi]
      simp only [hc, ite_true]
      by_cases hr : r < 64
      · simp only [hr, ite_true, ByteArray.toList_data_append, List.append_assoc]
        have h1 : (UInt8.ofNat (0x80 + r)).toNat = 128 + r := by
          simp [UInt8.toNat_ofNat]; omega
        simp only [Unw.decodeCfa1?, List.singleton_append, h1]
        rw [if_neg (by omega), if_pos (by omega), uleb?_uleb]
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true, Cfi.insn,
          Unw.CfaInsn.offset.injEq]
        omega
      · simp only [hr, ite_false, ByteArray.toList_data_append, List.append_assoc]
        simp [Unw.decodeCfa1?, uleb?_uleb, Cfi.insn]
        omega
    · have hc : (decide (off ≤ 0) && off % 8 == 0) = false := by simp [hle]
      simp only [hc, Bool.false_eq_true, ite_false, ByteArray.toList_data_append,
        List.append_assoc]
      simp [Unw.decodeCfa1?, uleb?_uleb, sleb?_sleb, Cfi.insn]
      omega

/-- The decoded instructions of `cfiAdvance delta`. -/
def advInsns (delta : Nat) : List Unw.CfaInsn :=
  if delta / 4 = 0 then [] else [.advance (4 * (delta / 4))]

theorem cfiAdvance_empty (delta : Nat) (h : delta / 4 = 0) : cfiAdvance delta = .empty := by
  simp [cfiAdvance, h]

theorem decodeCfa1?_advance (delta : Nat) (h0 : delta / 4 ≠ 0) (hb : delta / 4 < 2 ^ 32)
    (rest : List UInt8) :
    Unw.decodeCfa1? ((cfiAdvance delta).data.toList ++ rest) =
      some (.advance (4 * (delta / 4)), rest) := by
  simp only [cfiAdvance]
  generalize hd : delta / 4 = d at *
  simp only [beq_iff_eq, h0, ite_false]
  by_cases h64 : d < 64
  · simp only [h64, ite_true]
    have h1 : (UInt8.ofNat (0x40 + d)).toNat = 64 + d := by simp [UInt8.toNat_ofNat]; omega
    simp only [List.singleton_append, Unw.decodeCfa1?, h1]
    rw [if_pos (by omega)]
    simp only [Option.some.injEq, Prod.mk.injEq, and_true, Unw.CfaInsn.advance.injEq]
    omega
  · simp only [h64, ite_false]
    by_cases h256 : d < 256
    · simp only [h256, ite_true]
      simp [Unw.decodeCfa1?, UInt8.toNat_ofNat]
      omega
    · simp only [h256, ite_false]
      by_cases h65 : d < 65536
      · simp only [h65, ite_true]
        simp [Unw.decodeCfa1?, Unw.leNat, UInt8.toNat_ofNat]
        omega
      · simp only [h65, ite_false]
        simp [Unw.decodeCfa1?, Unw.leNat, UInt8.toNat_ofNat]
        omega

/-- The decoded instructions of the rows from location `at_`. -/
def insnsFrom : Nat → List (Nat × Cfi) → List Unw.CfaInsn
  | _, [] => []
  | at_, (o, i) :: rows => advInsns (o - at_) ++ i.insn :: insnsFrom o rows

/-- Rows the encoding round-trips: CFA offsets multiples of 8, code offsets below `2 ^ 32`
(the FDE's 32-bit address range). -/
def RowsOk (rows : List (Nat × Cfi)) : Prop := ∀ r ∈ rows, r.2.Ok ∧ r.1 < 2 ^ 32

theorem decodeCfaN?_cons_of (fuel : Nat) (bs rest : List UInt8) (i : Unw.CfaInsn)
    (h : Unw.decodeCfa1? (bs ++ rest) = some (i, rest)) (hne : bs ≠ []) :
    Unw.decodeCfaN? (fuel + 1) (bs ++ rest) = (Unw.decodeCfaN? fuel rest).map (i :: ·) := by
  obtain ⟨b, bs', rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [List.cons_append, Unw.decodeCfaN?.eq_3, ← List.cons_append, h]
  cases h2 : Unw.decodeCfaN? fuel rest <;> simp [h2]

theorem bytes_ne_nil (i : Cfi) : i.bytes.data.toList ≠ [] := by
  cases i <;> simp only [Cfi.bytes] <;> (try split) <;> (try split) <;>
    simp [ByteArray.toList_data_append]

theorem advance_ne_nil (delta : Nat) (h0 : delta / 4 ≠ 0) :
    (cfiAdvance delta).data.toList ≠ [] := by
  simp only [cfiAdvance, beq_iff_eq, h0, ite_false]
  repeat' split
  all_goals simp

theorem decodeCfaN?_from : ∀ (rows : List (Nat × Cfi)) (fuel at_ : Nat), RowsOk rows →
    (cfiProgramFrom at_ rows).data.toList.length ≤ fuel →
    Unw.decodeCfaN? fuel (cfiProgramFrom at_ rows).data.toList = some (insnsFrom at_ rows)
  | [], fuel, at_, _, _ => by cases fuel <;> simp [cfiProgramFrom, insnsFrom, Unw.decodeCfaN?]
  | (o, i) :: rows, fuel, at_, hok, hf => by
    have hr := hok (o, i) (List.mem_cons_self ..)
    have hok' : RowsOk rows := fun r hr => hok r (List.mem_cons_of_mem _ hr)
    have hI := bytes_ne_nil i
    have hIl : 1 ≤ i.bytes.data.toList.length := by
      cases h : i.bytes.data.toList with
      | nil => exact absurd h hI
      | cons _ _ => simp
    simp only [cfiProgramFrom, ByteArray.toList_data_append, List.append_assoc,
      List.length_append] at hf ⊢
    simp only [insnsFrom, advInsns]
    by_cases h0 : (o - at_) / 4 = 0
    · rw [cfiAdvance_empty _ h0] at hf ⊢
      simp only [ByteArray.data_empty, Array.toList_empty, List.nil_append, List.length_nil,
        Nat.zero_add] at hf ⊢
      simp only [h0, ite_true, List.nil_append]
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      rw [decodeCfaN?_cons_of f _ _ _ (decodeCfa1?_bytes i hr.1 _) hI,
        decodeCfaN?_from rows f o hok' (by omega)]
      rfl
    · have hlt : (o - at_) / 4 < 2 ^ 32 := by have := hr.2; omega
      have hA := advance_ne_nil _ h0
      have hAl : 1 ≤ (cfiAdvance (o - at_)).data.toList.length := by
        cases h : (cfiAdvance (o - at_)).data.toList with
        | nil => exact absurd h hA
        | cons _ _ => simp
      simp only [h0, ite_false, List.singleton_append]
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by omega⟩
      rw [decodeCfaN?_cons_of (f + 1) _ _ _ (decodeCfa1?_advance _ h0 hlt _) hA,
        decodeCfaN?_cons_of f _ _ _ (decodeCfa1?_bytes i hr.1 _) hI,
        decodeCfaN?_from rows f o hok' (by omega)]
      rfl

/-- The bytes of `cfiProgram rows` decode to the rows' instructions. -/
theorem decodeCfa?_cfiProgram (rows : List (Nat × Cfi)) (hok : RowsOk rows) :
    Unw.decodeCfa? (cfiProgram rows).data.toList = some (insnsFrom 0 rows) :=
  decodeCfaN?_from rows _ 0 hok (Nat.le_refl _)

/-! ## The LSDA -/

/-- The decoded entry of a call site. -/
def _root_.Backend.CallSite.entry (s : CallSite) : Unw.CallSiteEntry := ⟨s.start, s.len, s.pad, s.action⟩

/-- The bytes of one call-site entry. -/
def siteBytes (s : CallSite) : List UInt8 :=
  (uleb s.start).data.toList ++ (uleb s.len).data.toList ++ (uleb s.pad).data.toList ++
    (uleb s.action).data.toList

theorem uleb_ne_nil (n : Nat) : (uleb n).data.toList ≠ [] := by
  rw [uleb]; split <;> simp [ByteArray.toList_data_append]

theorem entries_bytes (sites : List CallSite) (acc : ByteArray) :
    (sites.foldl (fun b s => b ++ uleb s.start ++ uleb s.len ++ uleb s.pad ++ uleb s.action)
      acc).data.toList = acc.data.toList ++ sites.flatMap siteBytes := by
  induction sites generalizing acc with
  | nil => simp
  | cons s sites ih =>
    simp only [List.foldl_cons, ih, ByteArray.toList_data_append, List.flatMap_cons, siteBytes,
      List.append_assoc]

theorem decodeSitesN?_flat : ∀ (sites : List CallSite) (fuel : Nat),
    (sites.flatMap siteBytes).length ≤ fuel →
    Unw.decodeSitesN? fuel (sites.flatMap siteBytes) = some (sites.map (·.entry))
  | [], fuel, _ => by cases fuel <;> simp [Unw.decodeSitesN?]
  | s :: sites, fuel, hf => by
    have hne : siteBytes s ≠ [] := by
      intro h
      apply uleb_ne_nil s.start
      simp only [siteBytes, List.append_eq_nil_iff] at h
      exact h.1.1.1
    obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil hne
    have hl : 1 ≤ (siteBytes s).length := by rw [hb]; simp
    simp only [List.flatMap_cons, List.length_append] at hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [List.flatMap_cons]
    rw [hb, List.cons_append, Unw.decodeSitesN?.eq_3, ← List.cons_append, ← hb]
    simp only [siteBytes, List.append_assoc, uleb?_uleb, Option.bind_eq_bind, Option.bind_some,
      List.map_cons]
    rw [decodeSitesN?_flat sites f (by omega)]
    rfl

/-- The call-site table of `lsdaBytes sites` decodes to `sites`. -/
theorem decodeLsda?_lsdaBytes (sites : List CallSite) :
    Unw.decodeLsda? (lsdaBytes sites).data.toList = some (sites.map (·.entry)) := by
  obtain ⟨pad, hp⟩ : ∃ pad : Nat, lsdaBytes sites =
      let entries := sites.foldl (fun b s => b ++ uleb s.start ++ uleb s.len ++ uleb s.pad ++
        uleb s.action) ByteArray.empty
      let cs : ByteArray := ⟨#[0x01]⟩ ++ uleb entries.size ++ entries
      let actions : ByteArray := ⟨#[0x01, 0x00]⟩
      let typeInfo := le32 0
      let noPad := cs.size + actions.size + typeInfo.size
      let body : ByteArray := ⟨#[0xff, 0x03]⟩ ++ uleb (noPad + pad) ++ cs ++ actions ++
        ⟨Array.replicate pad 0⟩ ++ typeInfo
      body ++ padTo 4 body.size := ⟨_, rfl⟩
  rw [hp]
  simp only [ByteArray.toList_data_append, List.append_assoc]
  generalize hE : sites.foldl _ ByteArray.empty = E
  have hEb : E.data.toList = sites.flatMap siteBytes := by
    rw [← hE, entries_bytes]; simp
  have hEs : E.size = (sites.flatMap siteBytes).length := by
    rw [← hEb]; simp
  simp only [show (⟨#[0xff, 0x03]⟩ : ByteArray).data.toList = [0xff, 0x03] from rfl,
    show (⟨#[0x01]⟩ : ByteArray).data.toList = [0x01] from rfl, List.cons_append,
    List.nil_append, Unw.decodeLsda?, uleb?_uleb, Option.bind_eq_bind, Option.bind_some]
  rw [hEs, hEb]
  rw [if_pos (by simp), List.take_left' rfl]
  exact decodeSitesN?_flat sites _ (Nat.le_refl _)

/-! ## The call-site table describes the calls -/

/-- The entry of handler `h` of a call returning to `ret`, as the personality reads it. -/
def handlerEntry? (labs : List (Label × Nat)) (ret : Nat) (h : TryHandler) :
    Option Unw.CallSiteEntry :=
  (labs.lookup h.label).bind fun pad => match h with
    | .tag 0 _ => some ⟨ret - 1, 1, pad, 0⟩
    | .tag 1 _ => some ⟨ret - 1, 1, pad, 1⟩
    | _ => none

/-- The entry the personality must find for a call (`some ti` for a `tryCall`) returning to
`ret`: no landing pad for a plain call; for a `try_call` the landing pad of its first handler
(the label's offset in the final code) with the cleanup (tag 0) or catch-all (tag 1)
action. -/
def entryFor (labs : List (Label × Nat)) : Option TryInfo × Nat → Option Unw.CallSiteEntry
  | (c, ret) =>
    match handlersOf c with
    | [] => some ⟨ret - 1, 1, 0, 0⟩
    | h :: _ => handlerEntry? labs ret h

/-- The call-site table `sites` is right for `af` compiled to `fa` (decidable): the `k`-th
`bl`/`blr` of the final code is the `k`-th call of `af`, and the personality's lookup at the
call's return offset − 1 finds that call's entry (`entryFor`). -/
def CallSitesOk (af : AFunc) (fa : FnAsm) (sites : List CallSite) : Prop :=
  let r := scanLines fa.lines.toList 0 [] []
  r.2.length = af.calls.length ∧
  ∀ p ∈ af.calls.zip r.2,
    (entryFor r.1 p).isSome ∧ Unw.lookup (sites.map (·.entry)) (p.2 - 1) = entryFor r.1 p

instance (af : AFunc) (fa : FnAsm) (sites : List CallSite) : Decidable (CallSitesOk af fa sites) := by
  unfold CallSitesOk; infer_instance

/-- The return offsets `scanLines` collects increase strictly and are at least 4. -/
theorem scanLines_rets : ∀ (ls : List Line) (off : Nat) (labs : List (Label × Nat))
    (rets : List Nat), List.Pairwise (· > ·) rets → (∀ x ∈ rets, 4 ≤ x ∧ x ≤ off) →
    List.Pairwise (· < ·) (scanLines ls off labs rets).2 ∧
      ∀ x ∈ (scanLines ls off labs rets).2, 4 ≤ x
  | [], off, labs, rets, hp, hx => by
    simp only [scanLines]
    refine ⟨?_, fun x hm => (hx x (List.mem_reverse.mp hm)).1⟩
    rw [List.pairwise_reverse]; exact hp
  | ln :: rest, off, labs, rets, hp, hx => by
    simp only [scanLines]
    apply scanLines_rets
    · split
      · exact List.Pairwise.cons (fun x hm => by have := hx x hm; omega) hp
      · exact List.Pairwise.cons (fun x hm => by have := hx x hm; omega) hp
      · exact hp
    · intro x hm
      split at hm
      · rcases List.mem_cons.mp hm with rfl | hm
        · simp [Line.size]
        · have := hx x hm; simp [Line.size]; omega
      · rcases List.mem_cons.mp hm with rfl | hm
        · simp [Line.size]
        · have := hx x hm; simp [Line.size]; omega
      · have := hx x hm; have := Nat.le_add_right off ln.size; omega

theorem mapM_ok_cons {α β ε : Type} {f : α → Except ε β} {x : α} {xs : List α} {ys : List β}
    (h : (x :: xs).mapM f = .ok ys) :
    ∃ y ys', ys = y :: ys' ∧ f x = .ok y ∧ xs.mapM f = .ok ys' := by
  simp only [List.mapM_cons] at h
  cases hx : f x with
  | error e => simp [hx] at h; cases h
  | ok y =>
    cases hxs : xs.mapM f with
    | error e => simp [hx, hxs] at h; cases h
    | ok ys' =>
      simp [hx, hxs] at h
      cases h
      exact ⟨y, ys', rfl, rfl, rfl⟩

theorem mapM_ok_mem {α β ε : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
  | [], ys, h, y, hy => by simp at h; cases h; simp at hy
  | x :: xs, ys, h, y, hy => by
    obtain ⟨y0, ys', rfl, h0, hrest⟩ := mapM_ok_cons h
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨x, List.mem_cons_self .., h0⟩
    · obtain ⟨x', hx', h'⟩ := mapM_ok_mem hrest y hy
      exact ⟨x', List.mem_cons_of_mem _ hx', h'⟩

theorem handlerEntry_ok {labs : List (Label × Nat)} {ret : Nat} {h : TryHandler} {e : CallSite}
    (he : handlerEntry labs ret h = .ok e) :
    e.start = ret - 1 ∧ e.len = 1 ∧ handlerEntry? labs ret h = some e.entry := by
  unfold handlerEntry at he
  unfold handlerEntry?
  cases hl : labs.lookup h.label with
  | none => simp [hl] at he
  | some pad =>
    simp only [hl] at he
    rcases h with ⟨n, l⟩ | l
    · rcases n with _ | _ | n
      · simp at he; cases he; simp [CallSite.entry]
      · simp at he; cases he; simp [CallSite.entry]
      · simp at he
    · simp at he

/-- The entries of one call: nonempty, all for `[ret - 1, ret)`, the first one `entryFor`. -/
theorem siteEntries_ok {labs : List (Label × Nat)} {c : Option TryInfo} {ret : Nat}
    {es : List CallSite} (h : siteEntries labs (c, ret) = .ok es) :
    (∀ e ∈ es, e.start = ret - 1 ∧ e.len = 1) ∧
      es.head?.map (·.entry) = entryFor labs (c, ret) ∧ es ≠ [] := by
  unfold siteEntries at h
  unfold entryFor
  cases hs : handlersOf c with
  | nil =>
    simp only [hs, List.isEmpty_nil, ite_true, pure, Except.pure] at h
    cases h
    simp [CallSite.entry, hs]
  | cons hd tl =>
    simp only [hs, List.isEmpty_cons, Bool.false_eq_true, ite_false] at h
    obtain ⟨y, ys, rfl, hy, _⟩ := mapM_ok_cons h
    refine ⟨fun e he => ?_, ?_, by simp⟩
    · obtain ⟨x, _, hx⟩ := mapM_ok_mem h e he
      have := handlerEntry_ok hx
      exact ⟨this.1, this.2.1⟩
    · simp [(handlerEntry_ok hy).2.2, hs]

/-- The personality's lookup in the concatenated entries of calls returning to strictly
increasing offsets finds each call's first entry. -/
theorem lookup_groups {labs : List (Label × Nat)} :
    ∀ (ps : List (Option TryInfo × Nat)) (gs : List (List CallSite)),
      List.Pairwise (· < ·) (ps.map (·.2)) → (∀ p ∈ ps, 4 ≤ p.2) →
      ps.mapM (siteEntries labs) = .ok gs →
      ∀ p ∈ ps, (entryFor labs p).isSome ∧
        Unw.lookup (gs.flatten.map (·.entry)) (p.2 - 1) = entryFor labs p
  | [], _, _, _, _, p, hp => by simp at hp
  | p0 :: ps, gs, hpw, h4, hm, p, hp => by
    obtain ⟨g0, gs', rfl, hg0, hrest⟩ := mapM_ok_cons hm
    obtain ⟨c0, r0⟩ := p0
    obtain ⟨hall, hhead, hne⟩ := siteEntries_ok hg0
    obtain ⟨e0, g0', rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [List.head?_cons, Option.map_some] at hhead
    simp only [List.map_cons, List.pairwise_cons, List.mem_map] at hpw
    rcases List.mem_cons.mp hp with rfl | hp
    · refine ⟨by rw [← hhead]; rfl, ?_⟩
      have := hall e0 (List.mem_cons_self ..)
      simp only [Unw.lookup, List.flatten_cons, List.map_append, List.map_cons, List.cons_append]
      rw [List.find?_cons_of_pos (by simp [CallSite.entry, this.1, this.2]), hhead]
    · obtain ⟨hlt, hpw'⟩ := hpw
      have hgt : r0 < p.2 := hlt p.2 ⟨p, hp, rfl⟩
      have h4p := h4 p (List.mem_cons_of_mem _ hp)
      have h40 := h4 (c0, r0) (List.mem_cons_self ..)
      obtain ⟨hs, hl⟩ := lookup_groups ps gs' hpw' (fun q hq => h4 q (List.mem_cons_of_mem _ hq))
        hrest p hp
      refine ⟨hs, ?_⟩
      rw [← hl]
      simp only [Unw.lookup, List.flatten_cons, List.map_append, List.find?_append]
      rw [List.find?_eq_none.mpr]
      · rfl
      · intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨e, he, rfl⟩ := hx
        have := hall e he
        simp only [CallSite.entry, this.1, this.2, decide_eq_true_eq]
        omega

/-- **The call-site table is right by construction**: whenever `callSites` produces a table,
it satisfies `CallSitesOk`. -/
theorem callSites_ok {af : AFunc} {fa : FnAsm} {sites : List CallSite}
    (h : callSites af fa = .ok (some sites)) : CallSitesOk af fa sites := by
  unfold callSites at h
  by_cases ht : (!af.calls.any (·.isSome)) = true
  · simp only [ht, ite_true] at h
    cases h
  · simp only [ht, Bool.false_eq_true, ite_false] at h
    unfold CallSitesOk
    generalize hr : scanLines fa.lines.toList 0 [] [] = r at h ⊢
    obtain ⟨labs, rets⟩ := r
    simp only at h ⊢
    by_cases hl : (rets.length != af.calls.length) = true
    · simp only [hl, ite_true] at h
      cases h
    · simp only [hl, Bool.false_eq_true, ite_false] at h
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hl
      cases hm : (af.calls.zip rets).mapM (siteEntries labs) with
      | error e => rw [hm] at h; cases h
      | ok gs =>
        rw [hm] at h
        cases h
        have hsr := scanLines_rets fa.lines.toList 0 [] [] .nil (by simp)
        rw [hr] at hsr
        refine ⟨hl, ?_⟩
        apply lookup_groups _ gs _ _ hm
        · rw [List.map_snd_zip (by omega)]; exact hsr.1
        · intro p hp
          exact hsr.2 _ (List.of_mem_zip hp).2

end Backend.Proof.UnwindTables
