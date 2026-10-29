import FV.Backend.Obj
import FV.Unw.Dwarf

/-!
# The emitted unwind tables are correct by construction (S10c, #230)

`docs/plans/unwinding.md`, "What is proven about the emitted code". The unwinder model
(`FV/Unw/Dwarf.lean`) reads what the backend writes:

* LEB128: `uleb?_uleb`, `sleb?_sleb` (decode ∘ encode).
* CFI programs: `decodeCfa?_cfiProgram` — the bytes of `cfiProgram rows` decode to the rows'
  instructions (`insnsFrom 0 rows`) for rows whose CFA offsets are multiples of 8 and whose
  code offsets fit the FDE's 32 bits (`RowsOk`, what `unwindRows` produces).
* The rows describe the frame: `unwindRows_frame` — for a function with a frame, at every
  call's return offset − 1 the row (CIE then FDE, `Unw.rowAt cieInsns`) is `frameRow saved`
  (Cranelift's): CFA = x29 + 16 (the entry sp), x29 at CFA − 16, x30 at CFA − 8, and each
  register the prologue pushes `(DWARF register, CFA offset)` (`pushRows`); `unwindRows_leaf`:
  a function without a frame has the CIE's row (CFA = sp, return address in x30).
* LSDA: `decodeLsda?_lsdaBytes` — the call-site table of `lsdaBytes sites` decodes to `sites`;
  `callSites_ok` — the personality's lookup at each call's return offset − 1 finds that
  call's entry (`CallSitesOk`: no landing pad for a plain call; the first handler's landing
  pad and action for a `try_call`).
* Non-vacuity: `Witness.call_row` (a function with a frame, a saved x19 and a `try_call`).
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
    unfold retsAfter
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

/-! ## The CFI rows describe the frame -/

/-- A call instruction (`bl`/`blr`). -/
def callInsn? : Option Insn → Bool
  | some (.bl _) | some (.blr _) => true
  | _ => false

/-- A call instruction line (`bl`/`blr`). -/
def _root_.Backend.Line.isCall (l : Line) : Bool := callInsn? l.insn?

theorem loadConst64_noCall (rd : Reg) (v : Nat) : ∀ l ∈ loadConst64 rd v, l.isCall = false := by
  intro l hl
  simp only [loadConst64, List.mem_cons, List.mem_filterMap, List.mem_range] at hl
  rcases hl with rfl | ⟨j, _, hj⟩
  · rfl
  · split at hj
    · cases hj; rfl
    · cases hj

theorem spAdjLines_noCall (sub : Bool) (size : Nat) : ∀ l ∈ spAdjLines sub size, l.isCall = false := by
  intro l hl
  unfold spAdjLines at hl
  split at hl
  · simp at hl
  · split at hl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl; subst hl; cases sub <;> rfl
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with hl | rfl
      · exact loadConst64_noCall _ _ l hl
      · cases sub <;> rfl

theorem pushLines_noCall (int : Bool) (rs : List Reg) : ∀ l ∈ pushLines int rs, l.isCall = false := by
  intro l hl
  unfold pushLines at hl
  generalize pairsOf rs = po at hl
  obtain ⟨ps, o⟩ := po
  simp only [List.mem_append, List.mem_map] at hl
  rcases hl with hl | ⟨p, -, rfl⟩
  · cases o with
    | none => simp at hl
    | some r => simp only [List.mem_singleton] at hl; subst hl; cases int <;> rfl
  · cases int <;> rfl

theorem prologueLines_noCall {calls : Bool} (saves : List Reg) (size : Nat) :
    ∀ l ∈ prologueLines saves size calls, l.isCall = false := by
  intro l hl
  simp only [prologueLines, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with ((((rfl | rfl) | hl) | hl) | hl) | hl
  · rfl
  · rfl
  · rcases probeLines_mem hl with rfl | rfl | ⟨_, rfl⟩ <;> rfl
  · exact pushLines_noCall _ _ l hl
  · exact pushLines_noCall _ _ l hl
  · exact spAdjLines_noCall true _ l hl

/-- Rows at nondecreasing offsets from `at_`, a multiple of 4 apart, up to `hi`. -/
def RowsIn (at_ hi : Nat) : List (Nat × Cfi) → Prop
  | [] => True
  | (o, _) :: rs => at_ ≤ o ∧ o ≤ hi ∧ (o - at_) % 4 = 0 ∧ RowsIn o hi rs

theorem RowsIn.mono {at_ hi hi' : Nat} (h : hi ≤ hi') : ∀ {rows}, RowsIn at_ hi rows → RowsIn at_ hi' rows
  | [], _ => trivial
  | (o, _) :: rs, ⟨h1, h2, h3, h4⟩ => ⟨h1, by omega, h3, RowsIn.mono h h4⟩

theorem RowsIn.le {at_ hi : Nat} : ∀ {rows}, RowsIn at_ hi rows → ∀ r ∈ rows, r.1 ≤ hi
  | [], _, _, hr => by simp at hr
  | (o, _) :: rs, ⟨_, h2, _, h4⟩, r, hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact h2
    · exact RowsIn.le h4 r hr

theorem RowsIn.lower {a b hi : Nat} : ∀ {rows}, RowsIn a hi rows → b ≤ a → (a - b) % 4 = 0 →
    RowsIn b hi rows
  | [], _, _, _ => trivial
  | (o, _) :: rs, ⟨h1, h2, h3, h4⟩, hb, hm => ⟨by omega, h2, by omega, h4⟩

/-- The `(register, CFA offset)` of an `offset` row. -/
def offsetPair (r : Nat × Cfi) : Nat × Int :=
  match r.2 with
  | .offset d o => (d, o)
  | _ => (0, 0)

/-- Rows at offset `o`, then rows from `o` on: rows from below `o`. -/
theorem RowsIn.same {o hi : Nat} (hoh : o ≤ hi) :
    ∀ (G : List (Nat × Cfi)) {a : Nat} {rest : List (Nat × Cfi)}, a ≤ o → (o - a) % 4 = 0 →
      (∀ x ∈ G, x.1 = o) → RowsIn o hi rest → RowsIn a hi (G ++ rest)
  | [], _, _, hao, hm, _, h => h.lower hao hm
  | (o', c) :: G, _, _, hao, hm, hG, h => by
    obtain rfl : o' = o := hG _ (List.mem_cons_self ..)
    rw [List.cons_append]
    exact ⟨hao, hoh, hm, RowsIn.same hoh G (Nat.le_refl _) (by simp)
      (fun x hx => hG x (List.mem_cons_of_mem _ hx)) h⟩

/-- Rows of numbered groups, group `i`'s at `start + 4 (i + 1)`. -/
theorem RowsIn.flat (start : Nat) (F : List Reg × Nat → List (Nat × Cfi))
    (hF : ∀ g i, ∀ x ∈ F (g, i), x.1 = start + 4 * (i + 1)) :
    ∀ (gs : List (List Reg)) (n : Nat),
      RowsIn (start + 4 * n) (start + 4 * n + 4 * gs.length) ((gs.zipIdx n).flatMap F)
  | [], _ => by simp [RowsIn]
  | g :: gs, n => by
    rw [List.zipIdx_cons, List.flatMap_cons]
    have := RowsIn.flat start F hF gs (n + 1)
    rw [show start + 4 * (n + 1) + 4 * gs.length = start + 4 * n + 4 * (g :: gs).length by
      simp only [List.length_cons]; omega] at this
    exact RowsIn.same (o := start + 4 * (n + 1)) (by simp only [List.length_cons]; omega) _
      (by omega) (by omega)
      (hF g n) this

theorem pushGroups_length (int : Bool) (rs : List Reg) :
    (pushGroups rs).length = (pushLines int rs).length := by
  unfold pushGroups pushLines
  generalize pairsOf rs = po
  obtain ⟨ps, o⟩ := po
  cases o <;> simp

theorem clobberOff_mod8 (saves : List Reg) (r : Reg) : clobberOff saves r % 8 = 0 := by
  unfold clobberOff
  split <;> (try simp only [pushBytes]) <;> omega

/-- The push rows: after each push (from `start + 4` on, one push a line), an `offset` row with
a CFA offset of a multiple of 8 for each register it saves. -/
theorem pushRows_spec (saves : List Reg) (start : Nat) :
    RowsIn start (start + 4 * (pushGroups (savesInt saves) ++ pushGroups (savesFloat saves)).length)
      (pushRows saves start) ∧
    ∀ r ∈ pushRows saves start, ∃ d o, r.2 = .offset d o ∧ o % 8 = 0 := by
  refine ⟨?_, fun x hx => ?_⟩
  · unfold pushRows
    refine RowsIn.flat start _ ?_ _ 0
    intro g i x hx
    simp only [List.mem_filterMap, Option.map_eq_some_iff] at hx
    obtain ⟨r, -, dr, -, rfl⟩ := hx
    rfl
  · simp only [pushRows, List.mem_flatMap, List.mem_filterMap, Option.map_eq_some_iff] at hx
    obtain ⟨⟨g, i⟩, -, r, -, dr, -, rfl⟩ := hx
    refine ⟨dr, _, rfl, ?_⟩
    have h1 := clobberOff_mod8 saves r
    have h2 : clobberBytes saves % 8 = 0 := by simp only [clobberBytes, pushBytes]; omega
    omega

/-! ### Rows to the row at a code offset -/

theorem rowAtFrom_insn (pc : Nat) (row : Unw.Row) (loc : Nat) (i : Cfi) (is : List Unw.CfaInsn) :
    Unw.rowAtFrom pc row loc (i.insn :: is) = Unw.rowAtFrom pc (row.exec i.insn) loc is := by
  cases i <;> rfl

/-- Past every row, the row at `pc` is every row's instruction executed in order. -/
theorem rowAtFrom_insnsFrom (pc : Nat) : ∀ (rows : List (Nat × Cfi)) (row : Unw.Row) (at_ : Nat),
    RowsIn at_ pc rows →
    Unw.rowAtFrom pc row at_ (insnsFrom at_ rows) = rows.foldl (fun r x => r.exec x.2.insn) row
  | [], row, at_, _ => by simp [insnsFrom, Unw.rowAtFrom]
  | (o, i) :: rows, row, at_, ⟨h1, h2, h3, h4⟩ => by
    simp only [insnsFrom, advInsns, List.foldl_cons]
    by_cases h0 : (o - at_) / 4 = 0
    · have : o = at_ := by omega
      subst this
      simp only [h0, ite_true, List.nil_append, rowAtFrom_insn]
      exact rowAtFrom_insnsFrom pc rows _ _ h4
    · simp only [h0, ite_false, List.singleton_append, Unw.rowAtFrom]
      rw [if_pos (by omega), show at_ + 4 * ((o - at_) / 4) = o by omega, rowAtFrom_insn]
      exact rowAtFrom_insnsFrom pc rows _ _ h4

/-- The CIE's initial instructions (`DW_CFA_def_cfa sp, 0`, both CIEs of `ehFrame`). -/
def cieInsns : List Unw.CfaInsn := [.defCfa 31 0]

theorem decodeCfa?_cie : Unw.decodeCfa? [0x0c, 31, 0] = some cieInsns := by decide

/-- The row of a function with a frame at its call sites (Cranelift's): CFA = x29 + 16 (the
entry sp: the body keeps x29 = entry sp − 16), x29 at CFA − 16, x30 (the return address) at
CFA − 8, each pushed callee-saved register `(d, off)` at CFA + `off` (latest rule first). -/
def frameRow (saved : List (Nat × Int)) : Unw.Row :=
  { cfaReg := 29, cfaOff := 16, saved := saved.reverse ++ [(30, -8), (29, -16)] }

/-- The row of a function without a frame: the CIE's (CFA = sp, return address in x30). -/
def leafRow : Unw.Row := { cfaReg := 31, cfaOff := 0 }

theorem foldl_saveRows (rows : List (Nat × Cfi)) (h8 : ∀ r ∈ rows, ∃ d o, r.2 = .offset d o ∧ o % 8 = 0)
    (row : Unw.Row) :
    rows.foldl (fun r x => r.exec x.2.insn) row =
      { row with saved := (rows.map offsetPair).reverse ++ row.saved } := by
  induction rows generalizing row with
  | nil => simp
  | cons x rows ih =>
    obtain ⟨d, o, hx, _⟩ := h8 x (List.mem_cons_self ..)
    rw [List.foldl_cons, ih (fun r hr => h8 r (List.mem_cons_of_mem _ hr))]
    obtain ⟨xo, xi⟩ := x
    simp only at hx
    subst hx
    simp [Unw.Row.exec, Cfi.insn, offsetPair]

/-! ### Calls come after the prologue and the saves -/

theorem retsAfter_noCall {ln : Line} {off : Nat} {rets : List Nat} (h : ln.isCall = false) :
    retsAfter ln off rets = rets := by
  rcases ln with ⟨i, t⟩ | ⟨t, b⟩ | ⟨l⟩
  · cases i <;> first | rfl | simp [Line.isCall, Line.insn?, callInsn?] at h
  · rfl
  · rfl

theorem scanLines_noCall : ∀ (pre rest : List Line) (off : Nat) (labs : List (Label × Nat))
    (rets : List Nat), (∀ l ∈ pre, l.isCall = false) →
    ∃ labs', scanLines (pre ++ rest) off labs rets =
      scanLines rest (off + (pre.map Line.size).sum) labs' rets
  | [], rest, off, labs, rets, _ => ⟨labs, by simp⟩
  | ln :: pre, rest, off, labs, rets, h => by
    obtain ⟨labs', hs⟩ := scanLines_noCall pre rest (off + ln.size) (labsAfter ln off labs) rets
      (fun l hm => h l (List.mem_cons_of_mem _ hm))
    refine ⟨labs', ?_⟩
    simp only [List.cons_append, scanLines, retsAfter_noCall (h ln (List.mem_cons_self ..)), hs,
      List.map_cons, List.sum_cons, Nat.add_assoc]

/-- Every return offset `scanLines` collects from offset `off` on is at least `off + 4`. -/
theorem scanLines_rets_ge : ∀ (ls : List Line) (off lo : Nat) (labs : List (Label × Nat))
    (rets : List Nat), (∀ x ∈ rets, lo ≤ x) → lo ≤ off + 4 →
    ∀ x ∈ (scanLines ls off labs rets).2, lo ≤ x
  | [], off, lo, labs, rets, hx, _ => by
    simp only [scanLines, List.mem_reverse]; exact hx
  | ln :: rest, off, lo, labs, rets, hx, hlo => by
    simp only [scanLines]
    unfold retsAfter
    apply scanLines_rets_ge rest _ lo
    · intro x hm
      split at hm
      · rcases List.mem_cons.mp hm with rfl | hm
        · omega
        · exact hx x hm
      · rcases List.mem_cons.mp hm with rfl | hm
        · omega
        · exact hx x hm
      · exact hx x hm
    · omega

theorem insn?_isCall {l l' : Line} (h : l.insn? = l'.insn?) : l.isCall = l'.isCall := by
  simp [Line.isCall, h]

theorem size_of_insn? : ∀ (ls : List Line), ls.all (·.insn?.isSome) = true →
    (ls.map Line.size).sum = 4 * ls.length
  | [], _ => rfl
  | l :: ls, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have := size_of_insn? ls h.2
    cases l with
    | ins i t => simp [Line.size, this]; omega
    | word t b => simp [Line.insn?] at h
    | label l => simp [Line.insn?] at h

theorem noCall_of_insn? : ∀ (got expect : List Line), got.map Line.insn? = expect.map Line.insn? →
    (∀ l ∈ expect, l.isCall = false) → ∀ l ∈ got, l.isCall = false
  | [], _, _, _, l, hl => by simp at hl
  | _ :: _, [], h, _, _, _ => by simp at h
  | g :: got, e :: expect, h, he, l, hl => by
    simp only [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.mp hl with rfl | hl
    · rw [insn?_isCall h.1]; exact he e (List.mem_cons_self ..)
    · exact noCall_of_insn? got expect h.2 (fun l hm => he l (List.mem_cons_of_mem _ hm)) l hl

/-- **The CFI rows describe the frame at every call** (`unwindRows`, a function with a frame):
the rows round-trip through the `.eh_frame` encoding, and at every call's return offset − 1
(where the unwinder looks up a frame suspended at that call) the row is `frameRow saved`,
`saved` being the `(DWARF register, CFA offset)` of the prologue's pushes. -/
theorem unwindRows_frame {af : AFunc} {fa : FnAsm} {rows : List (Nat × Cfi)}
    (h : unwindRows af fa = .ok rows) (hf : af.frame = true) :
    RowsOk rows ∧ ∀ ret ∈ (scanLines fa.lines.toList 0 [] []).2,
      Unw.rowAt cieInsns (insnsFrom 0 rows) (ret - 1) =
        frameRow ((pushRows af.saves 8).map offsetPair) := by
  unfold unwindRows at h
  simp only [hf, Bool.not_true, Bool.false_eq_true, ite_false] at h
  cases hb : af.blocks[0]? with
  | none => simp [hb] at h
  | some lc =>
  obtain ⟨lab, code⟩ := lc
  simp only [hb] at h
  by_cases hp : (code.toList.head? != some AInst.prologue) = true
  · simp [hp, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  simp only [hp, Bool.false_eq_true, ite_false] at h
  generalize hpro : prologueLines af.saves af.frameSize af.isCaller = pro at h
  by_cases hz : 4 * pro.length ≥ 2 ^ 32
  · rw [if_pos hz] at h
    simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  rw [if_neg hz] at h
  split at h
  rotate_left
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  rename_i l0 hl0
  split at h
  rotate_left
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  rename_i hc
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hmap, hall⟩ := hc
  obtain ⟨hin, h8⟩ := pushRows_spec af.saves 8
  have hexpNC : ∀ l ∈ pro, l.isCall = false := fun l hl => prologueLines_noCall _ _ l (hpro ▸ hl)
  generalize hn : pro.length = n at hmap hall hz
  have hpush : 8 + 4 * (pushGroups (savesInt af.saves) ++ pushGroups (savesFloat af.saves)).length ≤
      4 * n := by
    rw [← hn, ← hpro, List.length_append, pushGroups_length true, pushGroups_length false]
    simp only [prologueLines, List.length_append, List.length_cons, List.length_nil]
    omega
  generalize hgot : List.take n (List.drop 1 fa.lines.toList) = got at hmap hall
  have hglen : got.length = n := by
    have := congrArg List.length hmap
    simp only [List.length_map] at this
    omega
  have hgotNC := noCall_of_insn? got _ hmap hexpNC
  have hRin : RowsIn 0 (4 * n) (prologueRows ++ pushRows af.saves 8) :=
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, hin.mono hpush⟩
  refine ⟨fun r hr => ?_, ?_⟩
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [prologueRows, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [Cfi.Ok]
    · obtain ⟨d, o, h2, ho⟩ := h8 r hr
      refine ⟨by rw [h2]; exact ho, ?_⟩
      have := hin.le r hr
      omega
  intro ret hret
  have hlines : fa.lines.toList = (Line.label l0 :: got) ++ List.drop n (List.drop 1 fa.lines.toList) := by
    rw [List.cons_append, ← hgot, List.take_append_drop]
    have h0 : fa.lines.toList.head? = some (Line.label l0) := by
      rw [List.head?_eq_getElem?]; simpa using hl0
    obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp h0
    rw [hys]; rfl
  rw [hlines] at hret
  obtain ⟨labs', hsc⟩ := scanLines_noCall (Line.label l0 :: got)
    (List.drop n (List.drop 1 fa.lines.toList)) 0 [] []
    (fun l hl => by
      rcases List.mem_cons.mp hl with rfl | hl
      · rfl
      · exact hgotNC l hl)
  rw [hsc] at hret
  have hsz : ((Line.label l0 :: got).map Line.size).sum = 4 * n := by
    simp only [List.map_cons, List.sum_cons, Line.size, Nat.zero_add]
    rw [size_of_insn? got hall, hglen]
  rw [hsz] at hret
  have hge := scanLines_rets_ge _ _ (4 * n + 4) _ _ (by simp) (by omega) ret hret
  simp only [Unw.rowAt, cieInsns]
  rw [rowAtFrom_insnsFrom _ _ _ _ (hRin.mono (by omega)), List.foldl_append,
    foldl_saveRows (pushRows af.saves 8) h8]
  simp [frameRow, prologueRows, Unw.rowAtFrom, Unw.Row.exec, Cfi.insn]


/-- A function without a frame has no rows: the CIE's row (CFA = sp, return address in x30)
holds everywhere. -/
theorem unwindRows_leaf {af : AFunc} {fa : FnAsm} {rows : List (Nat × Cfi)}
    (h : unwindRows af fa = .ok rows) (hf : af.frame = false) (pc : Nat) :
    rows = [] ∧ Unw.rowAt cieInsns (insnsFrom 0 rows) pc = leafRow := by
  unfold unwindRows at h
  simp only [hf, Bool.not_false, ite_true, pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, rfl⟩


/-! ## Non-vacuity: a function with a frame, a callee-save and a `try_call` -/

namespace Witness

/-- Block 0: the prologue (which pushes x19) and a `try_call f` whose catch handler is block 2. -/
def af : AFunc where
  name := "w"
  frameSize := 16
  slotBase := 0
  blocks := #[(0, #[.prologue, .inst (.tryCall ⟨.sym "f", [], []⟩ ⟨1, [.tag 1 2], false, 0⟩)]),
    (1, #[.epilogueRet]), (2, #[.epilogueRet])]
  saves := [.x 19]

/-- Its final code, unwind rows and call-site table. -/
def fa : FnAsm := (emitFunc 0 af).toOption.getD default
def rows : List (Nat × Cfi) :=
  [(4, .defCfaOffset 16), (4, .offset 29 (-16)), (4, .offset 30 (-8)), (8, .defCfaRegister 29),
    (12, .offset 19 (-32))]
def sites : List CallSite := [⟨15, 1, 28, 1⟩]

theorem ok_of_toOption {ε α : Type} {e : Except ε α} {x : α} (h : e.toOption = some x) :
    e = .ok x := by
  cases e <;> simp_all [Except.toOption]

theorem rows_ok : unwindRows af fa = .ok rows := ok_of_toOption (by decide +kernel)
theorem sites_ok : callSites af fa = .ok (some sites) := ok_of_toOption (by decide +kernel)
theorem calls : af.calls.zip [16] = [(some ⟨1, [.tag 1 2], false, 0⟩, 16)] := by decide +kernel
theorem rets : (scanLines fa.lines.toList 0 [] []).2 = [16] := by decide +kernel

/-- At the `bl f` (return offset 16) the unwinder finds the frame row with x19 at CFA − 32,
and the personality the landing pad at offset 28 (block 2) with the catch action; both tables
round-trip through their encodings. -/
theorem call_row :
    Unw.rowAt cieInsns (insnsFrom 0 rows) (16 - 1) = frameRow [(19, -32)] ∧
    Unw.lookup (sites.map (·.entry)) (16 - 1) = some ⟨15, 1, 28, 1⟩ ∧
    Unw.decodeCfa? (cfiProgram rows).data.toList = some (insnsFrom 0 rows) ∧
    Unw.decodeLsda? (lsdaBytes sites).data.toList = some (sites.map (·.entry)) := by
  obtain ⟨hok, hrow⟩ := unwindRows_frame rows_ok rfl
  have hsaved : (pushRows af.saves 8).map offsetPair = [(19, -32)] := by decide +kernel
  obtain ⟨-, hcs⟩ := callSites_ok sites_ok
  refine ⟨?_, ?_, decodeCfa?_cfiProgram rows hok, decodeLsda?_lsdaBytes sites⟩
  · rw [← hsaved]; exact hrow 16 (by rw [rets]; simp)
  · rw [(hcs (some ⟨1, [.tag 1 2], false, 0⟩, 16) (by rw [rets, calls]; simp)).2]
    decide +kernel

end Witness

end Backend.Proof.UnwindTables
