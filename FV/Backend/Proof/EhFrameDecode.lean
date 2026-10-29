module

public import FV.Unw.EhFrame
public import FV.Backend.Proof.UnwindTables
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Format.Basic
import all Init.Data.Int.Repr
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Nat.Gcd
import all Init.Data.Range.Basic
import all Init.Data.Repr
import all Init.Prelude
import all Init.Data.String.Basic
import all Init.Data.String.Defs
import all Init.Data.Nat.Power2.Basic
import all Init.Data.List.Basic
import all Init.Data.Option.Basic
import all Init.Control.Except

@[expose] public section

/-!
# The emitted `.eh_frame` / `.gcc_except_table` decode to the unwinder's tables (S10f)

The bytes `Backend.ehFrame` and `Backend.lsdaBytes` (`FV/Backend/Obj.lean`) write, placed and
relocated by the linker, read by the unwinder's model (`FV/Unw/EhFrame.lean`), give exactly the
tables the per-function theorem with unwinding assumes (`hcie`, `hfde`, `hlsda` of
`E2E.backend_correct_final_cleanup_unwind`): `T.cie = cieInsns`, `T.fde = insnsFrom 0 rows`,
`T.lsda` the call-site table.

* Bytes: `le_bytes4`/`le_bytes8`, `leNat_le4` (little-endian fields), `sdata4_le4`,
  `pcrel4_le4` (a `pcrel | sdata4` pointer written by `R_AARCH64_PREL32` denotes its target).
* Prefix stability of the decoders (`uleb?_append`, `sleb?_append`, `decodeCfa1?_append`,
  `decodeCfaN?_append`): decoding a prefix decodes it in any extension.
* `decodeCfa?_prog_pad`: an FDE's instructions followed by `DW_CFA_nop` padding decode to the
  rows' instructions (`noNops`).
* The entries: `parseCie_zR`, `parseCie_zLPR` (the two CIEs `ehFrame` writes, whatever the
  relocated personality pointer), `parseFde_plain`, `parseFde_lsda` (an FDE as `ehFrame` writes
  it, with its relocated `pc_begin` and LSDA pointer).
* The linker (the placement assumption, explicit): `linkSection` writes each relocation's
  value (`R_AARCH64_PREL32` `S + A − P`, `R_AARCH64_PREL64`) at its offset; `Fits` (the
  PREL32 values fit 32 bits, the targets 64) is what a successful link guarantees.
* The section: `entries_none`/`entries_lsda` (the linked `ehFrame` bytes split into the CIE(s)
  and one entry per function), `ehFdes_ehFrame` (they decode to `decodedFde` per function:
  `pc_begin` = the function's address, the LSDA pointer its LSDA's, the rows' instructions).
* `tablesAt_ehFrame`: for a pc of a function (first FDE covering it) whose LSDA is the
  `lsdaBytes` at its offset of `.gcc_except_table`, the unwinder's lookup yields
  `⟨cieInsns, insnsFrom 0 rows, lsda.map (List.map (·.entry))⟩` (`decodeLsda?_append`: the
  following LSDAs do not matter). Witness: `EhWitness.tables`.
-/

namespace Backend.Proof.EhFrameDecode

open Backend Backend.Proof.UnwindTables Unw

/-! ## Little-endian fields -/

theorem le_bytes4 (n : Nat) : (le 4 n).data.toList =
    [UInt8.ofNat n, UInt8.ofNat (n >>> 8), UInt8.ofNat (n >>> 16), UInt8.ofNat (n >>> 24)] := by
  simp [le, ByteArray.push, List.range', List.foldl]
  rfl

theorem le_bytes8 (n : Nat) : (le 8 n).data.toList =
    [UInt8.ofNat n, UInt8.ofNat (n >>> 8), UInt8.ofNat (n >>> 16), UInt8.ofNat (n >>> 24),
      UInt8.ofNat (n >>> 32), UInt8.ofNat (n >>> 40), UInt8.ofNat (n >>> 48),
      UInt8.ofNat (n >>> 56)] := by
  simp [le, ByteArray.push, List.range', List.foldl]
  rfl

theorem leNat_le4 (n : Nat) : leNat (le 4 n).data.toList = n % 2 ^ 32 := by
  rw [le_bytes4]
  simp [leNat, UInt8.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem sdata4_le4 {v : Int} (h1 : -2 ^ 31 ≤ v) (h2 : v < 2 ^ 31) :
    sdata4 (le 4 (v % 2 ^ 32).toNat).data.toList = v := by
  simp only [sdata4, leNat_le4]
  have hm : 0 ≤ v % 2 ^ 32 := Int.emod_nonneg _ (by decide)
  have hl : v % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by decide)
  have e : (((v % 2 ^ 32).toNat % 2 ^ 32 : Nat) : Int) = v % 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt (by omega)]; exact Int.toNat_of_nonneg hm
  split <;> omega

/-- **A `pcrel | sdata4` pointer the linker wrote for target `S` at address `P`** (`R_AARCH64_PREL32`:
`S + A − P` as 4 bytes; the linker checks that it fits in 32 bits) denotes `S`. -/
theorem pcrel4_le4 {P S : Nat} (hS : S < 2 ^ 64) (h1 : -2 ^ 31 ≤ (S : Int) - P)
    (h2 : (S : Int) - P < 2 ^ 31) :
    pcrel4 P (le 4 (((S : Int) - P) % 2 ^ 32).toNat).data.toList = S := by
  simp only [pcrel4]
  rw [sdata4_le4 h1 h2]
  rw [show (P : Int) + ((S : Int) - P) = S by omega]
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  simp

/-! ## Prefix stability of the decoders -/

theorem uleb?_append : ∀ {bs rest : List UInt8} {n : Nat} {r : List UInt8},
    uleb? bs = some (n, r) → uleb? (bs ++ rest) = some (n, r ++ rest)
  | [], _, _, _, h => by simp [uleb?] at h
  | b :: bs, rest, n, r, h => by
    simp only [uleb?] at h
    simp only [List.cons_append, uleb?]
    split at h
    · rename_i hb
      simp only [hb, ite_true, Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    · rename_i hb
      simp only [hb, ite_false]
      cases h' : uleb? bs with
      | none => simp [h'] at h
      | some p =>
        obtain ⟨m, r'⟩ := p
        simp only [h', Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [uleb?_append h']
        rfl

theorem sleb?_append : ∀ {bs rest : List UInt8} {n : Int} {r : List UInt8},
    sleb? bs = some (n, r) → sleb? (bs ++ rest) = some (n, r ++ rest)
  | [], _, _, _, h => by simp [sleb?] at h
  | b :: bs, rest, n, r, h => by
    simp only [sleb?] at h
    simp only [List.cons_append, sleb?]
    split at h
    · rename_i hb
      simp only [hb, ite_true, Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    · rename_i hb
      simp only [hb, ite_false]
      cases h' : sleb? bs with
      | none => simp [h'] at h
      | some p =>
        obtain ⟨m, r'⟩ := p
        simp only [h', Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [sleb?_append h']
        rfl

theorem map_append {α : Type} {o : Option (α × List UInt8)} {f : α → CfaInsn}
    {o' : Option (α × List UInt8)} {rest : List UInt8}
    (ho : ∀ a r, o = some (a, r) → o' = some (a, r ++ rest)) {i : CfaInsn} {r : List UInt8}
    (h : o.map (fun x => (f x.1, x.2)) = some (i, r)) :
    o'.map (fun x => (f x.1, x.2)) = some (i, r ++ rest) := by
  cases ho' : o with
  | none => rw [ho'] at h; cases h
  | some p =>
    obtain ⟨a, r0⟩ := p
    rw [ho'] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [ho a r0 ho']
    simp

theorem decodeCfa1?_append {bs rest : List UInt8} {i : CfaInsn} {r : List UInt8}
    (h : decodeCfa1? bs = some (i, r)) : decodeCfa1? (bs ++ rest) = some (i, r ++ rest) := by
  cases bs with
  | nil => simp [decodeCfa1?] at h
  | cons b bs =>
    rw [List.cons_append]
    dsimp only [decodeCfa1?] at h ⊢
    by_cases c1 : b.toNat / 64 = 1
    · rw [if_pos c1] at h ⊢
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    rw [if_neg c1] at h ⊢
    by_cases c2 : b.toNat / 64 = 2
    · rw [if_pos c2] at h ⊢
      exact map_append (f := fun (x : Nat) => .offset (b.toNat % 64) (-8 * x))
        (fun a r h => uleb?_append h) h
    rw [if_neg c2] at h ⊢
    by_cases c3 : b.toNat = 0x00
    · rw [if_pos c3] at h ⊢
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    rw [if_neg c3] at h ⊢
    by_cases c4 : b.toNat = 0x02
    · rw [if_pos c4] at h ⊢
      rcases bs with _ | ⟨d, r0⟩
      · cases h
      · simp only [List.cons_append, Option.some.injEq, Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, rfl⟩
    rw [if_neg c4] at h ⊢
    by_cases c5 : b.toNat = 0x03
    · rw [if_pos c5] at h ⊢
      rcases bs with _ | ⟨d0, _ | ⟨d1, r0⟩⟩
      · cases h
      · cases h
      · simp only [List.cons_append, Option.some.injEq, Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, rfl⟩
    rw [if_neg c5] at h ⊢
    by_cases c6 : b.toNat = 0x04
    · rw [if_pos c6] at h ⊢
      rcases bs with _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, _ | ⟨d3, r0⟩⟩⟩⟩
      · cases h
      · cases h
      · cases h
      · cases h
      · simp only [List.cons_append, Option.some.injEq, Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, rfl⟩
    rw [if_neg c6] at h ⊢
    by_cases c7 : b.toNat = 0x05
    · rw [if_pos c7] at h ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨⟨reg, r1⟩, h1, ⟨f, r2⟩, h2, h3⟩ := h
      exact ⟨(reg, r1 ++ rest), uleb?_append h1, (f, r2 ++ rest), uleb?_append h2,
        by simp only [pure, Option.some.injEq, Prod.mk.injEq] at h3 ⊢
           obtain ⟨rfl, rfl⟩ := h3; exact ⟨rfl, rfl⟩⟩
    rw [if_neg c7] at h ⊢
    by_cases c8 : b.toNat = 0x0c
    · rw [if_pos c8] at h ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨⟨reg, r1⟩, h1, ⟨f, r2⟩, h2, h3⟩ := h
      exact ⟨(reg, r1 ++ rest), uleb?_append h1, (f, r2 ++ rest), uleb?_append h2,
        by simp only [pure, Option.some.injEq, Prod.mk.injEq] at h3 ⊢
           obtain ⟨rfl, rfl⟩ := h3; exact ⟨rfl, rfl⟩⟩
    rw [if_neg c8] at h ⊢
    by_cases c9 : b.toNat = 0x0d
    · rw [if_pos c9] at h ⊢
      exact map_append (f := fun x => .defCfaRegister x) (fun a r h => uleb?_append h) h
    rw [if_neg c9] at h ⊢
    by_cases c10 : b.toNat = 0x0e
    · rw [if_pos c10] at h ⊢
      exact map_append (f := fun x => .defCfaOffset x) (fun a r h => uleb?_append h) h
    rw [if_neg c10] at h ⊢
    by_cases c11 : b.toNat = 0x11
    · rw [if_pos c11] at h ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨⟨reg, r1⟩, h1, ⟨f, r2⟩, h2, h3⟩ := h
      exact ⟨(reg, r1 ++ rest), uleb?_append h1, (f, r2 ++ rest), sleb?_append h2,
        by simp only [pure, Option.some.injEq, Prod.mk.injEq] at h3 ⊢
           obtain ⟨rfl, rfl⟩ := h3; exact ⟨rfl, rfl⟩⟩
    rw [if_neg c11] at h
    cases h

theorem decodeCfaN?_mono : ∀ {n : Nat} {bs : List UInt8} {is : List CfaInsn} (k : Nat),
    decodeCfaN? n bs = some is → decodeCfaN? (n + k) bs = some is
  | _, [], is, k, h => by
    cases k <;> simp_all [decodeCfaN?]
  | 0, _ :: _, _, _, h => by simp [decodeCfaN?] at h
  | n + 1, b :: bs, is, k, h => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [decodeCfaN?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨⟨i, r⟩, h1, is', h2, h3⟩ := h
    exact ⟨(i, r), h1, is', decodeCfaN?_mono k h2, h3⟩

theorem decodeCfaN?_append : ∀ {n m : Nat} {bs rest : List UInt8} {is js : List CfaInsn},
    decodeCfaN? n bs = some is → decodeCfaN? m rest = some js →
    decodeCfaN? (n + m) (bs ++ rest) = some (is ++ js)
  | n, m, [], rest, is, js, h, h' => by
    have : is = [] := by cases n <;> simpa [decodeCfaN?, eq_comm] using h
    subst this
    simpa [Nat.add_comm] using decodeCfaN?_mono n h'
  | 0, _, _ :: _, _, _, _, h, _ => by simp [decodeCfaN?] at h
  | n + 1, m, b :: bs, rest, is, js, h, h' => by
    simp only [decodeCfaN?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨i, r⟩, h1, is', h2, h3⟩ := h
    simp only [pure, Option.some.injEq] at h3
    subst h3
    rw [show n + 1 + m = (n + m) + 1 by omega, List.cons_append]
    simp only [decodeCfaN?, Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨(i, r ++ rest), ?_, is' ++ js, decodeCfaN?_append h2 h', rfl⟩
    have := decodeCfa1?_append (rest := rest) h1
    simpa using this

theorem decodeCfaN?_zeros : ∀ k : Nat,
    decodeCfaN? k (List.replicate k 0) = some (List.replicate k .nop)
  | 0 => rfl
  | k + 1 => by
    rw [List.replicate_succ]
    have h1 : decodeCfa1? ((0 : UInt8) :: List.replicate k 0) = some (.nop, List.replicate k 0) := by
      simp [decodeCfa1?]
    simp only [decodeCfaN?, Option.bind_eq_bind, h1, Option.bind_some, decodeCfaN?_zeros k]
    rfl

/-! ## The FDE's instructions with padding -/

theorem insnsFrom_noNop : ∀ (at_ : Nat) (rows : List (Nat × Cfi)), CfaInsn.nop ∉ insnsFrom at_ rows
  | _, [] => by simp [insnsFrom]
  | at_, (o, i) :: rows => by
    simp only [insnsFrom, advInsns, List.mem_append, List.mem_cons, not_or]
    refine ⟨?_, ?_, insnsFrom_noNop o rows⟩
    · split <;> simp
    · cases i <;> simp [Cfi.insn]

theorem noNops_pad (is : List CfaInsn) (h : CfaInsn.nop ∉ is) (k : Nat) :
    noNops (is ++ List.replicate k .nop) = is := by
  simp only [noNops, List.filter_append]
  rw [List.filter_eq_self.2 (fun a ha => by
    have : a ≠ .nop := fun e => h (e ▸ ha)
    simpa using this)]
  simp [List.filter_replicate]

/-- An FDE's instruction bytes followed by `k` bytes of `DW_CFA_nop` padding decode to the
rows' instructions and the padding. -/
theorem decodeCfa?_prog_pad (rows : List (Nat × Cfi)) (hok : RowsOk rows) (k : Nat) :
    decodeCfa? ((cfiProgram rows).data.toList ++ List.replicate k 0) =
      some (insnsFrom 0 rows ++ List.replicate k .nop) := by
  unfold decodeCfa?
  rw [List.length_append, List.length_replicate]
  exact decodeCfaN?_append (decodeCfa?_cfiProgram rows hok) (decodeCfaN?_zeros k)

theorem padTo_toList (a n : Nat) : (padTo a n).data.toList = List.replicate ((a - n % a) % a) 0 := by
  simp [padTo]

theorem take?_append {A B : List UInt8} {n : Nat} (h : A.length = n) :
    take? n (A ++ B) = some (A, B) := by
  subst h
  simp [take?]

theorem uleb0 : (uleb 0).data.toList = [0] := by
  rw [uleb]; rfl

theorem uleb4 : (uleb 4).data.toList = [4] := by
  rw [uleb]; rfl

theorem le4_length (n : Nat) : (le 4 n).data.toList.length = 4 := by rw [le_bytes4]; rfl

/-! ## The entries `ehFrame` writes -/

/-- The body of an entry as `ehFrame`'s `entry` pads it (to a multiple of 8 with the length
field). -/
def padded (body : List UInt8) : List UInt8 :=
  body ++ List.replicate ((8 - (4 + body.length) % 8) % 8) 0

/-- The bytes of an entry as `ehFrame` writes it: the length field and the padded body. -/
def entryBytes (body : List UInt8) : List UInt8 :=
  (le 4 (padded body).length).data.toList ++ padded body

/-- The `zR` CIE's body (`ehFrame`). -/
def cieZRBody : List UInt8 :=
  (le 4 0).data.toList ++ [1] ++ "zR".toUTF8.data.toList ++ [0] ++ (uleb 4).data.toList ++
    (sleb (-8)).data.toList ++ [30, 1, 0x1b, 0x0c, 31, 0]

/-- The `zLPR` CIE's body (`ehFrame`), the personality pointer's 8 bytes `pers` as the linker
wrote them. -/
def cieZLPRBody (pers : List UInt8) : List UInt8 :=
  (le 4 0).data.toList ++ [1] ++ "zLPR".toUTF8.data.toList ++ [0] ++ (uleb 4).data.toList ++
    (sleb (-8)).data.toList ++ [30] ++ (uleb 11).data.toList ++ [0x1b, 0x9c] ++ pers ++
    [0x1b, 0x0c, 31, 0]

theorem zR_bytes : "zR".toUTF8.data.toList = [0x7a, 0x52] := by rfl
theorem zLPR_bytes : "zLPR".toUTF8.data.toList = [0x7a, 0x4c, 0x50, 0x52] := by rfl
theorem sleb_m8 : (sleb (-8)).data.toList = [0x78] := by rw [sleb]; rfl
theorem uleb11 : (uleb 11).data.toList = [11] := by rw [uleb]; rfl
theorem le4_0 : (le 4 0).data.toList = [0, 0, 0, 0] := by rw [le_bytes4]; rfl
theorem take?_zero (bs : List UInt8) : take? 0 bs = some ([], bs) := by simp [take?]

/-- The `zR` CIE decodes (no LSDA, CFA = sp + 0). -/
theorem parseCie_zR : parseCie ((padded cieZRBody).drop 4) = some ⟨false, cieInsns⟩ := by
  decide +kernel

/-- The `zLPR` CIE decodes, whatever the personality pointer's bytes. -/
theorem parseCie_zLPR (v : Nat) :
    parseCie ((padded (cieZLPRBody (le 8 v).data.toList)).drop 4) = some ⟨true, cieInsns⟩ := by
  simp only [cieZLPRBody, le_bytes8, zLPR_bytes, sleb_m8, uleb11, le4_0, uleb4]
  simp [parseCie, padded, take?, cstr?, uleb?, sleb?, augLsda?, augZR, augZLPR, guard,
    decodeCfa?, decodeCfaN?, decodeCfa1?, noNops, cieInsns]

/-- **An FDE without an LSDA** as `ehFrame` writes it (after the CIE pointer: `pc_begin` as the
linker wrote it, `pc_range`, empty augmentation data, the rows' instructions, padding). -/
theorem parseFde_plain {cie : Cie} (hc : cie.lsda = false) (a : Nat) {pb : List UInt8}
    (hpb : pb.length = 4) (size : Nat) {rows : List (Nat × Cfi)} (hok : RowsOk rows) (k : Nat) :
    parseFde cie a (pb ++ (le 4 size).data.toList ++ (uleb 0).data.toList ++
      (cfiProgram rows).data.toList ++ List.replicate k 0) =
      some ⟨pcrel4 a pb, size % 2 ^ 32, none, insnsFrom 0 rows, cie.insns⟩ := by
  simp only [parseFde, List.append_assoc, take?_append hpb, take?_append (le4_length size), uleb0,
    Option.bind_eq_bind, Option.bind_some, List.cons_append, List.nil_append]
  simp only [uleb?, show (0 : UInt8).toNat = 0 by decide, show (0 : Nat) < 128 by decide,
    ite_true, Option.bind_some, take?_zero, hc, Bool.false_eq_true, ite_false]
  simp only [decodeCfa?_prog_pad rows hok k, Option.bind_some, pure, leNat_le4,
    noNops_pad _ (insnsFrom_noNop 0 rows) k]

/-- **An FDE with an LSDA** as `ehFrame` writes it: the augmentation data is the LSDA pointer
`lp` as the linker wrote it, at address `a + 9`. -/
theorem parseFde_lsda {cie : Cie} (hc : cie.lsda = true) (a : Nat) {pb lp : List UInt8}
    (hpb : pb.length = 4) (hlp : lp.length = 4) (size : Nat) {rows : List (Nat × Cfi)}
    (hok : RowsOk rows) (k : Nat) :
    parseFde cie a (pb ++ (le 4 size).data.toList ++ (uleb 4).data.toList ++ lp ++
      (cfiProgram rows).data.toList ++ List.replicate k 0) =
      some ⟨pcrel4 a pb, size % 2 ^ 32, some (pcrel4 (a + 9) lp), insnsFrom 0 rows,
        cie.insns⟩ := by
  simp only [parseFde, List.append_assoc, take?_append hpb, take?_append (le4_length size), uleb4,
    Option.bind_eq_bind, Option.bind_some, List.cons_append, List.nil_append]
  simp only [uleb?, show (4 : UInt8).toNat = 4 by decide, show (4 : Nat) < 128 by decide,
    ite_true, Option.bind_some, take?_append hlp, hc]
  simp only [decodeCfa?_prog_pad rows hok k, Option.bind_some, pure, leNat_le4,
    noNops_pad _ (insnsFrom_noNop 0 rows) k, List.length_cons, List.length_append]
  simp only [Option.some.injEq, Fde.mk.injEq, and_true, true_and]
  rw [Nat.add_sub_cancel_left]

/-! ## `ehFrame` as a fold -/

/-- A `for` loop whose body always continues is a fold. -/
theorem forIn_yield_foldl {α σ : Type} (l : List α) (init : σ) (f : α → σ → Id (ForInStep σ))
    (g : σ → α → σ) (h : ∀ a b, f a b = pure (.yield (g b a))) :
    forIn l init f = pure (l.foldl g init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => rw [List.forIn_cons, h, List.foldl_cons, ← ih]; rfl

/-- An entry as `ehFrame` writes it. -/
def entryB (body : ByteArray) : ByteArray :=
  le32 (body ++ padTo 8 (4 + body.size)).size ++ (body ++ padTo 8 (4 + body.size))

/-- The body of the FDE `ehFrame` writes at offset `at_` for `x = (start, size, rows, lsda?)`
(the LSDA functions' CIE at `cieP`). -/
def fdeBodyB (at_ cieP : Nat) (x : Nat × Nat × List (Nat × Cfi) × Option Nat) : ByteArray :=
  match x.2.2.2 with
  | none => le32 (at_ + 4) ++ le32 0 ++ le32 x.2.1 ++ uleb 0 ++ cfiProgram x.2.2.1
  | some _ => le32 (at_ + 4 - cieP) ++ le32 0 ++ le32 x.2.1 ++ uleb 4 ++ le32 0 ++ cfiProgram x.2.2.1

/-- The relocations of that FDE: its LSDA pointer (symbol `gcc`, addend the LSDA's offset) and
its `pc_begin` (the `.text` section symbol 1, addend the function's offset). -/
def fdeRelocs (at_ gcc : Nat) (x : Nat × Nat × List (Nat × Cfi) × Option Nat) :
    List (Nat × Nat × Nat × Int) :=
  match x.2.2.2 with
  | none => [(at_ + 8, 261, 1, x.1)]
  | some lo => [(at_ + 17, 261, gcc, lo), (at_ + 8, 261, 1, x.1)]

/-- One iteration of `ehFrame`'s loop. -/
def ehStep (cieP gcc : Nat) (st : ByteArray × Array (Nat × Nat × Nat × Int))
    (x : Nat × Nat × List (Nat × Cfi) × Option Nat) : ByteArray × Array (Nat × Nat × Nat × Int) :=
  (st.1 ++ entryB (fdeBodyB st.1.size cieP x), st.2 ++ (fdeRelocs st.1.size gcc x).toArray)

/-- The `zR` CIE entry `ehFrame` writes. -/
def cieZRB : ByteArray :=
  entryB (le32 0 ++ ⟨#[1]⟩ ++ "zR".toUTF8 ++ ⟨#[0]⟩ ++ uleb 4 ++ sleb (-8) ++
    ⟨#[30, 1, 0x1b, 0x0c, 31, 0]⟩)

/-- The `zLPR` CIE entry `ehFrame` writes. -/
def cieZLPRB : ByteArray :=
  entryB (le32 0 ++ ⟨#[1]⟩ ++ "zLPR".toUTF8 ++ ⟨#[0]⟩ ++ uleb 4 ++ sleb (-8) ++
    ⟨#[30]⟩ ++ uleb 11 ++ ⟨#[0x1b, 0x9c]⟩ ++ le64 0 ++ ⟨#[0x1b, 0x0c, 31, 0]⟩)

/-- **`ehFrame` as a fold** over the functions, from the CIE(s). -/
theorem ehFrame_eq (fdes : List (Nat × Nat × List (Nat × Cfi) × Option Nat)) (gcc dwref : Nat) :
    ehFrame fdes gcc dwref =
      if fdes.any (·.2.2.2.isSome) then
        let st := fdes.foldl (ehStep cieZRB.size gcc)
          (cieZRB ++ cieZLPRB, #[(cieZRB.size + 14 + 6, 260, dwref, 0)])
        (st.1, st.2.toList)
      else
        let st := fdes.foldl (ehStep 0 gcc) (cieZRB, #[])
        (st.1, st.2.toList) := by
  simp only [ehFrame, Id.run]
  split
  · simp only [bind, pure]
    rw [forIn_yield_foldl _ _ _ (ehStep _ gcc) fun a b => by
      rcases a with ⟨st, sz, rows, _ | lo⟩ <;> rfl]
    rfl
  · simp only [bind, pure]
    rw [forIn_yield_foldl _ _ _ (ehStep _ gcc) fun a b => by
      rcases a with ⟨st, sz, rows, _ | lo⟩ <;> rfl]
    rfl

/-! ## The section as a list of entries -/

theorem size_toList (b : ByteArray) : b.size = b.data.toList.length := rfl

/-- The FDE entries (bytes, relocations) the loop appends from offset `at_`. -/
def fdeEntries (cieP gcc : Nat) : Nat → List (Nat × Nat × List (Nat × Cfi) × Option Nat) →
    List UInt8 × List (Nat × Nat × Nat × Int)
  | _, [] => ([], [])
  | at_, x :: xs =>
    let e := (entryB (fdeBodyB at_ cieP x)).data.toList
    let r := fdeEntries cieP gcc (at_ + e.length) xs
    (e ++ r.1, fdeRelocs at_ gcc x ++ r.2)

theorem foldl_ehStep (cieP gcc : Nat) :
    ∀ (fdes : List (Nat × Nat × List (Nat × Cfi) × Option Nat))
      (st : ByteArray × Array (Nat × Nat × Nat × Int)),
      (fdes.foldl (ehStep cieP gcc) st).1.data.toList =
          st.1.data.toList ++ (fdeEntries cieP gcc st.1.size fdes).1 ∧
        (fdes.foldl (ehStep cieP gcc) st).2.toList =
          st.2.toList ++ (fdeEntries cieP gcc st.1.size fdes).2
  | [], st => by simp [fdeEntries]
  | x :: xs, st => by
    obtain ⟨h1, h2⟩ := foldl_ehStep cieP gcc xs (ehStep cieP gcc st x)
    simp only [List.foldl_cons, fdeEntries]
    refine ⟨?_, ?_⟩
    · rw [h1]
      simp only [ehStep, ByteArray.toList_data_append, List.append_assoc, size_toList,
        List.length_append]
    · rw [h2]
      simp only [ehStep, Array.toList_append, List.append_assoc, size_toList,
        ByteArray.toList_data_append, List.length_append, List.toList_toArray]

/-! ## The linker's relocations (the placement assumption) -/

/-- Overwrite the bytes at offset `o` with `v`. -/
def writeAt (bs : List UInt8) (o : Nat) (v : List UInt8) : List UInt8 :=
  bs.take o ++ v ++ bs.drop (o + v.length)

/-- The bytes the linker writes for a relocation `(offset, type, symbol, addend)` of a section at
`secAddr`, with the symbols at `symAddr`: `R_AARCH64_PREL64` (260) and `R_AARCH64_PREL32`
(261) write `S + A − P` (P = the field's address) as 8 and 4 bytes (AAELF64 §5.7.3); the
backend's `.eh_frame` has no other type. -/
def relocBytes (secAddr : Nat) (symAddr : Nat → Nat) : Nat × Nat × Nat × Int → List UInt8
  | (o, t, s, a) =>
    let v : Int := (symAddr s : Int) + a - ((secAddr + o : Nat) : Int)
    if t = 260 then (le 8 (v % 2 ^ 64).toNat).data.toList
    else if t = 261 then (le 4 (v % 2 ^ 32).toNat).data.toList
    else []

/-- **The linked section**: the section's bytes with its relocations resolved (the linker places
the section at `secAddr` and symbol `s` at `symAddr s`). -/
def linkSection (bs : List UInt8) (relocs : List (Nat × Nat × Nat × Int)) (secAddr : Nat)
    (symAddr : Nat → Nat) : List UInt8 :=
  relocs.foldl (fun bs r => writeAt bs r.1 (relocBytes secAddr symAddr r)) bs

theorem writeAt_mid (A Z B v : List UInt8) (h : Z.length = v.length) :
    writeAt (A ++ Z ++ B) A.length v = A ++ v ++ B := by
  simp only [writeAt, List.append_assoc, List.take_left', List.drop_append, h]
  simp [List.drop_eq_nil_of_le, h]

theorem writeAt_left (A B v : List UInt8) (o : Nat) (h : o + v.length ≤ A.length) :
    writeAt (A ++ B) o v = writeAt A o v ++ B := by
  simp only [writeAt, List.take_append_of_le_length (by omega : o ≤ A.length),
    List.drop_append_of_le_length h, List.append_assoc]

theorem writeAt_right (A B v : List UInt8) (o : Nat) :
    writeAt (A ++ B) (A.length + o) v = A ++ writeAt B o v := by
  simp only [writeAt, List.take_append, List.drop_append, List.append_assoc]
  simp [List.take_of_length_le, List.drop_eq_nil_of_le, Nat.add_assoc]

theorem writeAt_length (bs v : List UInt8) (o : Nat) (h : o + v.length ≤ bs.length) :
    (writeAt bs o v).length = bs.length := by
  simp only [writeAt, List.length_append, List.length_take, List.length_drop]
  omega

theorem relocBytes_length (secAddr : Nat) (symAddr : Nat → Nat) (r : Nat × Nat × Nat × Int) :
    (relocBytes secAddr symAddr r).length ≤ 8 := by
  obtain ⟨o, t, s, a⟩ := r
  simp only [relocBytes]
  split
  · rw [le_bytes8]; simp
  · split
    · rw [le_bytes4]; simp
    · simp

theorem relocBytes_261 (secAddr : Nat) (symAddr : Nat → Nat) (o s : Nat) (a : Int) :
    relocBytes secAddr symAddr (o, 261, s, a) =
      (le 4 (((symAddr s : Int) + a - ((secAddr + o : Nat) : Int)) % 2 ^ 32).toNat).data.toList := by
  simp [relocBytes]

theorem relocBytes_260 (secAddr : Nat) (symAddr : Nat → Nat) (o s : Nat) (a : Int) :
    relocBytes secAddr symAddr (o, 260, s, a) =
      (le 8 (((symAddr s : Int) + a - ((secAddr + o : Nat) : Int)) % 2 ^ 64).toNat).data.toList := by
  simp [relocBytes]

theorem entryB_toList (b : ByteArray) :
    (entryB b).data.toList = (le 4 (padded b.data.toList).length).data.toList ++ padded b.data.toList := by
  simp only [entryB, ByteArray.toList_data_append, padTo_toList, padded, size_toList,
    List.length_append, List.length_replicate, le32]

/-- The body (after the length field) of an FDE entry after linking: `pc_begin` (and the LSDA
pointer) resolved. -/
def linkedFdeBody (secAddr : Nat) (symAddr : Nat → Nat) (at_ cieP gcc : Nat)
    (x : Nat × Nat × List (Nat × Cfi) × Option Nat) : List UInt8 :=
  let body := (fdeBodyB at_ cieP x).data.toList
  let pad := List.replicate ((8 - (4 + body.length) % 8) % 8) 0
  let pb := relocBytes secAddr symAddr (at_ + 8, 261, 1, x.1)
  match x.2.2.2 with
  | none => (le 4 (at_ + 4)).data.toList ++ pb ++
      (le 4 x.2.1).data.toList ++ (uleb 0).data.toList ++ (cfiProgram x.2.2.1).data.toList ++ pad
  | some lo => (le 4 (at_ + 4 - cieP)).data.toList ++
      pb ++ (le 4 x.2.1).data.toList ++ (uleb 4).data.toList ++
      relocBytes secAddr symAddr (at_ + 17, 261, gcc, lo) ++ (cfiProgram x.2.2.1).data.toList ++ pad

/-- An FDE entry after linking. -/
def linkedFde (secAddr : Nat) (symAddr : Nat → Nat) (at_ cieP gcc : Nat)
    (x : Nat × Nat × List (Nat × Cfi) × Option Nat) : List UInt8 :=
  (le 4 (padded (fdeBodyB at_ cieP x).data.toList).length).data.toList ++
    linkedFdeBody secAddr symAddr at_ cieP gcc x

theorem linkSection_append (bs : List UInt8) (r1 r2 : List (Nat × Nat × Nat × Int)) (secAddr : Nat)
    (symAddr : Nat → Nat) :
    linkSection bs (r1 ++ r2) secAddr symAddr =
      linkSection (linkSection bs r1 secAddr symAddr) r2 secAddr symAddr := by
  simp [linkSection, List.foldl_append]

theorem writeAt3 (P X Y Z B v : List UInt8) (hX : X.length = 4) (hY : Y.length = 4)
    (hZ : Z.length = v.length) :
    writeAt (P ++ (X ++ (Y ++ (Z ++ B)))) (P.length + 8) v = P ++ (X ++ (Y ++ (v ++ B))) := by
  rw [show P ++ (X ++ (Y ++ (Z ++ B))) = (P ++ X ++ Y) ++ Z ++ B by simp,
    show P.length + 8 = (P ++ X ++ Y).length by simp [hX, hY], writeAt_mid _ _ _ _ hZ]
  simp

theorem writeAt6 (P X Y W S U Z B v : List UInt8) (hX : X.length = 4) (hY : Y.length = 4)
    (hW : W.length = 4) (hS : S.length = 4) (hU : U.length = 1) (hZ : Z.length = v.length) :
    writeAt (P ++ (X ++ (Y ++ (W ++ (S ++ (U ++ (Z ++ B))))))) (P.length + 17) v =
      P ++ (X ++ (Y ++ (W ++ (S ++ (U ++ (v ++ B)))))) := by
  rw [show P ++ (X ++ (Y ++ (W ++ (S ++ (U ++ (Z ++ B)))))) = (P ++ X ++ Y ++ W ++ S ++ U) ++ Z ++ B
      by simp,
    show P.length + 17 = (P ++ X ++ Y ++ W ++ S ++ U).length by simp [hX, hY, hW, hS, hU],
    writeAt_mid _ _ _ _ hZ]
  simp

theorem relocBytes261_length (secAddr : Nat) (symAddr : Nat → Nat) (o s : Nat) (a : Int) :
    (relocBytes secAddr symAddr (o, 261, s, a)).length = 4 := by
  rw [relocBytes_261, le4_length]

theorem le4_size (n : Nat) : (le 4 n).size = 4 := by rw [size_toList, le4_length]

theorem linkedFdeBody_length (secAddr : Nat) (symAddr : Nat → Nat) (at_ cieP gcc : Nat)
    (x : Nat × Nat × List (Nat × Cfi) × Option Nat) :
    (linkedFdeBody secAddr symAddr at_ cieP gcc x).length =
      (padded (fdeBodyB at_ cieP x).data.toList).length := by
  obtain ⟨st, sz, rows, _ | lo⟩ := x <;>
    simp only [linkedFdeBody, padded, fdeBodyB, ByteArray.toList_data_append, le32, le4_length,
      relocBytes261_length, List.length_append, List.length_replicate]

/-- Linking one FDE entry in place. -/
theorem link_fde (secAddr : Nat) (symAddr : Nat → Nat) (cieP gcc : Nat)
    (x : Nat × Nat × List (Nat × Cfi) × Option Nat) (P R : List UInt8) :
    linkSection (P ++ (entryB (fdeBodyB P.length cieP x)).data.toList ++ R)
        (fdeRelocs P.length gcc x) secAddr symAddr =
      P ++ linkedFde secAddr symAddr P.length cieP gcc x ++ R := by
  obtain ⟨st, sz, rows, _ | lo⟩ := x
  · simp only [fdeRelocs, linkSection, List.foldl_cons, List.foldl_nil, entryB_toList, linkedFde,
      linkedFdeBody]
    simp only [padded, fdeBodyB, ByteArray.toList_data_append, List.append_assoc, le32]
    rw [writeAt3 _ _ _ _ _ _ (le4_length _) (le4_length _)
      (by rw [le4_length, relocBytes261_length])]
  · simp only [fdeRelocs, linkSection, List.foldl_cons, List.foldl_nil, entryB_toList, linkedFde,
      linkedFdeBody]
    simp only [padded, fdeBodyB, ByteArray.toList_data_append, List.append_assoc, le32]
    rw [writeAt6 _ _ _ _ _ _ _ _ _ (le4_length _) (le4_length _) (le4_length _) (le4_length _)
      (by rw [uleb4]; rfl) (by rw [le4_length, relocBytes261_length])]
    rw [writeAt3 _ _ _ _ _ _ (le4_length _) (le4_length _)
      (by rw [le4_length, relocBytes261_length])]

theorem entryB_length (b : ByteArray) :
    (entryB b).data.toList.length = 4 + (padded b.data.toList).length := by
  rw [entryB_toList, List.length_append, le4_length]

/-- The linked FDE entries from offset `at_`. -/
def linkedFdes (secAddr : Nat) (symAddr : Nat → Nat) (cieP gcc : Nat) :
    Nat → List (Nat × Nat × List (Nat × Cfi) × Option Nat) → List UInt8
  | _, [] => []
  | at_, x :: xs => linkedFde secAddr symAddr at_ cieP gcc x ++
      linkedFdes secAddr symAddr cieP gcc (at_ + (entryB (fdeBodyB at_ cieP x)).data.toList.length) xs

/-- **Linking the FDEs**: the relocations of the FDE entries, resolved entry by entry. -/
theorem link_fdes (secAddr : Nat) (symAddr : Nat → Nat) (cieP gcc : Nat) :
    ∀ (xs : List (Nat × Nat × List (Nat × Cfi) × Option Nat)) (P : List UInt8),
      linkSection (P ++ (fdeEntries cieP gcc P.length xs).1) (fdeEntries cieP gcc P.length xs).2
          secAddr symAddr =
        P ++ linkedFdes secAddr symAddr cieP gcc P.length xs
  | [], P => by simp [fdeEntries, linkSection, linkedFdes]
  | x :: xs, P => by
    simp only [fdeEntries, linkedFdes]
    rw [linkSection_append, ← List.append_assoc, link_fde]
    have hl : (P ++ linkedFde secAddr symAddr P.length cieP gcc x).length =
        P.length + (entryB (fdeBodyB P.length cieP x)).data.toList.length := by
      simp only [List.length_append, linkedFde, linkedFdeBody_length, le4_length, entryB_length]
    rw [← hl, link_fdes secAddr symAddr cieP gcc xs, List.append_assoc]

/-- The entries of the linked FDEs: offset and body. -/
def fdeEntryList (secAddr : Nat) (symAddr : Nat → Nat) (cieP gcc : Nat) :
    Nat → List (Nat × Nat × List (Nat × Cfi) × Option Nat) → List (Nat × List UInt8)
  | _, [] => []
  | at_, x :: xs => (at_, linkedFdeBody secAddr symAddr at_ cieP gcc x) ::
      fdeEntryList secAddr symAddr cieP gcc (at_ + (entryB (fdeBodyB at_ cieP x)).data.toList.length) xs

theorem entriesN_entry (fuel off L : Nat) (body rest : List UInt8) (hb : body.length = L)
    (h0 : L ≠ 0) (hL : L < 0xffffffff) :
    entriesN (fuel + 1) off ((le 4 L).data.toList ++ body ++ rest) =
      (entriesN fuel (off + 4 + L) rest).map ((off, body) :: ·) := by
  have hne : (le 4 L).data.toList ++ body ++ rest ≠ [] := by
    rw [le_bytes4]; simp
  obtain ⟨b, bs, hbs⟩ := List.exists_cons_of_ne_nil hne
  rw [hbs, entriesN.eq_3, ← hbs, List.append_assoc, take?_append (le4_length L)]
  simp only [Option.bind_eq_bind, Option.bind_some, leNat_le4, Nat.mod_eq_of_lt (by omega : L < 2 ^ 32),
    h0, ite_false, show L ≠ 0xffffffff by omega, take?_append hb]
  cases entriesN fuel (off + 4 + L) rest <;> rfl

theorem padded_fde_length (at_ cieP : Nat) (x : Nat × Nat × List (Nat × Cfi) × Option Nat) :
    13 ≤ (padded (fdeBodyB at_ cieP x).data.toList).length ∧
      (padded (fdeBodyB at_ cieP x).data.toList).length ≤
        (cfiProgram x.2.2.1).data.toList.length + 24 := by
  obtain ⟨st, sz, rows, _ | lo⟩ := x <;>
    simp only [padded, fdeBodyB, ByteArray.toList_data_append, le32, le4_length, uleb0, uleb4,
      List.length_append, List.length_replicate, List.length_cons, List.length_nil] <;> omega

/-- The linked FDE entries are entries. -/
theorem entriesN_fdes (secAddr : Nat) (symAddr : Nat → Nat) (cieP gcc : Nat) :
    ∀ (xs : List (Nat × Nat × List (Nat × Cfi) × Option Nat)) (at_ fuel : Nat),
      xs.length ≤ fuel → (∀ x ∈ xs, (cfiProgram x.2.2.1).data.toList.length + 24 < 0xffffffff) →
      entriesN fuel at_ (linkedFdes secAddr symAddr cieP gcc at_ xs) =
        some (fdeEntryList secAddr symAddr cieP gcc at_ xs)
  | [], at_, fuel, _, _ => by cases fuel <;> simp [linkedFdes, fdeEntryList, entriesN]
  | x :: xs, at_, fuel, hf, hb => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hx := padded_fde_length at_ cieP x
    have hbx := hb x List.mem_cons_self
    simp only [linkedFdes, fdeEntryList, linkedFde, List.append_assoc]
    rw [← List.append_assoc, entriesN_entry f at_ _ _ _ (linkedFdeBody_length ..) (by omega)
      (by omega), entryB_length, ← Nat.add_assoc,
      entriesN_fdes secAddr symAddr cieP gcc xs _ f (by simp at hf; omega)
        fun y hy => hb y (List.mem_cons_of_mem _ hy)]
    rfl

/-! ## The FDEs of the linked section -/

theorem take4_cieZR : take? 4 (padded cieZRBody) = some ([0, 0, 0, 0], (padded cieZRBody).drop 4) := by
  decide +kernel

theorem take4_cieZLPR (pers : List UInt8) :
    take? 4 (padded (cieZLPRBody pers)) = some ([0, 0, 0, 0], (padded (cieZLPRBody pers)).drop 4) := by
  simp only [take?, padded, cieZLPRBody, le4_0, List.length_append, List.length_cons,
    List.length_nil, List.length_replicate]
  rw [if_pos (by omega)]
  simp

/-- The FDE of a linked entry without an LSDA (its CIE the `zR` one at offset 0). -/
theorem fdeOf_plain (es : List (Nat × List UInt8)) (addr : Nat) (symAddr : Nat → Nat)
    (at_ cieP gcc : Nat) (x : Nat × Nat × List (Nat × Cfi) × Option Nat) (hx : x.2.2.2 = none)
    (hok : RowsOk x.2.2.1) (hat : at_ + 4 < 2 ^ 32) (hes : es.lookup 0 = some (padded cieZRBody)) :
    fdeOf es addr at_ (linkedFdeBody addr symAddr at_ cieP gcc x) =
      some (some ⟨pcrel4 (addr + at_ + 8) (relocBytes addr symAddr (at_ + 8, 261, 1, x.1)),
        x.2.1 % 2 ^ 32, none, insnsFrom 0 x.2.2.1, cieInsns⟩) := by
  obtain ⟨st, sz, rows, lsda⟩ := x
  simp only at hx hok ⊢
  subst hx
  simp only [fdeOf, linkedFdeBody, List.append_assoc]
  rw [take?_append (le4_length _)]
  simp only [Option.bind_eq_bind, Option.bind_some, leNat_le4, Nat.mod_eq_of_lt hat,
    show at_ + 4 ≠ 0 by omega, ite_false, Nat.sub_self, hes, take4_cieZR, guard,
    show at_ + 4 ≤ at_ + 4 from Nat.le_refl _, ite_true, decide_true]
  simp only [pure, Option.bind_some, show leNat [0, 0, 0, 0] = 0 by rfl, ite_true, parseCie_zR]
  rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc,
    parseFde_plain (cie := ⟨false, cieInsns⟩) rfl _ (relocBytes261_length ..) sz hok]
  rfl

/-- The FDE of a linked entry with an LSDA (its CIE the `zLPR` one at offset `cieP`). -/
theorem fdeOf_lsda (es : List (Nat × List UInt8)) (addr : Nat) (symAddr : Nat → Nat)
    (at_ cieP gcc : Nat) (x : Nat × Nat × List (Nat × Cfi) × Option Nat) {lo : Nat}
    (hx : x.2.2.2 = some lo) (hok : RowsOk x.2.2.1) (hat : at_ + 4 < 2 ^ 32) (hcp : cieP ≤ at_)
    {v : Nat} (hes : es.lookup cieP = some (padded (cieZLPRBody (le 8 v).data.toList))) :
    fdeOf es addr at_ (linkedFdeBody addr symAddr at_ cieP gcc x) =
      some (some ⟨pcrel4 (addr + at_ + 8) (relocBytes addr symAddr (at_ + 8, 261, 1, x.1)),
        x.2.1 % 2 ^ 32,
        some (pcrel4 (addr + at_ + 8 + 9) (relocBytes addr symAddr (at_ + 17, 261, gcc, lo))),
        insnsFrom 0 x.2.2.1, cieInsns⟩) := by
  obtain ⟨st, sz, rows, lsda⟩ := x
  simp only at hx hok ⊢
  subst hx
  simp only [fdeOf, linkedFdeBody, List.append_assoc]
  rw [take?_append (le4_length _)]
  simp only [Option.bind_eq_bind, Option.bind_some, leNat_le4,
    Nat.mod_eq_of_lt (show at_ + 4 - cieP < 2 ^ 32 by omega),
    show at_ + 4 - cieP ≠ 0 by omega, ite_false,
    show at_ + 4 - (at_ + 4 - cieP) = cieP by omega, hes, take4_cieZLPR, guard,
    show at_ + 4 - cieP ≤ at_ + 4 by omega, ite_true, decide_true]
  simp only [pure, Option.bind_some, show leNat [0, 0, 0, 0] = 0 by rfl, ite_true, parseCie_zLPR]
  simp only [← List.append_assoc]
  rw [parseFde_lsda (cie := ⟨true, cieInsns⟩) rfl (addr + at_ + 8)
      (relocBytes261_length addr symAddr (at_ + 8) 1 st)
      (relocBytes261_length addr symAddr (at_ + 17) gcc lo) sz hok]
  rfl

/-- **A `R_AARCH64_PREL32` relocation the linker resolved** (the placement assumption): its value
`S + A − P` fits in 32 bits (the linker rejects the link otherwise) and `S + A` is an address. -/
def Fits (secAddr : Nat) (symAddr : Nat → Nat) (r : Nat × Nat × Nat × Int) : Prop :=
  r.2.1 = 261 →
    -2 ^ 31 ≤ (symAddr r.2.2.1 : Int) + r.2.2.2 - ((secAddr + r.1 : Nat) : Int) ∧
    (symAddr r.2.2.1 : Int) + r.2.2.2 - ((secAddr + r.1 : Nat) : Int) < 2 ^ 31 ∧
    (symAddr r.2.2.1 : Int) + r.2.2.2 < 2 ^ 64

/-- A resolved `pcrel | sdata4` pointer of a relocation `(o, 261, s, a)` with `a ≥ 0` denotes
`S + A`. -/
theorem pcrel4_reloc {secAddr : Nat} {symAddr : Nat → Nat} {o s a : Nat}
    (h : Fits secAddr symAddr (o, 261, s, a)) :
    pcrel4 (secAddr + o) (relocBytes secAddr symAddr (o, 261, s, a)) = symAddr s + a := by
  obtain ⟨h1, h2, h3⟩ := h rfl
  rw [relocBytes_261]
  have e : (symAddr s : Int) + (a : Int) = ((symAddr s + a : Nat) : Int) := by push_cast; rfl
  rw [e] at h1 h2 h3 ⊢
  exact pcrel4_le4 (by omega) h1 h2

/-- The FDE the unwinder decodes for a function `x = (start, size, rows, lsda?)` of the section,
`.text` at `symAddr 1`, `.gcc_except_table` at `symAddr gcc`. -/
def decodedFde (symAddr : Nat → Nat) (gcc : Nat) (x : Nat × Nat × List (Nat × Cfi) × Option Nat) :
    Fde :=
  ⟨symAddr 1 + x.1, x.2.1 % 2 ^ 32, x.2.2.2.map (symAddr gcc + ·), insnsFrom 0 x.2.2.1, cieInsns⟩

/-- **The FDEs of the linked entries.** -/
theorem mapM_fdes (es : List (Nat × List UInt8)) (addr : Nat) (symAddr : Nat → Nat)
    (cieP gcc : Nat) (hz : es.lookup 0 = some (padded cieZRBody)) :
    ∀ (xs : List (Nat × Nat × List (Nat × Cfi) × Option Nat)) (at_ : Nat),
      (∀ x ∈ xs, RowsOk x.2.2.1) → cieP ≤ at_ →
      at_ + (fdeEntries cieP gcc at_ xs).1.length < 2 ^ 32 →
      (∀ r ∈ (fdeEntries cieP gcc at_ xs).2, Fits addr symAddr r) →
      (∀ x ∈ xs, x.2.2.2.isSome → ∃ v, es.lookup cieP = some (padded (cieZLPRBody (le 8 v).data.toList))) →
      (fdeEntryList addr symAddr cieP gcc at_ xs).mapM (fun p => fdeOf es addr p.1 p.2) =
        some (xs.map fun x => some (decodedFde symAddr gcc x))
  | [], _, _, _, _, _, _ => by simp [fdeEntryList]
  | x :: xs, at_, hok, hcp, hlen, hfit, hc => by
    have hx := padded_fde_length at_ cieP x
    simp only [fdeEntries, List.length_append, entryB_length] at hlen hfit
    have hfx : ∀ r ∈ fdeRelocs at_ gcc x, Fits addr symAddr r := fun r hr => hfit r (by simp [hr])
    simp only [fdeEntryList, List.mapM_cons, List.map_cons]
    have hat : at_ + 4 < 2 ^ 32 := by omega
    have hrest := mapM_fdes es addr symAddr cieP gcc hz xs
      (at_ + (entryB (fdeBodyB at_ cieP x)).data.toList.length)
      (fun y hy => hok y (List.mem_cons_of_mem _ hy)) (by omega)
      (by rw [entryB_length]; omega)
      (fun r hr => hfit r (by rw [entryB_length] at hr; simp [hr]))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    obtain ⟨st, sz, rows, _ | lo⟩ := x
    · have hP := pcrel4_reloc (o := at_ + 8) (s := 1) (a := st)
        (hfx (at_ + 8, 261, 1, st) (by simp [fdeRelocs]))
      rw [fdeOf_plain es addr symAddr at_ cieP gcc _ rfl (hok _ List.mem_cons_self) hat hz, hrest]
      simp only [Nat.add_assoc] at hP ⊢
      simp only [hP, decodedFde, Option.map_none, Option.bind_eq_bind, Option.bind_some, pure]
      try rfl
    · obtain ⟨v, hv⟩ := hc _ List.mem_cons_self rfl
      have hP := pcrel4_reloc (hfx (at_ + 8, 261, 1, st) (by simp [fdeRelocs]))
      have hL := pcrel4_reloc (hfx (at_ + 17, 261, gcc, lo) (by simp [fdeRelocs]))
      rw [fdeOf_lsda es addr symAddr at_ cieP gcc _ rfl (hok _ List.mem_cons_self) hat hcp hv, hrest]
      rw [show addr + at_ + 8 + 9 = addr + (at_ + 17) by omega]
      simp only [Nat.add_assoc] at hP hL ⊢
      simp only [hP, hL, decodedFde, Option.map_some, Option.bind_eq_bind, Option.bind_some, pure]
      try rfl

/-! ## The whole section -/

theorem cieZRB_toList : cieZRB.data.toList = (le 4 20).data.toList ++ padded cieZRBody := by
  decide +kernel

theorem cieZLPRB_toList :
    cieZLPRB.data.toList = (le 4 28).data.toList ++ padded (cieZLPRBody (le 8 0).data.toList) := by
  decide +kernel

theorem cieZRB_size : cieZRB.size = 24 := by decide +kernel

theorem cieZLPRB_size : cieZLPRB.size = 32 := by decide +kernel

theorem padded_cieZLPR (p q : List UInt8) (h : p.length = q.length) :
    padded (cieZLPRBody p) = cieZLPRBody p ++ List.replicate
      ((8 - (4 + (cieZLPRBody q).length) % 8) % 8) 0 := by
  simp [padded, cieZLPRBody, h]

/-- Resolving the personality pointer of the `zLPR` CIE. -/
theorem link_pers (v : Nat) (F : List UInt8) :
    writeAt (cieZRB.data.toList ++ cieZLPRB.data.toList ++ F) 44 (le 8 v).data.toList =
      cieZRB.data.toList ++ ((le 4 28).data.toList ++ padded (cieZLPRBody (le 8 v).data.toList)) ++
        F := by
  have h8 : ∀ n, (le 8 n).data.toList.length = 8 := fun n => by rw [le_bytes8]; rfl
  rw [cieZLPRB_toList, padded_cieZLPR (le 8 0).data.toList (le 8 0).data.toList rfl,
    padded_cieZLPR (le 8 v).data.toList (le 8 0).data.toList (by simp [h8])]
  have hA : (cieZRB.data.toList ++ ((le 4 28).data.toList ++ ((le 4 0).data.toList ++ [1] ++
      "zLPR".toUTF8.data.toList ++ [0] ++ (uleb 4).data.toList ++ (sleb (-8)).data.toList ++ [30] ++
      (uleb 11).data.toList ++ [0x1b, 0x9c]))).length = 44 := by
    decide +kernel
  have := writeAt_mid (cieZRB.data.toList ++ ((le 4 28).data.toList ++ ((le 4 0).data.toList ++ [1] ++
      "zLPR".toUTF8.data.toList ++ [0] ++ (uleb 4).data.toList ++ (sleb (-8)).data.toList ++ [30] ++
      (uleb 11).data.toList ++ [0x1b, 0x9c]))) (le 8 0).data.toList
    ([0x1b, 0x0c, 31, 0] ++ List.replicate ((8 - (4 + (cieZLPRBody (le 8 0).data.toList).length) % 8) % 8) 0
      ++ F) (le 8 v).data.toList (by simp [h8])
  rw [hA] at this
  simp only [cieZLPRBody, List.append_assoc] at this ⊢
  exact this

theorem linkedFdes_length_ge (secAddr : Nat) (symAddr : Nat → Nat) (cieP gcc : Nat) :
    ∀ (xs : List (Nat × Nat × List (Nat × Cfi) × Option Nat)) (at_ : Nat),
      xs.length ≤ (linkedFdes secAddr symAddr cieP gcc at_ xs).length
  | [], _ => by simp [linkedFdes]
  | x :: xs, at_ => by
    have := linkedFdes_length_ge secAddr symAddr cieP gcc xs
      (at_ + (entryB (fdeBodyB at_ cieP x)).data.toList.length)
    simp only [linkedFdes, linkedFde, List.length_append, le4_length, List.length_cons]
    omega

theorem padded_cieZR_length : (padded cieZRBody).length = 20 := by decide +kernel

theorem padded_cieZLPR_length (v : Nat) : (padded (cieZLPRBody (le 8 v).data.toList)).length = 28 := by
  simp only [padded, cieZLPRBody, le_bytes8, le4_0, zLPR_bytes, sleb_m8, uleb11, uleb4]
  simp

/-- The section bytes and relocations `ehFrame` writes, linked at `addr`, in entries. -/
theorem entries_none (fdes : List (Nat × Nat × List (Nat × Cfi) × Option Nat)) (gcc dwref addr : Nat)
    (symAddr : Nat → Nat) (hn : fdes.any (·.2.2.2.isSome) = false)
    (hb : ∀ x ∈ fdes, (cfiProgram x.2.2.1).data.toList.length + 24 < 0xffffffff) :
    entries (linkSection (ehFrame fdes gcc dwref).1.data.toList (ehFrame fdes gcc dwref).2 addr symAddr) =
      some ((0, padded cieZRBody) :: fdeEntryList addr symAddr 0 gcc 24 fdes) := by
  rw [ehFrame_eq, hn]
  simp only [Bool.false_eq_true, ite_false]
  obtain ⟨h1, h2⟩ := foldl_ehStep 0 gcc fdes (cieZRB, #[])
  rw [h1, h2, cieZRB_size]
  simp only [Array.toList_empty, List.nil_append]
  have hl := link_fdes addr symAddr 0 gcc fdes cieZRB.data.toList
  rw [← size_toList, cieZRB_size] at hl
  rw [hl, cieZRB_toList, entries]
  have hlen := linkedFdes_length_ge addr symAddr 0 gcc fdes 24
  rw [show ((le 4 20).data.toList ++ padded cieZRBody ++ linkedFdes addr symAddr 0 gcc 24 fdes).length =
      (23 + (linkedFdes addr symAddr 0 gcc 24 fdes).length) + 1 by
    simp only [List.length_append, le4_length, padded_cieZR_length]; omega]
  rw [entriesN_entry _ 0 20 _ _ padded_cieZR_length (by decide) (by decide),
    entriesN_fdes addr symAddr 0 gcc fdes 24 _ (by omega) hb]
  rfl

theorem entriesN_mono' : ∀ {n off : Nat} {bs : List UInt8} {es : List (Nat × List UInt8)} (d : Nat),
    entriesN n off bs = some es → entriesN (n + d) off bs = some es
  | n, off, [], es, d, h => by cases n <;> cases d <;> simp_all [entriesN]
  | 0, _, _ :: _, _, _, h => by simp [entriesN] at h
  | n + 1, off, b :: bs, es, d, h => by
    rw [show n + 1 + d = (n + d) + 1 by omega]
    rw [entriesN.eq_3] at h ⊢
    cases ht : take? 4 (b :: bs) with
    | none => simp [ht] at h
    | some p =>
      obtain ⟨lf, r⟩ := p
      simp only [ht, Option.bind_eq_bind, Option.bind_some] at h ⊢
      split at h
      · rw [if_pos (by assumption)]; exact h
      · rw [if_neg (by assumption)]
        split at h
        · cases h
        · rw [if_neg (by assumption)]
          cases hb : take? (leNat lf) r with
          | none => simp [hb] at h
          | some q =>
            obtain ⟨body, r'⟩ := q
            simp only [hb, Option.bind_some] at h ⊢
            cases he : entriesN n (off + 4 + leNat lf) r' with
            | none => simp [he] at h
            | some es' =>
              simp only [he, Option.bind_some] at h
              rw [entriesN_mono' d he]
              exact h

/-- The same with LSDAs: the two CIEs, the personality pointer resolved. -/
theorem entries_lsda (fdes : List (Nat × Nat × List (Nat × Cfi) × Option Nat)) (gcc dwref addr : Nat)
    (symAddr : Nat → Nat) (hn : fdes.any (·.2.2.2.isSome) = true)
    (hb : ∀ x ∈ fdes, (cfiProgram x.2.2.1).data.toList.length + 24 < 0xffffffff) :
    ∃ v, entries (linkSection (ehFrame fdes gcc dwref).1.data.toList (ehFrame fdes gcc dwref).2
        addr symAddr) =
      some ((0, padded cieZRBody) :: (24, padded (cieZLPRBody (le 8 v).data.toList)) ::
        fdeEntryList addr symAddr 24 gcc 56 fdes) := by
  rw [ehFrame_eq, hn]
  simp only [ite_true]
  obtain ⟨h1, h2⟩ := foldl_ehStep cieZRB.size gcc fdes
    (cieZRB ++ cieZLPRB, #[(cieZRB.size + 14 + 6, 260, dwref, 0)])
  rw [h1, h2, cieZRB_size]
  simp only [ByteArray.size_append, cieZRB_size, cieZLPRB_size, ByteArray.toList_data_append]
  simp only [show (24 + 14 + 6 : Nat) = 44 from rfl, show (24 + 32 : Nat) = 56 from rfl]
  rw [linkSection_append]
  simp only [linkSection, List.toList_toArray, List.foldl_cons, List.foldl_nil]
  rw [relocBytes_260, link_pers]
  refine ⟨(((symAddr dwref : Int) + 0 - ((addr + 44 : Nat) : Int)) % 2 ^ 64).toNat, ?_⟩
  have hl := link_fdes addr symAddr 24 gcc fdes
    (cieZRB.data.toList ++ ((le 4 28).data.toList ++ padded (cieZLPRBody
      (le 8 ((((symAddr dwref : Int) + 0 - ((addr + 44 : Nat) : Int)) % 2 ^ 64).toNat)).data.toList)))
  have hP : (cieZRB.data.toList ++ ((le 4 28).data.toList ++ padded (cieZLPRBody
      (le 8 ((((symAddr dwref : Int) + 0 - ((addr + 44 : Nat) : Int)) % 2 ^ 64).toNat)).data.toList))).length
      = 56 := by
    simp only [List.length_append, ← size_toList, cieZRB_size, le4_length, le4_size,
      padded_cieZLPR_length]
  rw [hP] at hl
  simp only [linkSection] at hl
  rw [hl, cieZRB_toList, entries]
  have hlen := linkedFdes_length_ge addr symAddr 24 gcc fdes 56
  have key : entriesN (fdes.length + 1 + 1) 0 ((le 4 20).data.toList ++ padded cieZRBody ++
      ((le 4 28).data.toList ++ padded (cieZLPRBody (le 8 ((((symAddr dwref : Int) + 0 -
        ((addr + 44 : Nat) : Int)) % 2 ^ 64).toNat)).data.toList) ++
      linkedFdes addr symAddr 24 gcc 56 fdes)) =
      some ((0, padded cieZRBody) :: (24, padded (cieZLPRBody (le 8 ((((symAddr dwref : Int) + 0 -
        ((addr + 44 : Nat) : Int)) % 2 ^ 64).toNat)).data.toList)) ::
        fdeEntryList addr symAddr 24 gcc 56 fdes) := by
    rw [entriesN_entry _ 0 20 _ _ padded_cieZR_length (by decide) (by decide),
      entriesN_entry _ _ 28 _ _ (padded_cieZLPR_length _) (by decide) (by decide),
      entriesN_fdes addr symAddr 24 gcc fdes _ _ (by omega) hb]
    rfl
  have hl2 : fdes.length + 1 + 1 ≤ ((le 4 20).data.toList ++ padded cieZRBody ++
      ((le 4 28).data.toList ++ padded (cieZLPRBody (le 8 ((((symAddr dwref : Int) + 0 -
        ((addr + 44 : Nat) : Int)) % 2 ^ 64).toNat)).data.toList)) ++
      linkedFdes addr symAddr 24 gcc 56 fdes).length := by
    simp only [List.length_append, le4_length, padded_cieZR_length, padded_cieZLPR_length]; omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hl2
  simp only [List.append_assoc] at key hd ⊢
  rw [hd, entriesN_mono' d key]

/-- The relocations and the size of the section `ehFrame` writes. -/
theorem ehFrame_parts (fdes : List (Nat × Nat × List (Nat × Cfi) × Option Nat)) (gcc dwref : Nat) :
    let cieP := if fdes.any (·.2.2.2.isSome) then 24 else 0
    let at0 := if fdes.any (·.2.2.2.isSome) then 56 else 24
    (ehFrame fdes gcc dwref).1.size = at0 + (fdeEntries cieP gcc at0 fdes).1.length ∧
      ∀ r ∈ (fdeEntries cieP gcc at0 fdes).2, r ∈ (ehFrame fdes gcc dwref).2 := by
  intro cieP at0
  rw [ehFrame_eq]
  by_cases hn : fdes.any (·.2.2.2.isSome) = true
  · simp only [cieP, at0, hn, ite_true]
    obtain ⟨h1, h2⟩ := foldl_ehStep cieZRB.size gcc fdes
      (cieZRB ++ cieZLPRB, #[(cieZRB.size + 14 + 6, 260, dwref, 0)])
    simp only [ByteArray.size_append, cieZRB_size, cieZLPRB_size] at h1 h2 ⊢
    refine ⟨?_, fun r hr => ?_⟩
    · rw [size_toList, h1, ByteArray.toList_data_append, List.length_append, List.length_append,
        ← size_toList, ← size_toList, cieZRB_size, cieZLPRB_size]
    · rw [h2]; simp [hr]
  · simp only [Bool.not_eq_true] at hn
    simp only [cieP, at0, hn, Bool.false_eq_true, ite_false]
    obtain ⟨h1, h2⟩ := foldl_ehStep 0 gcc fdes (cieZRB, #[])
    simp only [cieZRB_size] at h1 h2 ⊢
    refine ⟨?_, fun r hr => ?_⟩
    · rw [size_toList, h1, List.length_append, ← size_toList, cieZRB_size]
    · rw [h2]; simp [hr]

theorem fdeOf_cieZR (es : List (Nat × List UInt8)) (addr : Nat) :
    fdeOf es addr 0 (padded cieZRBody) = some none := by
  simp [fdeOf, take4_cieZR, show leNat [0, 0, 0, 0] = 0 by rfl, pure]

theorem fdeOf_cieZLPR (es : List (Nat × List UInt8)) (addr off : Nat) (pers : List UInt8) :
    fdeOf es addr off (padded (cieZLPRBody pers)) = some none := by
  simp [fdeOf, take4_cieZLPR, show leNat [0, 0, 0, 0] = 0 by rfl, pure]

theorem reduceOption_map_some {α β : Type} (f : α → β) :
    ∀ xs : List α, (xs.map fun x => some (f x)).reduceOption = xs.map f
  | [] => rfl
  | x :: xs => by simp [List.reduceOption, reduceOption_map_some f xs]

/-- **The FDEs of the linked `.eh_frame`.** `ehFrame fdes` placed at `addr`, its relocations
resolved against the symbol addresses `symAddr` (`.text` = symbol 1, `.gcc_except_table` = `gcc`)
as the linker resolves them (`Fits`), decodes to one FDE per function, with `pc_begin` the
function's address, the LSDA pointer its LSDA's address, and the CFA program its rows'. -/
theorem ehFdes_ehFrame (fdes : List (Nat × Nat × List (Nat × Cfi) × Option Nat)) (gcc dwref addr : Nat)
    (symAddr : Nat → Nat) (hok : ∀ x ∈ fdes, RowsOk x.2.2.1)
    (hb : ∀ x ∈ fdes, (cfiProgram x.2.2.1).data.toList.length + 24 < 0xffffffff)
    (hsz : (ehFrame fdes gcc dwref).1.size < 2 ^ 32)
    (hfit : ∀ r ∈ (ehFrame fdes gcc dwref).2, Fits addr symAddr r) :
    ehFdes (linkSection (ehFrame fdes gcc dwref).1.data.toList (ehFrame fdes gcc dwref).2 addr symAddr)
        addr = some (fdes.map (decodedFde symAddr gcc)) := by
  obtain ⟨hs, hr⟩ := ehFrame_parts fdes gcc dwref
  by_cases hn : fdes.any (·.2.2.2.isSome) = true
  · simp only [hn, ite_true] at hs hr
    obtain ⟨v, he⟩ := entries_lsda fdes gcc dwref addr symAddr hn hb
    simp only [ehFdes, he, Option.bind_eq_bind, Option.bind_some]
    have hm := mapM_fdes ((0, padded cieZRBody) :: (24, padded (cieZLPRBody (le 8 v).data.toList)) ::
        fdeEntryList addr symAddr 24 gcc 56 fdes) addr symAddr 24 gcc (by simp [List.lookup])
      fdes 56 hok (by omega) (by omega) (fun r h => hfit r (hr r h))
      (fun _ _ _ => ⟨v, by simp [List.lookup]⟩)
    simp only [List.mapM_cons, fdeOf_cieZR, fdeOf_cieZLPR, hm, Option.bind_eq_bind, Option.bind_some,
      pure]
    simp [List.reduceOption, reduceOption_map_some]
  · simp only [Bool.not_eq_true] at hn
    simp only [hn, Bool.false_eq_true, ite_false] at hs hr
    have he := entries_none fdes gcc dwref addr symAddr hn hb
    simp only [ehFdes, he, Option.bind_eq_bind, Option.bind_some]
    have hm := mapM_fdes ((0, padded cieZRBody) :: fdeEntryList addr symAddr 0 gcc 24 fdes) addr
      symAddr 0 gcc (by simp [List.lookup]) fdes 24 hok (by omega) (by omega)
      (fun r h => hfit r (hr r h))
      (fun x hx hs => by
        have := List.any_eq_false.mp hn x hx
        simp_all)
    simp only [List.mapM_cons, fdeOf_cieZR, hm, Option.bind_eq_bind, Option.bind_some,
      pure]
    simp [List.reduceOption, reduceOption_map_some]

/-! ## The lookup: the tables of the function covering a pc -/

/-- An LSDA decodes the same followed by anything (the next function's LSDA). -/
theorem decodeLsda?_append {bs : List UInt8} {es : List CallSiteEntry} (rest : List UInt8)
    (h : decodeLsda? bs = some es) : decodeLsda? (bs ++ rest) = some es := by
  obtain ⟨bs', rfl⟩ : ∃ bs', bs = 0xff :: 0x03 :: bs' := by
    unfold decodeLsda? at h
    split at h
    · exact ⟨_, rfl⟩
    · cases h
  · simp only [decodeLsda?, List.cons_append, Option.bind_eq_bind] at h ⊢
    cases hu : uleb? bs' with
    | none => simp [hu] at h
    | some p =>
      obtain ⟨n, r⟩ := p
      rw [uleb?_append hu]
      simp only [hu, Option.bind_some] at h ⊢
      split at h
      · rename_i r'
        simp only [List.cons_append]
        cases hl : uleb? r' with
        | none => simp [hl] at h
        | some q =>
          obtain ⟨len, r''⟩ := q
          rw [uleb?_append hl]
          simp only [hl, Option.bind_some] at h ⊢
          split at h
          · rw [if_pos (by simp only [List.length_append]; omega),
              List.take_append_of_le_length (by assumption)]
            exact h
          · cases h
      · cases h

/-- **The tables of the function covering `pc`.** The functions `fdes = pre ++ x :: post` of the
section `ehFrame fdes gcc dwref` (placed at `addr`, relocated: `Fits`), `pc` in `x`'s range and
in none of `pre`'s: the unwinder finds `x`'s address, the CIE's instructions, `x`'s rows'
instructions and, if `x` has an LSDA at offset `lo` of `.gcc_except_table` (`gccB`, placed at
`symAddr gcc`), the call-site table of the `lsdaBytes sites` written there. -/
theorem tablesAt_ehFrame (fdes : List (Nat × Nat × List (Nat × Cfi) × Option Nat))
    (gcc dwref addr : Nat) (symAddr : Nat → Nat) (hok : ∀ x ∈ fdes, RowsOk x.2.2.1)
    (hb : ∀ x ∈ fdes, (cfiProgram x.2.2.1).data.toList.length + 24 < 0xffffffff)
    (hsz : (ehFrame fdes gcc dwref).1.size < 2 ^ 32)
    (hfit : ∀ r ∈ (ehFrame fdes gcc dwref).2, Fits addr symAddr r)
    {pre post : List (Nat × Nat × List (Nat × Cfi) × Option Nat)}
    {x : Nat × Nat × List (Nat × Cfi) × Option Nat} (hfd : fdes = pre ++ x :: post) {pc : Nat}
    (hpc : symAddr 1 + x.1 ≤ pc ∧ pc < symAddr 1 + x.1 + x.2.1 % 2 ^ 32)
    (hpre : ∀ y ∈ pre, ¬ (symAddr 1 + y.1 ≤ pc ∧ pc < symAddr 1 + y.1 + y.2.1 % 2 ^ 32))
    (gccB : List UInt8) {L : Option (List CallSite)} (hL : x.2.2.2.isSome = L.isSome)
    (hG : ∀ lo sites, x.2.2.2 = some lo → L = some sites →
      ∃ rest, gccB.drop lo = (lsdaBytes sites).data.toList ++ rest) :
    tablesAt (linkSection (ehFrame fdes gcc dwref).1.data.toList (ehFrame fdes gcc dwref).2 addr
        symAddr) addr gccB (symAddr gcc) pc =
      some (symAddr 1 + x.1, ⟨cieInsns, insnsFrom 0 x.2.2.1, L.map (List.map (·.entry))⟩) := by
  have hfind : (fdes.map (decodedFde symAddr gcc)).find?
      (fun f => decide (f.pcBegin ≤ pc ∧ pc < f.pcBegin + f.pcRange)) = some (decodedFde symAddr gcc x) := by
    subst hfd
    rw [List.map_append, List.find?_append, List.find?_eq_none.mpr (fun f hf => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hf
      have := hpre y hy
      exact fun h => this (of_decide_eq_true h))]
    simp [decodedFde, hpc]
  simp only [tablesAt, ehFdes_ehFrame fdes gcc dwref addr symAddr hok hb hsz hfit, hfind,
    Option.bind_eq_bind, Option.bind_some]
  obtain ⟨st, sz, rows, _ | lo⟩ := x <;> rcases L with _ | sites
  · simp [decodedFde, pure]
  · simp at hL
  · simp at hL
  · obtain ⟨rest, hr⟩ := hG lo sites rfl rfl
    simp [decodedFde, pure, hr, decodeLsda?_append rest (decodeLsda?_lsdaBytes sites)]

/-! ## Witness: S10c's function (`UnwindTables.Witness`), linked -/

namespace EhWitness

/-- `.text` at `0x400000`, `.gcc_except_table` (symbol 2) at `0x500000`, `DW.ref` (3) at
`0x600000`; `.eh_frame` at `0x480000`. The function `Witness.af` at offset 0 of `.text`, 40
bytes, its LSDA at offset 0 of `.gcc_except_table`. -/
def symAddr (i : Nat) : Nat := if i = 1 then 0x400000 else if i = 2 then 0x500000 else 0x600000
def fdes : List (Nat × Nat × List (Nat × Cfi) × Option Nat) := [(0, 40, Witness.rows, some 0)]
def gccB : List UInt8 := (lsdaBytes Witness.sites).data.toList

theorem fits : ∀ r ∈ (ehFrame fdes 2 3).2, Fits 0x480000 symAddr r := by
  simp only [Fits]; decide +kernel

/-- At a pc of the function (`0x400010`), the unwinder reads its tables from the linked
sections: the address `0x400000`, the CIE's and the rows' instructions, the call-site table. -/
theorem tables :
    tablesAt (linkSection (ehFrame fdes 2 3).1.data.toList (ehFrame fdes 2 3).2 0x480000 symAddr)
        0x480000 gccB 0x500000 0x400010 =
      some (0x400000, ⟨cieInsns, insnsFrom 0 Witness.rows, some (Witness.sites.map (·.entry))⟩) :=
  tablesAt_ehFrame fdes 2 3 0x480000 symAddr
    (by simp only [fdes, List.mem_singleton, forall_eq]
        exact (unwindRows_frame Witness.rows_ok rfl).1)
    (by decide +kernel) (by decide +kernel) fits (pre := []) (post := []) rfl
    (by decide +kernel) (by simp) gccB (L := some Witness.sites) rfl
    (fun lo sites h1 h2 => by cases h1; cases h2; exact ⟨[], by simp [gccB]⟩)

end EhWitness

end Backend.Proof.EhFrameDecode
