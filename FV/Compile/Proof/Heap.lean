import FV.Compile.Proof.Bytes
import FV.Compile.Proof.Rel

/-!
# Map objects in memory (`Compile.mapEnv`'s representation)

`MemModels m H`: the memory `m` is well formed and holds, for each object `h ↦ (d, es)` of
the abstract heap `H`, a header allocation `[h, h+16)` with the length and the entry-array
address `d`, and the entry array `[d, d + 16·|es|)`. Pieces of different objects are
different allocations.

Main results: `MemModels.readEntries`, `MemModels.writeEntries` (in-place update of one
object), `MemModels.newMapObj` (a fresh object), and preservation under allocation,
stores into other allocations and `free` of other allocations.
-/

set_option autoImplicit false

namespace Compile.Proof

open Compile Clif

/-- The eight bytes at `a` hold `x` (little endian). -/
def WordAt (m : Mem) (a : Nat) (x : Word) : Prop :=
  ∀ i, i < 8 → m.bytes (a + i) = some (BitVec.ofNat 8 (x.toNat / 2 ^ (8 * i)))

theorem WordAt.keeps {m m' : Mem} {a : Nat} {x : Word} {al : Alloc} (hw : WordAt m a x)
    (hal : al ∈ m.allocs) (hin : al.base ≤ a ∧ a + 8 ≤ al.base + al.size) (hk : Keeps m m' al) :
    WordAt m' a x := fun i hi => by rw [(hk hal).2 _ (by omega) (by omega)]; exact hw i hi

theorem readWord_of_wordAt {m : Mem} {a : Nat} {x : Word} {al : Alloc} (hw : WordAt m a x)
    (hal : al ∈ m.allocs) (hin : al.base ≤ a ∧ a + 8 ≤ al.base + al.size) :
    readWord m a = .ok x := by
  unfold readWord
  rw [load_eq hal hin (by simp)]
  have := readBits_of_bytes (m := m) (addr := a) (n := 8) x.toNat x.isLt hw
  simpa using this

theorem writeWord_eq {m : Mem} {a : Nat} (x : Word) {al : Alloc} (hal : al ∈ m.allocs)
    (hin : al.base ≤ a ∧ a + 8 ≤ al.base + al.size) :
    writeWord m a x = .ok (m.writeBits false a 8 x) := by
  unfold writeWord
  rw [store_eq x hal hin (by simp)]; rfl

theorem wordAt_writeBits (m : Mem) (a : Nat) (x : Word) : WordAt (m.writeBits false a 8 x) a x :=
  fun i hi => by rw [writeBits_in x hi, extract_byte]

theorem WordAt.writeBits {m : Mem} {a b : Nat} {x y : Word} (hw : WordAt m a x)
    (h : a + 8 ≤ b ∨ b + 8 ≤ a) : WordAt (m.writeBits false b 8 y) a x := fun i hi => by
  rw [writeBits_out y (by omega)]; exact hw i hi

/-! ## Objects -/

/-- The object `h ↦ (d, es)` is represented in `m`. -/
structure ObjAt (m : Mem) (h d : Nat) (es : List (Word × Word)) : Prop where
  hdr : (⟨h, 16⟩ : Alloc) ∈ m.allocs
  arr : (⟨d, 16 * es.length⟩ : Alloc) ∈ m.allocs
  len : es.length ≤ maxEntries
  wlen : WordAt m h (BitVec.ofNat 64 es.length)
  wdata : WordAt m (h + 8) (BitVec.ofNat 64 d)
  went : ∀ i (hi : i < es.length), WordAt m (d + 16 * i) es[i].1 ∧ WordAt m (d + 16 * i + 8) es[i].2

theorem ObjAt.keeps {m m' : Mem} {h d : Nat} {es : List (Word × Word)} (ho : ObjAt m h d es)
    (k₁ : Keeps m m' ⟨h, 16⟩) (k₂ : Keeps m m' ⟨d, 16 * es.length⟩) : ObjAt m' h d es where
  hdr := (k₁ ho.hdr).1
  arr := (k₂ ho.arr).1
  len := ho.len
  wlen := ho.wlen.keeps ho.hdr (by simp) k₁
  wdata := ho.wdata.keeps ho.hdr (by simp) k₁
  went i hi := ⟨(ho.went i hi).1.keeps ho.arr (by simp; omega) k₂,
    (ho.went i hi).2.keeps ho.arr (by simp; omega) k₂⟩

/-- `b` is not the base of any piece of any object. -/
def ObjFree (H : Heap) (b : Nat) : Prop := ∀ h d es, H h = some (d, es) → b ≠ h ∧ b ≠ d

structure MemModels (m : Mem) (H : Heap) : Prop where
  wf : MemWF m
  obj : ∀ h d es, H h = some (d, es) → ObjAt m h d es
  sep : ∀ h d es h' d' es', H h = some (d, es) → H h' = some (d', es') →
    d ≠ h' ∧ (h ≠ h' → d ≠ d')

def Heap.set (H : Heap) (h : Nat) (p : Nat × List (Word × Word)) : Heap :=
  fun x => if x = h then some p else H x

@[simp] theorem Heap.set_same (H : Heap) (h : Nat) (p : Nat × List (Word × Word)) :
    H.set h p h = some p := by simp [Heap.set]

theorem Heap.set_other (H : Heap) {h x : Nat} (p : Nat × List (Word × Word)) (hx : x ≠ h) :
    H.set h p x = H x := by simp [Heap.set, hx]

theorem maxEntries_lt : maxEntries < 2 ^ 64 := by decide

theorem MemModels.readEntries {m : Mem} {H : Heap} (hm : MemModels m H) {h d : Nat}
    {es : List (Word × Word)} (hH : H h = some (d, es)) : readEntries m h = .ok es := by
  have ho := hm.obj h d es hH
  have hdlt : d < 2 ^ 64 := by
    have := hm.wf.below _ ho.arr; have := hm.wf.fits; simp at *; omega
  have hlen : es.length < 2 ^ 64 := Nat.lt_of_le_of_lt ho.len maxEntries_lt
  unfold Compile.readEntries
  rw [readWord_of_wordAt ho.wlen ho.hdr (by simp), readWord_of_wordAt ho.wdata ho.hdr (by simp)]
  simp only [Res.ok_bind, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen, Nat.mod_eq_of_lt hdlt,
    decide_eq_true ho.len, Res.check_true]
  suffices H : ∀ n, n ≤ es.length → (List.range n).mapM (fun i => do
      let k ← readWord m (d + 16 * i)
      let v ← readWord m (d + 16 * i + 8)
      pure (k, v)) = Res.ok (es.take n) by
    rw [H _ (Nat.le_refl _), List.take_length]
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.mapM_append, ih (by omega)]
    have hw := ho.went n (by omega)
    simp only [List.mapM_cons, List.mapM_nil,
      readWord_of_wordAt hw.1 ho.arr (by simp; omega),
      readWord_of_wordAt hw.2 ho.arr (by simp; omega), Res.ok_bind, Res.pure_eq]
    rw [List.take_succ_eq_append_getElem (by omega)]

/-- Preservation under a memory change that keeps every object piece. -/
theorem MemModels.keeps {m m' : Mem} {H : Heap} (hm : MemModels m H) (hwf : MemWF m')
    (hk : ∀ h d es, H h = some (d, es) → Keeps m m' ⟨h, 16⟩ ∧ Keeps m m' ⟨d, 16 * es.length⟩) :
    MemModels m' H :=
  ⟨hwf, fun h d es hH => (hm.obj h d es hH).keeps (hk h d es hH).1 (hk h d es hH).2, hm.sep⟩

/-- A write inside an allocation that is not an object piece. -/
theorem MemModels.writeBits {m : Mem} {H : Heap} (hm : MemModels m H) {big : Bool}
    {addr n w : Nat} (x : BitVec w) {al : Alloc} (hal : al ∈ m.allocs)
    (hin : al.base ≤ addr ∧ addr + n ≤ al.base + al.size) (hfree : ObjFree H al.base) :
    MemModels (m.writeBits big addr n x) H :=
  hm.keeps (hm.wf.writeBits x) fun h d es hH =>
    ⟨Keeps.writeBits hm.wf x hal hin (Ne.symm (hfree h d es hH).1),
     Keeps.writeBits hm.wf x hal hin (Ne.symm (hfree h d es hH).2)⟩

theorem MemModels.alloc {m : Mem} {H : Heap} (hm : MemModels m H) {size align : Nat}
    (h16 : align ≤ 16) (hf : (m.alloc size align).2.fits = true) :
    MemModels (m.alloc size align).2 H ∧ ObjFree H (m.alloc size align).1 := by
  obtain ⟨hwf, hge, -, -, -, -, -⟩ := hm.wf.alloc h16 hf
  refine ⟨hm.keeps hwf fun h d es _ => ⟨Keeps.alloc m size align h16 _,
    Keeps.alloc m size align h16 _⟩, fun h d es hH => ?_⟩
  have ho := hm.obj h d es hH
  have := hm.wf.below _ ho.hdr; have := hm.wf.below _ ho.arr
  simp at *; omega

theorem MemModels.free {m : Mem} {H : Heap} (hm : MemModels m H) (bases : List Nat)
    (hfree : ∀ b ∈ bases, ObjFree H b) : MemModels (m.free bases) H :=
  hm.keeps (hm.wf.free bases) fun h d es hH =>
    ⟨Keeps.free bases fun hb => (hfree _ hb h d es hH).1 rfl,
     Keeps.free bases fun hb => (hfree _ hb h d es hH).2 rfl⟩

/-- An object's pieces lie below `next`. -/
theorem MemModels.pieces_lt {m : Mem} {H : Heap} (hm : MemModels m H) {h d : Nat}
    {es : List (Word × Word)} (hH : H h = some (d, es)) : h < m.next ∧ d < m.next := by
  have ho := hm.obj h d es hH
  have := hm.wf.below _ ho.hdr; have := hm.wf.below _ ho.arr
  simp at *; omega

theorem ObjFree.of_lt {m : Mem} {H : Heap} (hm : MemModels m H) {b : Nat} (hb : m.next ≤ b) :
    ObjFree H b := fun h d es hH => by
  have := hm.pieces_lt hH; omega

/-! ## Writing an entry array -/

/-- One step of `writeEntries`' loop. -/
def entryW (data : Nat) (m : Mem) (p : (Word × Word) × Nat) : Res Mem := do
  let m ← writeWord m (data + 16 * p.2) p.1.1
  writeWord m (data + 16 * p.2 + 8) p.1.2

theorem entries_fold {data cnt : Nat} : ∀ (l : List ((Word × Word) × Nat)) (m : Mem),
    (l.map (·.2)).Nodup → (∀ p ∈ l, p.2 < cnt) → (⟨data, 16 * cnt⟩ : Alloc) ∈ m.allocs →
    ∃ m', l.foldlM (entryW data) m = .ok m' ∧ m'.allocs = m.allocs ∧ m'.next = m.next ∧
      (∀ a, (∀ p ∈ l, a < data + 16 * p.2 ∨ data + 16 * p.2 + 16 ≤ a) → m'.bytes a = m.bytes a) ∧
      ∀ p ∈ l, WordAt m' (data + 16 * p.2) p.1.1 ∧ WordAt m' (data + 16 * p.2 + 8) p.1.2
  | [], m, _, _, _ => ⟨m, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => by simp at h⟩
  | p :: l, m, hnd, hlt, hal => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hp := hlt p List.mem_cons_self
    let m₁ := (m.writeBits false (data + 16 * p.2) 8 p.1.1).writeBits false
      (data + 16 * p.2 + 8) 8 p.1.2
    have e₁ : entryW data m p = .ok m₁ := by
      simp only [entryW]
      rw [writeWord_eq _ hal (by simp; omega), Res.ok_bind,
        writeWord_eq (m := m.writeBits false (data + 16 * p.2) 8 p.1.1) _ hal (by simp; omega)]
    obtain ⟨m', hf, ha, hn, hb, hw⟩ := entries_fold l m₁ hnd.2
      (fun q hq => hlt q (List.mem_cons_of_mem _ hq)) hal
    refine ⟨m', by rw [List.foldlM_cons, e₁]; exact hf, ha, hn, fun a ha' => ?_, ?_⟩
    · rw [hb a (fun q hq => ha' q (List.mem_cons_of_mem _ hq))]
      have := ha' p List.mem_cons_self
      simp only [m₁]
      rw [writeBits_out _ (by omega), writeBits_out _ (by omega)]
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · have hd : ∀ r ∈ l, r.2 ≠ q.2 := fun r hr he => hnd.1 (he ▸ List.mem_map_of_mem hr)
        have hdis : ∀ a, data + 16 * q.2 ≤ a → a < data + 16 * q.2 + 16 →
            ∀ r ∈ l, a < data + 16 * r.2 ∨ data + 16 * r.2 + 16 ≤ a := by
          intro a h1 h2 r hr
          have := hd r hr
          rcases Nat.lt_or_gt_of_ne this with h | h <;> omega
        constructor
        · intro i hi
          rw [hb _ (hdis _ (by omega) (by omega))]
          simp only [m₁]
          rw [writeBits_out _ (by omega)]
          exact wordAt_writeBits m _ _ i hi
        · intro i hi
          rw [hb _ (hdis _ (by omega) (by omega))]
          exact wordAt_writeBits _ _ _ i hi
      · exact hw q hq

theorem zip_range_mem {α : Type} {l : List α} {p : α × Nat} (h : p ∈ l.zip (List.range l.length)) :
    p.2 < l.length ∧ ∃ hi : p.2 < l.length, p.1 = l[p.2] := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem h
  simp only [List.length_zip, List.length_range, Nat.min_self] at hi
  simp only [List.getElem_zip, List.getElem_range] at he
  subst he
  exact ⟨hi, hi, rfl⟩

theorem zip_range_nodup {α : Type} (l : List α) :
    ((l.zip (List.range l.length)).map (·.2)).Nodup := by
  rw [List.map_snd_zip (by simp)]; exact List.nodup_range

theorem mem_zip_range {α : Type} (l : List α) (i : Nat) (hi : i < l.length) :
    (l[i], i) ∈ l.zip (List.range l.length) := by
  apply List.mem_iff_getElem.2
  exact ⟨i, by simp [hi], by simp⟩

/-- `writeEntries` on a header allocation `h` that is no other object's piece. -/
theorem writeEntries_spec {m : Mem} {H : Heap} (hm : MemModels m H) {h : Nat}
    (es : List (Word × Word)) (hh : (⟨h, 16⟩ : Alloc) ∈ m.allocs)
    (hsep : ∀ h' d' es', H h' = some (d', es') → h' ≠ h → d' ≠ h) :
    writeEntries m h es = .trap oomTrap ∨
    ∃ m' d, writeEntries m h es = .ok m' ∧ m.next ≤ d ∧ m.next ≤ m'.next ∧
      MemModels m' (H.set h (d, es)) ∧ (∀ al ∈ m.allocs, al.base ≠ h → Keeps m m' al) := by
  unfold writeEntries
  by_cases hlen' : ¬ es.length ≤ maxEntries
  · left; simp [hlen']
  have hlen : es.length ≤ maxEntries := Classical.not_not.1 hlen'
  simp only [decide_eq_true hlen, Res.trapUnless_true, Res.ok_bind]
  by_cases hfit' : ¬ (m.alloc (16 * es.length) 16).2.fits = true
  · left; simp at hfit'; simp [Nat.not_le.2 hfit']
  have hfit : (m.alloc (16 * es.length) 16).2.fits = true := Classical.not_not.1 hfit'
  right
  simp only [hfit, Res.trapUnless_true, Res.ok_bind]
  obtain ⟨hwf₁, hge, hal16, hlt64, hmem, hallocs, hbytes⟩ := hm.wf.alloc (Nat.le_refl 16) hfit
  generalize hdata : (m.alloc (16 * es.length) 16).1 = data at *
  generalize hm₁ : (m.alloc (16 * es.length) 16).2 = m₁ at *
  obtain ⟨m₂, hf, ha₂, hn₂, hb₂, hw₂⟩ := entries_fold (data := data) (cnt := es.length)
    (es.zip (List.range es.length)) m₁ (zip_range_nodup es)
    (fun p hp => (zip_range_mem hp).1) hmem
  have hf' : (es.zip (List.range es.length)).foldlM (init := m₁) (fun m ((k, v), i) => do
      let m ← writeWord m (data + 16 * i) k
      writeWord m (data + 16 * i + 8) v) = .ok m₂ := hf
  rw [hf', Res.ok_bind]
  have hh₁ : (⟨h, 16⟩ : Alloc) ∈ m₂.allocs := by rw [ha₂, hallocs]; exact List.mem_cons_of_mem _ hh
  let m₃ := m₂.writeBits false h 8 (BitVec.ofNat 64 es.length)
  have hh₃ : (⟨h, 16⟩ : Alloc) ∈ m₃.allocs := hh₁
  rw [writeWord_eq _ hh₁ (by simp), Res.ok_bind, writeWord_eq _ hh₃ (by simp)]
  let m₄ := m₃.writeBits false (h + 8) 8 (BitVec.ofNat 64 data)
  have hwf₂ : MemWF m₂ := ⟨by rw [hn₂]; exact hwf₁.fits, by rw [ha₂, hn₂]; exact hwf₁.below,
    by rw [ha₂]; exact hwf₁.sorted⟩
  have hwf₄ : MemWF m₄ := (hwf₂.writeBits _).writeBits _
  have hhlt : h + 16 ≤ data := by have := hm.wf.below _ hh; simp at this; omega
  -- bytes of m₄ outside the header and the new array are those of `m`
  have hout : ∀ a, (a < h ∨ h + 16 ≤ a) → (a < data ∨ data + 16 * es.length ≤ a) →
      m₄.bytes a = m.bytes a := by
    intro a h1 h2
    simp only [m₄, m₃]
    rw [writeBits_out _ (by omega), writeBits_out _ (by omega),
      hb₂ a (fun p hp => by have := (zip_range_mem hp).1; omega), hbytes]
  have hkeep : ∀ al ∈ m.allocs, al.base ≠ h → Keeps m m₄ al := by
    intro al hal hne _
    have hal₄ : al ∈ m₄.allocs := by
      simp only [m₄, m₃, writeBits_allocs]; rw [ha₂, hallocs]; exact List.mem_cons_of_mem _ hal
    refine ⟨hal₄, fun x h1 h2 => hout x ?_ ?_⟩
    · rcases hm.wf.disj hal hh hne with h' | h' <;> simp at h' <;> omega
    · have := hm.wf.below al hal; omega
  refine ⟨m₄, data, rfl, hge, ?_, ⟨hwf₄, fun h' d' es' hH => ?_, fun h₁ d₁ es₁ h₂ d₂ es₂ hH₁ hH₂ => ?_⟩, hkeep⟩
  · simp only [m₄, m₃, writeBits_next]; rw [hn₂, ← hm₁]; simp [Mem.alloc]
    have := (alignUp16 m.next).1; omega
  · by_cases he : h' = h
    · subst he
      simp at hH; obtain ⟨rfl, rfl⟩ := hH
      refine ⟨hh₃, by simp only [m₄, m₃, writeBits_allocs]; rw [ha₂]; exact hmem, hlen,
        ?_, ?_, fun i hi => ?_⟩
      · exact (wordAt_writeBits m₂ _ _).writeBits (by omega)
      · exact wordAt_writeBits m₃ _ _
      · obtain ⟨w₁, w₂⟩ := hw₂ _ (mem_zip_range es i hi)
        exact ⟨(w₁.writeBits (by omega)).writeBits (by omega),
          (w₂.writeBits (by omega)).writeBits (by omega)⟩
    · rw [Heap.set_other _ _ he] at hH
      have ho := hm.obj h' d' es' hH
      exact ho.keeps (hkeep _ ho.hdr (by simpa using he))
        (hkeep _ ho.arr (by simpa using hsep h' d' es' hH he))
  · have lt : ∀ x d e, H x = some (d, e) → x < m.next ∧ d < m.next := fun x d e hx =>
      hm.pieces_lt hx
    by_cases e₁ : h₁ = h <;> by_cases e₂ : h₂ = h
    · subst e₁; subst e₂; simp at hH₁ hH₂
      obtain ⟨rfl, rfl⟩ := hH₁
      exact ⟨by omega, fun h => absurd rfl h⟩
    · subst e₁; simp at hH₁; obtain ⟨rfl, rfl⟩ := hH₁
      rw [Heap.set_other _ _ e₂] at hH₂
      have := lt _ _ _ hH₂
      exact ⟨by omega, fun _ => by omega⟩
    · subst e₂; simp at hH₂; obtain ⟨rfl, rfl⟩ := hH₂
      rw [Heap.set_other _ _ e₁] at hH₁
      have := lt _ _ _ hH₁
      exact ⟨hsep _ _ _ hH₁ e₁, fun _ => by omega⟩
    · rw [Heap.set_other _ _ e₁] at hH₁; rw [Heap.set_other _ _ e₂] at hH₂
      exact hm.sep _ _ _ _ _ _ hH₁ hH₂

theorem newMapObj_spec {m : Mem} {H : Heap} (hm : MemModels m H) (es : List (Word × Word)) :
    newMapObj m es = .trap oomTrap ∨
    ∃ h m' d, newMapObj m es = .ok (h, m') ∧ m.next ≤ h ∧ h < 2 ^ 64 ∧ H h = none ∧
      m.next ≤ d ∧ m.next ≤ m'.next ∧ MemModels m' (H.set h (d, es)) ∧
      (∀ al ∈ m.allocs, Keeps m m' al) := by
  unfold newMapObj
  by_cases hfit' : ¬ (m.alloc 16 16).2.fits = true
  · left; simp at hfit'; simp [Nat.not_le.2 hfit']
  have hfit : (m.alloc 16 16).2.fits = true := Classical.not_not.1 hfit'
  simp only [hfit, Res.trapUnless_true, Res.ok_bind]
  obtain ⟨hm₁, hfree⟩ := hm.alloc (Nat.le_refl 16) hfit
  obtain ⟨_, hge, _, hlt, hmem, hallocs, _⟩ := hm.wf.alloc (Nat.le_refl 16) hfit
  generalize hh : (m.alloc 16 16).1 = h at *
  generalize hm₁' : (m.alloc 16 16).2 = m₁ at *
  have hnone : H h = none := by
    cases hH : H h with
    | none => rfl
    | some p => have := hm.pieces_lt hH; omega
  rcases writeEntries_spec hm₁ es hmem (fun h' d' es' hH _ => (hfree h' d' es' hH).2.symm) with
    ht | ⟨m', d, he, hd, hn, hm', hk⟩
  · left; rw [ht]; rfl
  · right
    have : m.next ≤ m₁.next := by
      rw [← hm₁']; simp [Mem.alloc]; have := (alignUp16 m.next).1; omega
    refine ⟨h, m', d, by rw [he]; rfl, hge, by omega, hnone, by omega, by omega, hm',
      fun al hal => ?_⟩
    · have hk₁ := Keeps.alloc m 16 16 (Nat.le_refl 16) al
      rw [hm₁'] at hk₁
      refine hk₁.trans (hk al (hk₁ hal).1 ?_)
      have := hm.wf.below al hal; omega

end Compile.Proof
