import FV.Concurrency.FrameDisj
import FV.Concurrency.ArmAllocStraight
import FV.Concurrency.ClifCStep

/-!
# Geometry of a call segment (#473, `SegOkG` groundwork)

* `Nested.privA_sub`: a nested callee's private set (`PrivA`: outside its world `RL.F`) lies in
  its caller's: the callee's frame and dead stack are in the caller's dead stack, its kept
  addresses are the caller's frame and kept addresses (`B.G = A.FK`), and its code is private to
  the caller by hypothesis;
* `Nested.privA_callee_out`, `Nested.privA_callee`: with exact nesting (the callee entered at the
  caller's body `sp`, its region exactly the caller's callee budget) the caller's private set is
  in the callee's, up to the callee's explicit CLIF slots (`slotArea`) and the callee's outgoing
  stack-argument area `[spB, spB + intBase)` (empty when the callee passes no stack arguments:
  `intBase_eq_zero`);
* `cstep_reads_valid`: every memory event of a CLIF thread step is at memory valid in the step's
  state (the footprint of a `CStep` pins its events to the statement's checked access).
-/

namespace Concurrency.CallSegGeo

open Backend Backend.Proof E2E FrameDisj ArmAllocThread

/-! ## Private sets of nested activations -/

section nested
variable {A B : RL}

/-- **A nested callee's private set lies in its caller's.** -/
theorem Nested.privA_sub (hB : B.Wf) (hn : Nested A B)
    (hcode : ∀ a, CodeAddr B.s0 a → A.F a) : ∀ a, PrivA B a → PrivA A a := by
  intro a h
  unfold PrivA at h ⊢
  generalize BitVec.ofNat 64 a = x at h ⊢
  have hdead : Region B x → A.F x := fun hr => Or.inl (Or.inr (hn.region_dead hB.stack hr))
  rcases h with (hf | hd) | hg
  · rcases frameF_frame hB hf with hfr | hc
    · exact hdead (frame_region hfr)
    · exact hcode x hc
  · exact hdead (dead_region hB hd).1
  · rw [hn.keep] at hg
    rcases hg with hf | hg
    · exact Or.inl (Or.inl hf)
    · exact Or.inr hg

/-- The outgoing stack-argument area is empty without stack arguments. -/
theorem intBase_eq_zero {R : RL} (h : R.vc.outgoing = 0) : R.fr.intBase = 0 := by
  show alignTo R.vc.outgoing 16 = 0
  rw [h]; rfl

/-- **With exact nesting, the caller's private set is in the callee's**, up to the callee's
CLIF slots and its outgoing stack-argument area `[spB, spB + intBase)` (in its frame). -/
theorem Nested.privA_callee_out (hB : StackAvail B.K B.af B.s0) (hn : Nested A B)
    (hsp : spv B.s0 = A.spB) (hK : frameDrop B.af + B.K = A.K) :
    ∀ a, PrivA A a → PrivA B a ∨ slotArea B (BitVec.ofNat 64 a) ∨
      (Frame B (BitVec.ofNat 64 a) ∧ (BitVec.ofNat 64 a - B.spB).toNat < B.fr.intBase) := by
  intro a h
  unfold PrivA at h ⊢
  generalize BitVec.ofNat 64 a = x at h ⊢
  rcases h with (hf | hd) | hg
  · exact Or.inl (Or.inr (by rw [hn.keep]; exact Or.inl hf))
  · have hr : Region B x := by unfold Region; rw [hK, hsp]; exact hd
    have hsb : B.spB.toNat = (spv B.s0).toNat - frameDrop B.af ∧
        frameDrop B.af + B.K ≤ (spv B.s0).toNat := spBody_toNat hB
    obtain ⟨h1, h2⟩ := hsb
    unfold Region StackBelow at hr
    by_cases hfr : x.toNat < (spv B.s0).toNat ∧ (spv B.s0).toNat ≤ x.toNat + frameDrop B.af
    · have hoff : (x - B.spB).toNat = x.toNat - B.spB.toNat :=
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
      have ho : (x - (spv B.s0 - BitVec.ofNat 64 (frameDrop B.af))).toNat =
          x.toNat - B.spB.toNat := hoff
      by_cases c1 : (x - B.spB).toNat < B.fr.intBase
      · exact Or.inr (Or.inr ⟨hfr, c1⟩)
      by_cases c2 : (x - B.spB).toNat < B.fr.size
      · refine Or.inl (Or.inl (Or.inl ?_))
        unfold frameF; rw [ho]; left; exact ⟨by omega, by omega⟩
      by_cases c3 : (x - B.spB).toNat < B.af.frameSize
      · refine Or.inr (Or.inl ?_)
        unfold slotArea; exact ⟨by omega, c3⟩
      · refine Or.inl (Or.inl (Or.inl ?_))
        unfold frameF; rw [ho]; right; left; exact ⟨by omega, by omega⟩
    · refine Or.inl (Or.inl (Or.inr ?_))
      show StackBelow B.K B.spB x
      unfold StackBelow
      omega
  · exact Or.inl (Or.inr (by rw [hn.keep]; exact Or.inr hg))

/-- **With exact nesting and no outgoing stack arguments, the caller's private set is in the
callee's or its CLIF slots.** -/
theorem Nested.privA_callee (hB : StackAvail B.K B.af B.s0) (hn : Nested A B)
    (hsp : spv B.s0 = A.spB) (hK : frameDrop B.af + B.K = A.K) (hib : B.fr.intBase = 0) :
    ∀ a, PrivA A a → PrivA B a ∨ slotArea B (BitVec.ofNat 64 a) := fun a h => by
  rcases Nested.privA_callee_out hB hn hsp hK a h with h | h | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h
  · rw [hib] at h; exact absurd h (Nat.not_lt_zero _)

end nested

/-! ## The events of a CLIF thread step are at valid memory -/

section cstep
open Prog ClifThread IselClif ClifCStep

/-- `B` with the byte at `y` set to `o`. -/
def setB (B : Bytes) (y : Nat) (o : Option (BitVec 8)) : Bytes := fun x => if x = y then o else B x

/-- Agreement only depends on the bytes the read events read. -/
theorem agrees_congr {D : Nat → Prop} : ∀ {evs : List (Ev SKind BVal)} {B B' : Bytes},
    (∀ x, ¬ D x → B x = B' x) → (∀ e ∈ evs, e.dir = .R → ∀ j < e.n, ¬ D (e.loc + j)) →
    Agrees bytesI B evs → Agrees bytesI B' evs
  | [], _, _, _, _, _ => trivial
  | e :: es, B, B', hBB, hr, h => by
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun hd => ?_, agrees_congr (B := write1 bytesI B e) ?_
      (fun e' he' => hr e' (List.mem_cons_of_mem _ he')) h2⟩
    · rw [h1 hd]
      simp only [bytesI, getB]
      apply List.map_congr_left
      intro j hj
      exact hBB _ (hr e (by simp) hd j (List.mem_range.mp hj))
    · intro x hx
      simp only [write1]
      split
      · simp only [bytesI, putB]
        split
        · rfl
        · exact hBB x hx
      · exact hBB x hx

theorem agrees_setB {evs : List (Ev SKind BVal)} {B : Bytes} {y : Nat} {o : Option (BitVec 8)}
    (hy : ∀ e ∈ evs, e.dir = .R → ∀ j < e.n, e.loc + j ≠ y) (h : Agrees bytesI B evs) :
    Agrees bytesI (setB B y o) evs :=
  agrees_congr (D := (· = y)) (fun x hx => by simp [setB, hx]) hy h

/-- **Pinning a read**: if every memory agreeing with the read events (all within `[l, l + n)`)
holds the `n` bytes at `a`, then `l = a`. -/
theorem read_pin {evs : List (Ev SKind BVal)} {l n a : Nat} (hn : 0 < n)
    (hreads : ∀ e ∈ evs, e.dir = .R → ∀ j < e.n, l ≤ e.loc + j ∧ e.loc + j < l + n)
    {B0 : Bytes} (hB0 : Agrees bytesI B0 evs)
    (hR : ∀ B, Agrees bytesI B evs → ∀ j < n, (B (a + j)).isSome) : l = a := by
  have hin : ∀ j < n, l ≤ a + j ∧ a + j < l + n := by
    intro j hj
    refine Classical.byContradiction fun hc => ?_
    have hA : Agrees bytesI (setB B0 (a + j) none) evs := agrees_setB (fun e he hr k hk heq => by
      have := hreads e he hr k hk
      exact hc ⟨by omega, by omega⟩) hB0
    have := hR _ hA j hj
    simp [setB] at this
  have h0 := hin 0 hn
  have h1 := hin (n - 1) (by omega)
  omega

/-- **Pinning a write**: if on every memory agreeing with the read events (all within
`[a, a + n)`) the bytes `[l, l + n)` outside `[a, a + n)` are the write's, then `l = a`. -/
theorem write_pin {evs : List (Ev SKind BVal)} {l n a : Nat} {v : BVal} (hn : 0 < n)
    (hreads : ∀ e ∈ evs, e.dir = .R → ∀ j < e.n, a ≤ e.loc + j ∧ e.loc + j < a + n)
    {B0 : Bytes} (hB0 : Agrees bytesI B0 evs)
    (hW : ∀ B, Agrees bytesI B evs → ∀ y, l ≤ y → y < l + n → ¬ (a ≤ y ∧ y < a + n) →
      B y = v.getD (y - l) none) : l = a := by
  have hin : ∀ y, l ≤ y → y < l + n → a ≤ y ∧ y < a + n := by
    intro y h1 h2
    refine Classical.byContradiction fun hc => ?_
    have hy : ∀ e ∈ evs, e.dir = .R → ∀ j < e.n, e.loc + j ≠ y := fun e he hr j hj heq => by
      have := hreads e he hr j hj
      exact hc ⟨by omega, by omega⟩
    have e1 := hW _ (agrees_setB (o := none) hy hB0) y h1 h2 hc
    have e2 := hW _ (agrees_setB (o := some 0) hy hB0) y h1 h2 hc
    have := e1.trans e2.symm
    simp [setB] at this
  have h0 := hin l (Nat.le_refl _) (by omega)
  have h1 := hin (l + n - 1) (by omega) (by omega)
  omega

/-- The bytes of the last (write) event after a step's events. -/
theorem applyEvs_last (evs : List (Ev SKind BVal)) (w : Ev SKind BVal) (B : Bytes)
    (hw : w.dir = .W) (y : Nat) (h1 : w.loc ≤ y) (h2 : y < w.loc + w.n) :
    applyEvs bytesI B (evs ++ [w]) y = w.val.getD (y - w.loc) none := by
  simp only [applyEvs, List.foldl_append, List.foldl_cons, List.foldl_nil, write1, hw,
    ite_true, bytesI, putB, h1, h2, and_self]

theorem foldlM_isSome {β : Type} {f : β → Nat → Option β} :
    ∀ {l : List Nat} {init r : β}, l.foldlM f init = some r → ∀ x ∈ l, ∃ b, (f b x).isSome
  | [], _, _, _, x, hx => absurd hx List.not_mem_nil
  | y :: l, init, r, h, x, hx => by
    simp only [List.foldlM_cons] at h
    cases hf : f init y with
    | none => rw [hf] at h; simp at h
    | some b =>
      rw [hf] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨init, by rw [hf]; rfl⟩
      · exact foldlM_isSome (l := l) (init := b) h x hx

/-- A successful read's bytes are initialised. -/
theorem readBits_init {m : Clif.Mem} {big : Bool} {a n w : Nat} {r : BitVec w}
    (h : m.readBits big a n w = some r) : ∀ j < n, (m.bytes (a + j)).isSome := by
  intro j hj
  have hi : Clif.Mem.byteIndex big n (Clif.Mem.byteIndex big n j) = j := by
    unfold Clif.Mem.byteIndex; split <;> omega
  unfold Clif.Mem.readBits at h
  obtain ⟨b, hb⟩ := foldlM_isSome h (Clif.Mem.byteIndex big n j)
    (List.mem_range.mpr (byteIndex_lt hj))
  simp only [hi] at hb
  cases hx : m.bytes (a + j) with
  | none => rw [hx] at hb; simp at hb
  | some _ => rfl

theorem load_mem {c : Clif.Mem} {fl : Clif.MemFlags} {a n w : Nat} {r : BitVec w}
    (h : c.load fl a n w = .ok r) : c.valid a n = true ∧ ∀ j < n, (c.bytes (a + j)).isSome := by
  simp only [Clif.Mem.load, bind_ok] at h
  obtain ⟨u, hc, h⟩ := h
  refine ⟨checkAccess_valid hc, ?_⟩
  cases hr : c.readBits (fl.endianness == some .big) a n w with
  | none => rw [hr] at h; simp at h
  | some x => exact readBits_init hr

theorem store_mem {c c' : Clif.Mem} {fl : Clif.MemFlags} {a n w : Nat} {x : BitVec w}
    (h : c.store fl a n x = .ok c') :
    c.valid a n = true ∧ ∀ y, ¬ (a ≤ y ∧ y < a + n) → c'.bytes y = c.bytes y := by
  obtain ⟨hv, hst⟩ := store_ok h
  refine ⟨hv, fun y hy => ?_⟩
  rw [hst c rfl] at h
  cases h
  simp only [Clif.Mem.writeBits, hy, ite_false]

theorem ofOption_ok {α : Type} {msg : String} {o : Option α} {v : α}
    (h : Clif.Res.ofOption msg o = .ok v) : o = some v := by
  cases o <;> simp at h ⊢; exact h

/-! ### The memory statements' accesses -/

theorem eval_load {fr : Clif.Frame} {c : Clif.Mem} {op : Clif.LoadOp} {ty : Clif.Ty}
    {fl : Clif.MemFlags} {pp : Nat} {off : Int} {vals : List Clif.Val} {m : Clif.Mem}
    (h : Clif.evalInst fr c (.load op ty fl pp off) = .ok (vals, m)) :
    ∃ pv, fr.regs pp = some pv ∧ c.valid (Clif.effAddr pv off) (op.size ty) = true ∧
      ∀ j < op.size ty, (c.bytes (Clif.effAddr pv off + j)).isSome := by
  simp only [Clif.evalInst, Clif.Frame.get, bind_ok] at h
  obtain ⟨pv, hpv, u, -, raw, hl, -⟩ := h
  exact ⟨pv, ofOption_ok hpv, load_mem hl⟩

theorem eval_store {fr : Clif.Frame} {c : Clif.Mem} {op : Clif.StoreOp} {ty : Clif.Ty}
    {fl : Clif.MemFlags} {x pp : Nat} {off : Int} {vals : List Clif.Val} {m : Clif.Mem}
    (h : Clif.evalInst fr c (.store op ty fl x pp off) = .ok (vals, m)) :
    ∃ pv, fr.regs pp = some pv ∧ c.valid (Clif.effAddr pv off) (op.size ty) = true ∧
      ∀ y, ¬ (Clif.effAddr pv off ≤ y ∧ y < Clif.effAddr pv off + op.size ty) →
        m.bytes y = c.bytes y := by
  simp only [Clif.evalInst, Clif.Frame.get, bind_ok] at h
  obtain ⟨xv, -, pv, hpv, u, -, mem', hst, hp⟩ := h
  obtain ⟨-, rfl⟩ := pure_ok' hp
  exact ⟨pv, ofOption_ok hpv, store_mem hst⟩

theorem eval_atomicLoad {fr : Clif.Frame} {c : Clif.Mem} {ty : Clif.Ty}
    {fl : Clif.MemFlags} {pp : Nat} {vals : List Clif.Val} {m : Clif.Mem}
    (h : Clif.evalInst fr c (.atomicLoad ty fl pp) = .ok (vals, m)) :
    ∃ pv, fr.regs pp = some pv ∧ c.valid (Clif.effAddr pv 0) ty.bytes = true ∧
      ∀ j < ty.bytes, (c.bytes (Clif.effAddr pv 0 + j)).isSome := by
  simp only [Clif.evalInst, Clif.Frame.get, bind_ok] at h
  obtain ⟨pv, hpv, u, -, v, hl, -⟩ := h
  exact ⟨pv, ofOption_ok hpv, load_mem hl⟩

theorem eval_atomicStore {fr : Clif.Frame} {c : Clif.Mem} {ty : Clif.Ty}
    {fl : Clif.MemFlags} {x pp : Nat} {vals : List Clif.Val} {m : Clif.Mem}
    (h : Clif.evalInst fr c (.atomicStore ty fl x pp) = .ok (vals, m)) :
    ∃ pv, fr.regs pp = some pv ∧ c.valid (Clif.effAddr pv 0) ty.bytes = true ∧
      ∀ y, ¬ (Clif.effAddr pv 0 ≤ y ∧ y < Clif.effAddr pv 0 + ty.bytes) →
        m.bytes y = c.bytes y := by
  simp only [Clif.evalInst, Clif.Frame.get, bind_ok] at h
  obtain ⟨xv, -, pv, hpv, u, -, mem', hst, hp⟩ := h
  obtain ⟨-, rfl⟩ := pure_ok' hp
  exact ⟨pv, ofOption_ok hpv, store_mem hst⟩

theorem eval_atomicRmw {fr : Clif.Frame} {c : Clif.Mem} {op : Clif.AtomicRmwOp} {ty : Clif.Ty}
    {fl : Clif.MemFlags} {pp x : Nat} {vals : List Clif.Val} {m : Clif.Mem}
    (h : Clif.evalInst fr c (.atomicRmw op ty fl pp x) = .ok (vals, m)) :
    ∃ pv, fr.regs pp = some pv ∧ c.valid (Clif.effAddr pv 0) ty.bytes = true ∧
      (∀ j < ty.bytes, (c.bytes (Clif.effAddr pv 0 + j)).isSome) ∧
      ∀ y, ¬ (Clif.effAddr pv 0 ≤ y ∧ y < Clif.effAddr pv 0 + ty.bytes) →
        m.bytes y = c.bytes y := by
  simp only [Clif.evalInst, Clif.Frame.get, bind_ok] at h
  obtain ⟨pv, hpv, xv, -, u, -, old, hl, mem', hst, hp⟩ := h
  obtain ⟨-, rfl⟩ := pure_ok' hp
  exact ⟨pv, ofOption_ok hpv, (load_mem hl).1, (load_mem hl).2, (store_mem hst).2⟩

theorem eval_atomicCas {fr : Clif.Frame} {c : Clif.Mem} {ty : Clif.Ty}
    {fl : Clif.MemFlags} {pp ex x : Nat} {vals : List Clif.Val} {m : Clif.Mem}
    (h : Clif.evalInst fr c (.atomicCas ty fl pp ex x) = .ok (vals, m)) :
    ∃ pv, fr.regs pp = some pv ∧ c.valid (Clif.effAddr pv 0) ty.bytes = true ∧
      (∀ j < ty.bytes, (c.bytes (Clif.effAddr pv 0 + j)).isSome) ∧
      ∀ y, ¬ (Clif.effAddr pv 0 ≤ y ∧ y < Clif.effAddr pv 0 + ty.bytes) →
        m.bytes y = c.bytes y := by
  simp only [Clif.evalInst, Clif.Frame.get, bind_ok] at h
  obtain ⟨pv, hpv, ev, -, xv, -, u, -, old, hl, mem', hst, hp⟩ := h
  obtain ⟨-, rfl⟩ := pure_ok' hp
  refine ⟨pv, ofOption_ok hpv, (load_mem hl).1, (load_mem hl).2, ?_⟩
  split at hst
  · exact (store_mem hst).2
  · simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq] at hst
    subst hst
    exact fun _ _ => rfl

/-! ### The step -/

/-- A non-call statement's successful step is a successful outcome, whose memory gives the
step's bytes. -/
theorem step_ok {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {stm : Clif.Stmt}
    {rest : List Clif.Stmt} (hb : s.frame.body = stm :: rest)
    (hc : ∀ fn args, stm.inst ≠ .call fn args)
    (hci : ∀ sig callee args, stm.inst ≠ .callIndirect sig callee args)
    {B : Bytes} {t'' : TState} {X : Bytes}
    (h : res (Clif.step env p (withBytes s B)) = some (t'', X)) :
    ∃ vals m, Clif.evalInst s.frame (withB s.mem B) stm.inst = .ok (vals, m) ∧ X = m.bytes := by
  rw [Clif.step_inst env p (withBytes s B) stm rest hb hc hci] at h
  cases he : Clif.evalInst (withBytes s B).frame (withBytes s B).mem stm.inst with
  | ok r =>
    obtain ⟨vals, m⟩ := r
    rw [he] at h
    simp only [Clif.StepResult.ofRes, Clif.continueWith] at h
    split at h
    · simp only [res, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨vals, m, he, h.2.symm⟩
    · simp [res] at h
  | trap c => rw [he] at h; simp [Clif.StepResult.ofRes, res] at h
  | stuck msg => rw [he] at h; simp [Clif.StepResult.ofRes, res] at h

theorem loadSize_pos (op : Clif.LoadOp) (ty : Clif.Ty) : 0 < op.size ty := by
  cases op <;> cases ty <;> decide

theorem storeSize_pos (op : Clif.StoreOp) (ty : Clif.Ty) : 0 < op.size ty := by
  cases op <;> cases ty <;> decide

theorem bytes_pos (ty : Clif.Ty) : 0 < ty.bytes := by
  cases ty <;> decide

/-- **Every memory event of a CLIF thread step is at memory valid in the step's state**: the
footprint of the step pins its read and write events to the statement's access, which the
statement checks (`Clif.Mem.checkAccess`) before touching memory. -/
theorem cstep_reads_valid {env : Clif.Env} {p : Clif.Program} {s : Clif.State}
    {evs : List (Ev SKind BVal)} {t' : TState} (h : CStep env p (.run s) evs t') :
    ∀ e ∈ evs, e.dir ≠ .F → s.mem.valid e.loc e.n = true := by
  obtain ⟨⟨hsh, hd⟩, ⟨B0, hB0⟩, hf⟩ := h
  cases hb : s.frame.body with
  | nil =>
    simp only [evShape, hb] at hsh
    obtain rfl : evs = [] := by simpa using hsh
    intro e he; simp at he
  | cons stm rest =>
    have hE : (∀ fn args, stm.inst ≠ .call fn args) →
        (∀ sig callee args, stm.inst ≠ .callIndirect sig callee args) →
        ∀ B, Agrees bytesI B evs → ∃ vals m,
          Clif.evalInst s.frame (withB s.mem B) stm.inst = .ok (vals, m) ∧
          applyEvs bytesI B evs = m.bytes := fun hc hci B hB => by
      obtain ⟨t'', h1, -⟩ := hf B hB
      exact step_ok hb hc hci h1
    cases hi : stm.inst <;> simp only [evShape, hb, hi] at hsh <;> rw [hi] at hE
    all_goals first
      | (obtain rfl : evs = [] := by simpa using hsh
         intro e he; simp at he)
      | skip
    case fence =>
      rcases evs with _ | ⟨e1, _ | ⟨e2, evs⟩⟩ <;> simp at hsh
      intro e he hne
      simp only [List.mem_singleton] at he
      subst he
      exact absurd (by rw [(hd e (by simp)).1, hsh.1]; rfl) hne
    all_goals sorry

end cstep

end Concurrency.CallSegGeo
