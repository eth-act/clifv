module

public import FV.Concurrency.ClifThread
public import FV.Concurrency.IselClif

@[expose] public section

/-!
# The CLIF thread steps of the memory statements (T2h, #311, layer 2e groundwork)

Layer 2 realizes a VCode thread run by a run of the CLIF event semantics `ClifThread.CStep`. A
`CStep` is a `Clif.step` whose events are its footprint: on every byte memory holding the read
events' bytes, the step reaches the same state (up to the bytes) and writes exactly the write
events. This file proves it, from one successful `Clif.step`, for the statements with events:

* `cstep_of_eval`: the general shape — the statement's outcome on every byte memory agreeing
  with the read events is the same values and memory, with the write events applied;
* `cstep_load`, `cstep_store`, `cstep_atomicLoad`, `cstep_atomicStore`, `cstep_atomicRmw`,
  `cstep_atomicCas` (both outcomes of the comparison), `cstep_fence`: the events of `evShape`
  at the statement's access (`IselClif.access`): a read of the bytes there, a write of the
  stored value's bytes (`valB`).

Witness: `Witness.cstep_atomicLoad0`.
-/

namespace Concurrency.ClifCStep

open Prog ClifThread IselClif Backend.Proof

/-- The bytes of the `n`-byte store of `v` at an address (`writeBits`' byte order). -/
def valB {w : Nat} (big : Bool) (n : Nat) (v : BitVec w) : BVal :=
  (List.range n).map fun k => some (v.extractLsb' (8 * Clif.Mem.byteIndex big n k) 8)

theorem valB_length {w : Nat} (big : Bool) (n : Nat) (v : BitVec w) : (valB big n v).length = n := by
  simp [valB]

theorem getB_length (B : Bytes) (a n : Nat) : (getB B a n).length = n := by simp [getB]

/-- `writeBits` is `putB` of `valB`. -/
theorem writeBits_bytes {w : Nat} (c : Clif.Mem) (big : Bool) (a n : Nat) (v : BitVec w) :
    (c.writeBits big a n v).bytes = putB c.bytes a n (valB big n v) := by
  funext x
  simp only [Clif.Mem.writeBits, putB, valB]
  split
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  · rfl

theorem foldlM_congr {β : Type} {f g : β → Nat → Option β} :
    ∀ {l : List Nat} (init : β), (∀ x ∈ l, ∀ b, f b x = g b x) → l.foldlM f init = l.foldlM g init
  | [], _, _ => rfl
  | x :: l, init, h => by
    simp only [List.foldlM_cons]
    rw [h x (List.mem_cons_self ..)]
    cases g init x with
    | none => rfl
    | some b => exact foldlM_congr b fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem byteIndex_lt {big : Bool} {n i : Nat} (h : i < n) : Clif.Mem.byteIndex big n i < n := by
  unfold Clif.Mem.byteIndex; split <;> omega

/-- A read depends only on the bytes it reads. -/
theorem readBits_congr {c c' : Clif.Mem} {big : Bool} {a n w : Nat}
    (h : ∀ j < n, c.bytes (a + j) = c'.bytes (a + j)) :
    c.readBits big a n w = c'.readBits big a n w := by
  unfold Clif.Mem.readBits
  apply foldlM_congr
  intro i hi b
  rw [h _ (byteIndex_lt (List.mem_range.mp hi))]

theorem getB_eq {B B' : Bytes} {a n : Nat} (h : getB B a n = getB B' a n) :
    ∀ j < n, B (a + j) = B' (a + j) := by
  intro j hj
  have := congrArg (·[j]?) h
  simpa [getB, List.getElem?_map, List.getElem?_range hj] using this

/-- The memory `m` with bytes `B`. -/
abbrev withB (m : Clif.Mem) (B : Bytes) : Clif.Mem := { m with bytes := B }

/-- **A step whose outcome on every agreeing byte memory is the same values and memory, with the
write events applied, is a `CStep` with those events.** -/
theorem cstep_of_eval {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {stm : Clif.Stmt}
    {rest : List Clif.Stmt} (hb : s.frame.body = stm :: rest)
    (hc : ∀ fn args, stm.inst ≠ .call fn args)
    (hci : ∀ sig callee args, stm.inst ≠ .callIndirect sig callee args)
    {evs : List (Ev SKind BVal)} (hk : KindsOk s evs) (hag : Agrees bytesI s.mem.bytes evs)
    {vals : List Clif.Val} {m0 : Clif.Mem}
    (hev : ∀ B, Agrees bytesI B evs →
      Clif.evalInst s.frame (withB s.mem B) stm.inst = .ok (vals, withB m0 (applyEvs bytesI B evs)))
    {s' : Clif.State}
    (hs : Clif.step env p s = .next s') : CStep env p (.run s) evs (.run s') := by
  refine ⟨hk, ⟨_, hag⟩, fun B hB => ?_⟩
  have hb' : (withBytes s B).frame.body = stm :: rest := hb
  rw [Clif.step_inst env p _ stm rest hb hc hci] at hs
  have h0 : Clif.evalInst s.frame s.mem stm.inst =
      .ok (vals, withB m0 (applyEvs bytesI s.mem.bytes evs)) := hev s.mem.bytes hag
  rw [h0] at hs
  simp only [Clif.StepResult.ofRes, Clif.continueWith] at hs
  obtain ⟨regs, hregs⟩ : ∃ regs, s.frame.regs.setMany stm.results vals = some regs := by
    cases h : s.frame.regs.setMany stm.results vals with
    | none => rw [h] at hs; cases hs
    | some r => exact ⟨r, rfl⟩
  rw [hregs] at hs
  cases hs
  have h1 : Clif.evalInst (withBytes s B).frame (withBytes s B).mem stm.inst =
      .ok (vals, withB m0 (applyEvs bytesI B evs)) := hev B hB
  rw [Clif.step_inst env p _ stm rest hb' hc hci, h1]
  refine ⟨.run { (withBytes s B) with
      frame := { s.frame with regs := regs, body := rest }
      mem := withB m0 (applyEvs bytesI B evs) }, ?_, rfl⟩
  have hr : (withBytes s B).frame.regs = s.frame.regs := rfl
  simp only [Clif.StepResult.ofRes, Clif.continueWith, hr, hregs, res]
  rfl

theorem not_call_load {stm : Clif.Stmt} {i : Clif.Inst} (hi : stm.inst = i)
    (h : ∀ fn args, i ≠ .call fn args) (h' : ∀ sig callee args, i ≠ .callIndirect sig callee args) :
    (∀ fn args, stm.inst ≠ .call fn args) ∧
      ∀ sig callee args, stm.inst ≠ .callIndirect sig callee args :=
  ⟨fun fn args => hi ▸ h fn args, fun sig callee args => hi ▸ h' sig callee args⟩

/-- The statement's outcome from a successful step. -/
theorem eval_of_step {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {stm : Clif.Stmt}
    {rest : List Clif.Stmt} (hb : s.frame.body = stm :: rest)
    (hc : ∀ fn args, stm.inst ≠ .call fn args)
    (hci : ∀ sig callee args, stm.inst ≠ .callIndirect sig callee args) {s' : Clif.State}
    (hs : Clif.step env p s = .next s') :
    ∃ vals m, Clif.evalInst s.frame s.mem stm.inst = .ok (vals, m) := by
  rw [Clif.step_inst env p s stm rest hb hc hci] at hs
  cases h : Clif.evalInst s.frame s.mem stm.inst with
  | ok r => exact ⟨r.1, r.2, rfl⟩
  | trap c => rw [h] at hs; cases hs
  | stuck m => rw [h] at hs; cases hs

theorem pure_ok' {l vals : List Clif.Val} {c m : Clif.Mem}
    (h : (pure (l, c) : Clif.Res (List Clif.Val × Clif.Mem)) = .ok (vals, m)) : l = vals ∧ c = m := by
  simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq, Prod.mk.injEq] at h
  exact h

theorem applyEvs_read (B : Bytes) (k : SKind) (a n : Nat) (v : BVal) :
    applyEvs bytesI B [⟨k, .R, a, n, v⟩] = B := by
  simp [applyEvs, write1]

theorem applyEvs_write (B : Bytes) (k : SKind) (a n : Nat) (v : BVal) :
    applyEvs bytesI B [⟨k, .W, a, n, v⟩] = putB B a n v := by
  simp [applyEvs, write1, bytesI]

theorem load_withB {m : Clif.Mem} {B : Bytes} {fl : Clif.MemFlags} {a n w : Nat}
    (h : ∀ j < n, B (a + j) = m.bytes (a + j)) : (withB m B).load fl a n w = m.load fl a n w := by
  simp only [Clif.Mem.load, checkAccess_allocs (c := withB m B) (c' := m) rfl,
    readBits_congr (c := withB m B) (c' := m) h]

theorem writeBits_withB {w : Nat} (m : Clif.Mem) (B : Bytes) (big : Bool) (a n : Nat)
    (v : BitVec w) : (withB m B).writeBits big a n v = withB m (putB B a n (valB big n v)) := by
  have := writeBits_bytes (withB m B) big a n v
  simp only [Clif.Mem.writeBits] at this ⊢
  rw [this]

/-- **`load`**: a read of its access. -/
theorem cstep_load {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {stm : Clif.Stmt}
    {rest : List Clif.Stmt} {op : Clif.LoadOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {pp : Nat}
    {off : Int} (hb : s.frame.body = stm :: rest) (hi : stm.inst = .load op ty fl pp off)
    {pv : Clif.Val} (hpv : s.frame.regs pp = some pv) {s' : Clif.State}
    (hs : Clif.step env p s = .next s') :
    CStep env p (.run s) [⟨.naR, .R, Clif.effAddr pv off, op.size ty,
      getB s.mem.bytes (Clif.effAddr pv off) (op.size ty)⟩] (.run s') := by
  obtain ⟨hc, hci⟩ := not_call_load hi (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have e : ∀ c, Clif.evalInst s.frame c stm.inst =
      ((Clif.Res.check (op.size ty ≤ ty.bytes) "load: access wider than result") >>= fun _ =>
        (c.load fl (Clif.effAddr pv off) (op.size ty) (8 * op.size ty)) >>= fun raw =>
          pure ([⟨ty, if op.signed then raw.signExtend ty.width else raw.zeroExtend ty.width⟩], c)) := by
    intro c
    simp only [hi, Clif.evalInst, Clif.Frame.get, hpv, Clif.Res.ofOption_some, Clif.Res.ok_bind]
  obtain ⟨vals, m, hev⟩ := eval_of_step hb hc hci hs
  rw [e, bind_ok] at hev
  obtain ⟨u, hck, hev⟩ := hev
  rw [bind_ok] at hev
  obtain ⟨raw, hl, hev⟩ := hev
  refine cstep_of_eval (vals := vals) (m0 := s.mem) hb hc hci ?_ ?_ (fun B hB => ?_) hs
  · refine ⟨by simp [evShape, hb, hi], ?_⟩
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact ⟨rfl, getB_length ..⟩
  · exact ⟨fun _ => rfl, trivial⟩
  · rw [applyEvs_read B .naR, e, hck, Clif.Res.ok_bind,
      load_withB (getB_eq (hB.1 rfl).symm), hl, Clif.Res.ok_bind]
    obtain ⟨hv, -⟩ := pure_ok' hev
    rw [← hv]
    rfl

theorem getAs_ok' {fr : Clif.Frame} {x : Nat} {ty : Clif.Ty} {v : BitVec ty.width}
    (h : fr.getAs x ty = .ok v) {β : Type} (f : BitVec ty.width → Clif.Res β) :
    (fr.getAs x ty >>= f) = f v := by
  rw [h]; rfl

/-- **`store`**: a write of the stored value's bytes at its access. -/
theorem cstep_store {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {stm : Clif.Stmt}
    {rest : List Clif.Stmt} {op : Clif.StoreOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {x pp : Nat}
    {off : Int} (hb : s.frame.body = stm :: rest) (hi : stm.inst = .store op ty fl x pp off)
    {pv : Clif.Val} (hpv : s.frame.regs pp = some pv) {v : BitVec ty.width}
    (hx : s.frame.getAs x ty = .ok v) {s' : Clif.State} (hs : Clif.step env p s = .next s') :
    CStep env p (.run s) [⟨.naW, .W, Clif.effAddr pv off, op.size ty,
      valB (bigOf fl) (op.size ty) v⟩] (.run s') := by
  obtain ⟨hc, hci⟩ := not_call_load hi (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have e : ∀ c, Clif.evalInst s.frame c stm.inst =
      ((Clif.Res.check (op.size ty ≤ ty.bytes) "store: access wider than value") >>= fun _ =>
        (c.store fl (Clif.effAddr pv off) (op.size ty) v) >>= fun mem' => pure ([], mem')) := by
    intro c
    simp only [hi, Clif.evalInst, Clif.Frame.get, hpv, Clif.Res.ofOption_some, Clif.Res.ok_bind,
      getAs_ok' hx]
  obtain ⟨vals, m, hev⟩ := eval_of_step hb hc hci hs
  rw [e, bind_ok] at hev
  obtain ⟨u, hck, hev⟩ := hev
  rw [bind_ok] at hev
  obtain ⟨m1, hst, hev⟩ := hev
  refine cstep_of_eval (vals := vals) (m0 := s.mem) hb hc hci ?_ ?_ (fun B _ => ?_) hs
  · refine ⟨by simp [evShape, hb, hi], ?_⟩
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact ⟨rfl, valB_length ..⟩
  · exact ⟨(fun h => nomatch h), trivial⟩
  · rw [applyEvs_write, e, hck, Clif.Res.ok_bind, (store_ok hst).2 (withB s.mem B) rfl,
      Clif.Res.ok_bind, writeBits_withB]
    obtain ⟨hv, -⟩ := pure_ok' hev
    rw [← hv]
    rfl

/-- **`atomic_load`**: an `scR` read of its access. -/
theorem cstep_atomicLoad {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {stm : Clif.Stmt}
    {rest : List Clif.Stmt} {ty : Clif.Ty} {fl : Clif.MemFlags} {pp : Nat}
    (hb : s.frame.body = stm :: rest) (hi : stm.inst = .atomicLoad ty fl pp)
    {pv : Clif.Val} (hpv : s.frame.regs pp = some pv) {s' : Clif.State}
    (hs : Clif.step env p s = .next s') :
    CStep env p (.run s) [⟨.scR, .R, Clif.effAddr pv 0, ty.bytes,
      getB s.mem.bytes (Clif.effAddr pv 0) ty.bytes⟩] (.run s') := by
  obtain ⟨hc, hci⟩ := not_call_load hi (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have e : ∀ c, Clif.evalInst s.frame c stm.inst =
      ((Clif.Res.check (Clif.effAddr pv 0 % ty.bytes == 0) "misaligned atomic access") >>= fun _ =>
        (c.load fl (Clif.effAddr pv 0) ty.bytes ty.width) >>= fun v => pure ([⟨ty, v⟩], c)) := by
    intro c
    simp only [hi, Clif.evalInst, Clif.Frame.get, hpv, Clif.Res.ofOption_some, Clif.Res.ok_bind]
  obtain ⟨vals, m, hev⟩ := eval_of_step hb hc hci hs
  rw [e, bind_ok] at hev
  obtain ⟨u, hck, hev⟩ := hev
  rw [bind_ok] at hev
  obtain ⟨raw, hl, hev⟩ := hev
  refine cstep_of_eval (vals := vals) (m0 := s.mem) hb hc hci ?_ ?_ (fun B hB => ?_) hs
  · refine ⟨by simp [evShape, hb, hi], ?_⟩
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact ⟨rfl, getB_length ..⟩
  · exact ⟨fun _ => rfl, trivial⟩
  · rw [applyEvs_read B .scR, e, hck, Clif.Res.ok_bind,
      load_withB (getB_eq (hB.1 rfl).symm), hl, Clif.Res.ok_bind]
    obtain ⟨hv, -⟩ := pure_ok' hev
    rw [← hv]
    rfl

/-- **`atomic_store`**: an `scW` write of the stored value's bytes at its access. -/
theorem cstep_atomicStore {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {stm : Clif.Stmt}
    {rest : List Clif.Stmt} {ty : Clif.Ty} {fl : Clif.MemFlags} {x pp : Nat}
    (hb : s.frame.body = stm :: rest) (hi : stm.inst = .atomicStore ty fl x pp)
    {pv : Clif.Val} (hpv : s.frame.regs pp = some pv) {v : BitVec ty.width}
    (hx : s.frame.getAs x ty = .ok v) {s' : Clif.State} (hs : Clif.step env p s = .next s') :
    CStep env p (.run s) [⟨.scW, .W, Clif.effAddr pv 0, ty.bytes,
      valB (bigOf fl) ty.bytes v⟩] (.run s') := by
  obtain ⟨hc, hci⟩ := not_call_load hi (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have e : ∀ c, Clif.evalInst s.frame c stm.inst =
      ((Clif.Res.check (Clif.effAddr pv 0 % ty.bytes == 0) "misaligned atomic access") >>= fun _ =>
        (c.store fl (Clif.effAddr pv 0) ty.bytes v) >>= fun mem' => pure ([], mem')) := by
    intro c
    simp only [hi, Clif.evalInst, Clif.Frame.get, hpv, Clif.Res.ofOption_some, Clif.Res.ok_bind,
      getAs_ok' hx]
  obtain ⟨vals, m, hev⟩ := eval_of_step hb hc hci hs
  rw [e, bind_ok] at hev
  obtain ⟨u, hck, hev⟩ := hev
  rw [bind_ok] at hev
  obtain ⟨m1, hst, hev⟩ := hev
  refine cstep_of_eval (vals := vals) (m0 := s.mem) hb hc hci ?_ ?_ (fun B _ => ?_) hs
  · refine ⟨by simp [evShape, hb, hi], ?_⟩
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact ⟨rfl, valB_length ..⟩
  · exact ⟨(fun h => nomatch h), trivial⟩
  · rw [applyEvs_write, e, hck, Clif.Res.ok_bind, (store_ok hst).2 (withB s.mem B) rfl,
      Clif.Res.ok_bind, writeBits_withB]
    obtain ⟨hv, -⟩ := pure_ok' hev
    rw [← hv]
    rfl

theorem applyEvs_rw (B : Bytes) (a n : Nat) (r w : BVal) :
    applyEvs bytesI B [⟨SKind.scR, .R, a, n, r⟩, ⟨.scW, .W, a, n, w⟩] = putB B a n w := by
  simp [applyEvs, write1, bytesI]

/-- **`atomic_rmw`**: an `scR` read of the old value's bytes, then an `scW` write of the new
value's bytes, at its access. -/
theorem cstep_atomicRmw {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {stm : Clif.Stmt}
    {rest : List Clif.Stmt} {op : Clif.AtomicRmwOp} {ty : Clif.Ty} {fl : Clif.MemFlags}
    {pp x : Nat} (hb : s.frame.body = stm :: rest) (hi : stm.inst = .atomicRmw op ty fl pp x)
    {pv : Clif.Val} (hpv : s.frame.regs pp = some pv) {v : BitVec ty.width}
    (hx : s.frame.getAs x ty = .ok v) {old : BitVec ty.width}
    (hold : s.mem.load fl (Clif.effAddr pv 0) ty.bytes ty.width = .ok old) {s' : Clif.State}
    (hs : Clif.step env p s = .next s') :
    CStep env p (.run s) [⟨.scR, .R, Clif.effAddr pv 0, ty.bytes,
        getB s.mem.bytes (Clif.effAddr pv 0) ty.bytes⟩,
      ⟨.scW, .W, Clif.effAddr pv 0, ty.bytes,
        valB (bigOf fl) ty.bytes (Clif.Sem.atomicRmw op old v)⟩] (.run s') := by
  obtain ⟨hc, hci⟩ := not_call_load hi (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have e : ∀ c, Clif.evalInst s.frame c stm.inst =
      ((Clif.Res.check (Clif.effAddr pv 0 % ty.bytes == 0) "misaligned atomic access") >>= fun _ =>
        (c.load fl (Clif.effAddr pv 0) ty.bytes ty.width) >>= fun old =>
          (c.store fl (Clif.effAddr pv 0) ty.bytes (Clif.Sem.atomicRmw op old v)) >>= fun mem' =>
            pure ([⟨ty, old⟩], mem')) := by
    intro c
    simp only [hi, Clif.evalInst, Clif.Frame.get, hpv, Clif.Res.ofOption_some, Clif.Res.ok_bind,
      getAs_ok' hx]
  obtain ⟨vals, m, hev⟩ := eval_of_step hb hc hci hs
  rw [e, bind_ok] at hev
  obtain ⟨u, hck, hev⟩ := hev
  rw [hold, Clif.Res.ok_bind, bind_ok] at hev
  obtain ⟨m1, hst, hev⟩ := hev
  refine cstep_of_eval (vals := vals) (m0 := s.mem) hb hc hci ?_ ?_ (fun B hB => ?_) hs
  · refine ⟨by simp [evShape, hb, hi], ?_⟩
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact ⟨rfl, getB_length ..⟩
    · exact ⟨rfl, valB_length ..⟩
  · exact ⟨fun _ => rfl, (fun h => nomatch h), trivial⟩
  · rw [applyEvs_rw, e, hck, Clif.Res.ok_bind, load_withB (getB_eq (hB.1 rfl).symm), hold,
      Clif.Res.ok_bind, (store_ok hst).2 (withB s.mem B) rfl, Clif.Res.ok_bind, writeBits_withB]
    obtain ⟨hv, -⟩ := pure_ok' hev
    rw [← hv]
    rfl

/-- **`atomic_cas`**: an `scR` read of the old value's bytes at its access, then, if it equals
the expected value, an `scW` write of the replacement's bytes. -/
theorem cstep_atomicCas {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {stm : Clif.Stmt}
    {rest : List Clif.Stmt} {ty : Clif.Ty} {fl : Clif.MemFlags} {pp ex x : Nat}
    (hb : s.frame.body = stm :: rest) (hi : stm.inst = .atomicCas ty fl pp ex x)
    {pv : Clif.Val} (hpv : s.frame.regs pp = some pv) {ev v : BitVec ty.width}
    (hex : s.frame.getAs ex ty = .ok ev) (hx : s.frame.getAs x ty = .ok v)
    {old : BitVec ty.width}
    (hold : s.mem.load fl (Clif.effAddr pv 0) ty.bytes ty.width = .ok old) {s' : Clif.State}
    (hs : Clif.step env p s = .next s') :
    CStep env p (.run s) (⟨.scR, .R, Clif.effAddr pv 0, ty.bytes,
        getB s.mem.bytes (Clif.effAddr pv 0) ty.bytes⟩ ::
      if old == ev then [⟨.scW, .W, Clif.effAddr pv 0, ty.bytes, valB (bigOf fl) ty.bytes v⟩]
      else []) (.run s') := by
  obtain ⟨hc, hci⟩ := not_call_load hi (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have e : ∀ c, Clif.evalInst s.frame c stm.inst = (do
      let ev ← s.frame.getAs ex ty
      let a ← s.frame.getAs x ty
      Clif.Res.check (Clif.effAddr pv 0 % ty.bytes == 0) "misaligned atomic access"
      let old ← c.load fl (Clif.effAddr pv 0) ty.bytes ty.width
      let mem' ← if old == ev then c.store fl (Clif.effAddr pv 0) ty.bytes a else pure c
      pure ([⟨ty, old⟩], mem')) := by
    intro c
    simp only [hi, Clif.evalInst, Clif.Frame.get, hpv, Clif.Res.ofOption_some, Clif.Res.ok_bind]
  obtain ⟨vals, m, hev⟩ := eval_of_step hb hc hci hs
  rw [e, getAs_ok' hex, getAs_ok' hx, bind_ok] at hev
  obtain ⟨u, hck, hev⟩ := hev
  rw [hold, Clif.Res.ok_bind] at hev
  have hkinds : ∀ (w : List (Ev SKind BVal)), (w = [] ∨ w = [⟨.scW, .W, Clif.effAddr pv 0,
      ty.bytes, valB (bigOf fl) ty.bytes v⟩]) →
      KindsOk s (⟨.scR, .R, Clif.effAddr pv 0, ty.bytes,
        getB s.mem.bytes (Clif.effAddr pv 0) ty.bytes⟩ :: w) := by
    intro w hw
    rcases hw with rfl | rfl
    · refine ⟨by simp [evShape, hb, hi], ?_⟩
      intro e he
      simp only [List.mem_singleton] at he
      subst he
      exact ⟨rfl, getB_length ..⟩
    · refine ⟨by simp [evShape, hb, hi], ?_⟩
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact ⟨rfl, getB_length ..⟩
      · exact ⟨rfl, valB_length ..⟩
  have hl : ∀ B : Bytes, getB s.mem.bytes (Clif.effAddr pv 0) ty.bytes =
      getB B (Clif.effAddr pv 0) ty.bytes →
      (withB s.mem B).load fl (Clif.effAddr pv 0) ty.bytes ty.width = .ok old := fun B h => by
    rw [load_withB (getB_eq h.symm), hold]
  by_cases hq : (old == ev) = true
  · simp only [hq, ite_true] at hev ⊢
    rw [bind_ok] at hev
    obtain ⟨m1, hst, hev⟩ := hev
    refine cstep_of_eval (vals := vals) (m0 := s.mem) hb hc hci (hkinds _ (.inr rfl))
      ⟨fun _ => rfl, (fun h => nomatch h), trivial⟩ (fun B hB => ?_) hs
    rw [applyEvs_rw, e, getAs_ok' hex, getAs_ok' hx, hck, Clif.Res.ok_bind, hl B (hB.1 rfl),
      Clif.Res.ok_bind]
    simp only [hq, ite_true]
    rw [(store_ok hst).2 (withB s.mem B) rfl, Clif.Res.ok_bind, writeBits_withB]
    obtain ⟨hv, -⟩ := pure_ok' hev
    rw [← hv]
    rfl
  · simp only [hq, Bool.false_eq_true, ite_false] at hev ⊢
    refine cstep_of_eval (vals := vals) (m0 := s.mem) hb hc hci (hkinds _ (.inl rfl))
      ⟨fun _ => rfl, trivial⟩ (fun B hB => ?_) hs
    rw [applyEvs_read, e, getAs_ok' hex, getAs_ok' hx, hck, Clif.Res.ok_bind, hl B (hB.1 rfl),
      Clif.Res.ok_bind]
    simp only [hq, Bool.false_eq_true, ite_false]
    obtain ⟨hv, -⟩ := pure_ok' hev
    rw [← hv]
    rfl

/-- **`fence`**: its `fence` event. -/
theorem cstep_fence {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {stm : Clif.Stmt}
    {rest : List Clif.Stmt} (hb : s.frame.body = stm :: rest) (hi : stm.inst = .fence)
    {s' : Clif.State} (hs : Clif.step env p s = .next s') :
    CStep env p (.run s) [⟨.fence, .F, 0, 0, []⟩] (.run s') := by
  obtain ⟨hc, hci⟩ := not_call_load hi (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have e : ∀ c, Clif.evalInst s.frame c stm.inst = pure ([], c) := by
    intro c
    simp only [hi, Clif.evalInst]
  refine cstep_of_eval (vals := []) (m0 := s.mem) hb hc hci ?_ ?_ (fun B _ => ?_) hs
  · refine ⟨by simp [evShape, hb, hi], ?_⟩
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact ⟨rfl, rfl⟩
  · exact ⟨(fun h => nomatch h), trivial⟩
  · rw [e]
    simp [applyEvs, write1]

end Concurrency.ClifCStep
