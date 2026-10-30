import FV.Backend.Proof.IselMemSem
import FV.Backend.Proof.IselCmpRun
import FV.Concurrency.IselCheck
import FV.Concurrency.IselMemAux

/-!
# Helpers for the segment of a memory statement (T2h, #311, layer 2e)

* `seqRun_split`: a run of `A ++ B` that falls through is a run of `A` then of `B`;
* `seqRun_nomem`: a run of covered instructions without memory kinds keeps the memory;
* `bytes_of_mr`: the bytes a VCode write left at a CLIF access are the CLIF bytes there
  (`MemRelOk.bytes`);
* `applyR_local`: read events at one access change the memory only there.
-/

namespace Concurrency.IselMemHelp

open Arm ArmFoot ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  VCodeAddr SegFoot Code

theorem seqRun_split {V W : Type} {sem : ISem V W} :
    ∀ {A B : List MInst} {ρ ρ' : Nat → V} {w w' : W},
      seqRun sem (A ++ B) ρ w = some (.fall ρ' w') →
      ∃ ρ1 w1, seqRun sem A ρ w = some (.fall ρ1 w1) ∧ seqRun sem B ρ1 w1 = some (.fall ρ' w')
  | [], _, _, _, _, _, h => ⟨_, _, rfl, by simpa using h⟩
  | i :: A, B, ρ, ρ', w, w', h => by
    obtain ⟨ops, outs, w₁, hops, hsem, hlen, hrest⟩ := seqRun_cons_fall h
    obtain ⟨ρ1, w1, h1, h2⟩ := seqRun_split hrest
    refine ⟨ρ1, w1, ?_, h2⟩
    simp only [seqRun, hops, hsem, hlen, ite_true, h1, Option.map_some, SeqEnd.succ]

/-- **A run of covered instructions without memory kinds keeps the memory** (and the world
error-free and aligned). -/
theorem seqRun_nomem {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} (hX : TlsMemFree X) :
    ∀ {ms : List MInst} {ρ ρ' : Nat → CV} {w w' : ArmState},
      (∀ i ∈ ms, Covered fc i ∧ akinds i = []) → Arm.r .ERR w = .None → CheckSPAlignment w →
      seqRun (csem F fc X) ms ρ w = some (.fall ρ' w') →
      w'.mem = w.mem ∧ Arm.r .ERR w' = .None ∧ CheckSPAlignment w'
  | [], _, _, _, _, _, he, hal, h => by
    simp only [seqRun, Option.some.injEq, SeqEnd.fall.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, he, hal⟩
  | i :: ms, ρ, ρ', w, w', hms, he, hal, h => by
    obtain ⟨ops, outs, w₁, hops, hsem, -, hrest⟩ := seqRun_cons_fall h
    obtain ⟨hc, hk⟩ := hms i List.mem_cons_self
    have hcov := IselMemAux.covered_cov hc hops ρ
    have hst : i.isCtl = false → csemWF fc i (vuses ops ρ) = true ∧ CheckSPAlignment w := by
      intro hctl
      rcases hcov with h | h
      · rw [hctl] at h; cases h
      · exact ⟨h, hal⟩
    have hf := ifoot_csem (F := F) (ctx := fc) (X := X) (uses := vuses ops ρ) hX he hc.1 hc.2.1 hst
    rw [VCodeEvents.cEvs_nil hk] at hf
    have hm1 := SegRun.ifoot_nil_mem hf hsem
    obtain ⟨he1, hal1, -⟩ := csem_keep hc.1 hc.2.1 hcov he hal hsem
    obtain ⟨hm, he', hal'⟩ :=
      seqRun_nomem hX (fun j hj => hms j (List.mem_cons_of_mem _ hj)) he1 hal1 hrest
    exact ⟨hm.trans hm1, he', hal'⟩

/-- **The bytes of a VCode write at a CLIF access are the CLIF bytes there**: after the write,
the world holds the event's bytes, and the memory relation pins the initialised CLIF bytes. -/
theorem bytes_of_mr {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {f : Clif.Function} {MR : MemRelT} (hMR : MemRelOk F sb syms f MR)
    {sl : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {w : ArmState} (hmr : MR sl cm w)
    {a n : Nat} (hv : cm.valid a n = true) (hinit : ∀ k < n, (cm.bytes (a + k)).isSome)
    {e : Ev} (ha : e.addr = BitVec.ofNat 64 a) (hn : e.n = n)
    (hmem : ∀ k < n, w.mem (e.addr + BitVec.ofNat 64 k) =
      (e.val.extractLsb' (8 * k) 8)) :
    ProgE2E.bytesOf e.n e.val = getB cm.bytes a n := by
  subst hn
  apply List.ext_getElem
  · simp [ProgE2E.bytesOf, getB]
  intro k h1 h2
  simp only [ProgE2E.bytesOf, getB, List.getElem_map, List.getElem_range]
  have hk : k < e.n := by simpa [ProgE2E.bytesOf] using h1
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hinit k hk)
  rw [hx]
  have hb := hMR.bytes sl cm w (a + k) x hmr (valid_sub hv hk) hx
  rw [← hb, ← hmem k hk, ha]
  simp only [read_mem, read_store, BitVec.ofNat_add]

/-- **Read events at one access change the memory only there.** -/
theorem applyR_local {A : BitVec 64} {n : Nat} (hn : n ≤ 2 ^ 64) :
    ∀ {evs : List Ev} (m : Memory), (∀ e ∈ evs, e.addr = A ∧ e.n = n) →
      applyR evs m = writeM n A (readM n A (applyR evs m)) m
  | [], m, _ => (writeM_readM n A m).symm
  | e :: es, m, h => by
    obtain ⟨hA, hN⟩ := h e List.mem_cons_self
    have ih := applyR_local hn (m := if e.k.dir = .R then writeM e.n e.addr e.val m else m)
      (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [applyR]
    generalize hm1 : (if e.k.dir = .R then writeM e.n e.addr e.val m else m) = m1 at ih ⊢
    generalize hXv : applyR es m1 = Xv at ih ⊢
    have hw : ∀ v, writeM n A v m1 = writeM n A v m := by
      intro v
      funext x
      by_cases hx : ∃ k < n, A + BitVec.ofNat 64 k = x
      · obtain ⟨k, hk, rfl⟩ := hx
        rw [writeM_apply_in _ _ _ _ _ hn hk, writeM_apply_in _ _ _ _ _ hn hk]
      · simp only [not_exists, not_and] at hx
        rw [writeM_apply_out _ _ _ _ _ hx, writeM_apply_out _ _ _ _ _ hx, ← hm1]
        split
        · subst hA hN; rw [writeM_apply_out _ _ _ _ _ hx]
        · rfl
    calc Xv = writeM n A (readM n A Xv) m1 := ih
      _ = writeM n A (readM n A Xv) m := hw _

/-! ## The memory instruction, the access -/

theorem memBytes_form {i : MInst} {n : Nat} (h : SegShape.memBytes i = some n) :
    i.isCtl = false ∨ (∃ ty op fl a x d r1 r2, i = .atomicRmwLoop ty op fl a x d r1 r2) ∨
      (∃ ty fl a e x d r, i = .atomicCasLoop ty fl a e x d r) := by
  cases i <;> simp only [SegShape.memBytes, reduceCtorEq] at h
  all_goals first
    | exact .inl rfl
    | exact .inr (.inl ⟨_, _, _, _, _, _, _, _, rfl⟩)
    | exact .inr (.inr ⟨_, _, _, _, _, _, _, rfl⟩)

theorem akinds_dmb {i : MInst} (h : akinds i = [.dmb]) : i = .fence := by
  cases i <;> simp [akinds] at h ⊢

theorem ofOption_none {α : Type} {m : String} : (Clif.Res.ofOption m (none : Option α)) = .stuck m :=
  rfl

/-- A memory statement that runs has an access. -/
theorem access_of_ok {env : Clif.Env} {p : Clif.Program} {fr : Clif.Frame} {c : Clif.Mem}
    {inst : Clif.Inst} (hthr : IselCheck.threadInstB inst = true) (hnp : pureInst inst = false)
    (hfe : inst ≠ .fence) {r : List Clif.Val × Clif.Mem} (h : instOutcome env p fr c inst = .ok r) :
    ∃ a n, IselClif.access fr inst = some (a, n) := by
  cases inst <;> simp only [IselCheck.threadInstB, pureInst, Bool.not_eq_true'] at hthr hnp
  all_goals first
    | (exact absurd rfl hfe)
    | (cases hthr; done)
    | (cases hnp; done)
    | skip
  case load op ty fl pp off =>
    cases hp : fr.regs pp with
    | none => simp [instOutcome, Clif.evalInst, Clif.Frame.get, hp, ofOption_none] at h
    | some pv => exact ⟨Clif.effAddr pv off, op.size ty, by simp [IselClif.access, hthr, hp]⟩
  case store op ty fl x pp off =>
    cases hp : fr.regs pp with
    | none =>
      simp only [instOutcome, Clif.evalInst, Clif.Frame.get, hp, ofOption_none] at h
      cases hx : fr.getAs x ty <;> simp [hx] at h <;> cases h
    | some pv => exact ⟨Clif.effAddr pv off, op.size ty, by simp [IselClif.access, hp]⟩
  case atomicRmw op ty fl pp x =>
    cases hp : fr.regs pp with
    | none => simp [instOutcome, Clif.evalInst, Clif.Frame.get, hp, ofOption_none] at h
    | some pv => exact ⟨Clif.effAddr pv 0, ty.bytes, by simp [IselClif.access, hthr, hp]⟩
  case atomicCas ty fl pp ex x =>
    cases hp : fr.regs pp with
    | none => simp [instOutcome, Clif.evalInst, Clif.Frame.get, hp, ofOption_none] at h
    | some pv => exact ⟨Clif.effAddr pv 0, ty.bytes, by simp [IselClif.access, hthr, hp]⟩
  case atomicLoad ty fl pp =>
    cases hp : fr.regs pp with
    | none => simp [instOutcome, Clif.evalInst, Clif.Frame.get, hp, ofOption_none] at h
    | some pv => exact ⟨Clif.effAddr pv 0, ty.bytes, by simp [IselClif.access, hthr, hp]⟩
  case atomicStore ty fl x pp =>
    cases hp : fr.regs pp with
    | none =>
      simp only [instOutcome, Clif.evalInst, Clif.Frame.get, hp, ofOption_none] at h
      cases hx : fr.getAs x ty <;> simp [hx] at h <;> cases h
    | some pv => exact ⟨Clif.effAddr pv 0, ty.bytes, by simp [IselClif.access, hp]⟩

/-- The checked size of a statement's memory instruction is its access size, which is positive. -/
theorem expect_access {fr : Clif.Frame} {inst : Clif.Inst} {ks : List AKind} {nE a n : Nat}
    (he : SegShape.expect inst = some (ks, nE)) (ha : IselClif.access fr inst = some (a, n)) :
    nE = n ∧ 0 < n := by
  cases inst <;> simp only [SegShape.expect, reduceCtorEq, Option.some.injEq, Prod.mk.injEq,
    IselClif.access] at he ha
  case load op ty fl pp off =>
    obtain ⟨-, pv, -, hh⟩ := IselClif.access_some_ite ha
    simp only [Prod.mk.injEq] at hh
    rw [← he.2, ← hh.2]; exact ⟨rfl, by cases op <;> cases ty <;> decide⟩
  case store op ty fl x pp off =>
    obtain ⟨pv, -, hh⟩ := IselClif.access_some ha
    simp only [Prod.mk.injEq] at hh
    rw [← he.2, ← hh.2]; exact ⟨rfl, by cases op <;> cases ty <;> decide⟩
  case atomicRmw op ty fl pp x =>
    obtain ⟨-, pv, -, hh⟩ := IselClif.access_some_ite ha
    simp only [Prod.mk.injEq] at hh
    rw [← he.2, ← hh.2]; exact ⟨rfl, by cases ty <;> decide⟩
  case atomicCas ty fl pp ex x =>
    obtain ⟨-, pv, -, hh⟩ := IselClif.access_some_ite ha
    simp only [Prod.mk.injEq] at hh
    rw [← he.2, ← hh.2]; exact ⟨rfl, by cases ty <;> decide⟩
  case atomicLoad ty fl pp =>
    obtain ⟨-, pv, -, hh⟩ := IselClif.access_some_ite ha
    simp only [Prod.mk.injEq] at hh
    rw [← he.2, ← hh.2]; exact ⟨rfl, by cases ty <;> decide⟩
  case atomicStore ty fl x pp =>
    obtain ⟨pv, -, hh⟩ := IselClif.access_some ha
    simp only [Prod.mk.injEq] at hh
    rw [← he.2, ← hh.2]; exact ⟨rfl, by cases ty <;> decide⟩

end Concurrency.IselMemHelp
