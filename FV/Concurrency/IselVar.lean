import FV.Concurrency.IselMem
import FV.Concurrency.IselMemAux
import FV.Concurrency.VCodeSize

/-!
# The memory instruction's events are the CLIF access (T2h, #311, layer 2e)

**`events_at_access`**: for a memory statement whose code (`LowerInstOk`) has exactly one
instruction with a memory kind, `mi` at index `m`, of the access size, on a matched pair (CLIF
memory and world, `MemRelOk`) where the CLIF statement succeeds, the run of the code reaches `mi`
and every event of `mi`'s footprint (`cEvs`) is the CLIF access (address `a`, `n` bytes): every
byte of the access lies in an event of the run (`IselClif.access_in_events`, the footprint premises
`SegFoot.runFoot_csem`), only `mi` has events (`IselCover.cover_of_not_runOut`), and its events
are one access of `n` bytes (`VCodeSize.cEvs_size`, `addr_eq_of_oneAcc`).
-/

namespace Concurrency.IselVar

open Arm ArmFoot ArmThread Backend Backend.Proof Backend.Proof.Driver VCodeThread VCodeAddr
  VCodeSize IselCover IselFoot IselClif SegFoot IselMemAux Code

/-- The index of the one element with a property. -/
theorem index_unique {α : Type} {P : α → Bool} {pre post : List α} {x : α}
    (hpre : ∀ y ∈ pre, P y = false) (hpost : ∀ y ∈ post, P y = false) {j : Nat} {i : α}
    (hj : (pre ++ x :: post)[j]? = some i) (hi : P i = true) : j = pre.length ∧ i = x := by
  rcases Nat.lt_trichotomy j pre.length with h | h | h
  · rw [List.getElem?_append_left h] at hj
    have := hpre i (List.mem_of_getElem? hj)
    rw [hi] at this; cases this
  · subst h
    rw [List.getElem?_append_right (Nat.le_refl _)] at hj
    simp at hj
    exact ⟨rfl, hj.symm⟩
  · rw [List.getElem?_append_right (by omega)] at hj
    obtain ⟨j', rfl⟩ : ∃ j', j = pre.length + 1 + j' := ⟨j - pre.length - 1, by omega⟩
    rw [show pre.length + 1 + j' - pre.length = j' + 1 by omega] at hj
    simp only [List.getElem?_cons_succ] at hj
    have := hpost i (List.mem_of_getElem? hj)
    rw [hi] at this; cases this

theorem access_le {fr : Clif.Frame} {inst : Clif.Inst} {a n : Nat}
    (h : access fr inst = some (a, n)) : n ≤ 16 := by
  cases inst <;> simp only [access, reduceCtorEq] at h
  case load op ty fl pp off =>
    obtain ⟨-, pv, -, he⟩ := access_some_ite h
    simp only [Prod.mk.injEq] at he; rw [← he.2]; cases op <;> cases ty <;> decide
  case store op ty fl x pp off =>
    obtain ⟨pv, -, he⟩ := access_some h
    simp only [Prod.mk.injEq] at he; rw [← he.2]; cases op <;> cases ty <;> decide
  case atomicRmw op ty fl pp x =>
    obtain ⟨-, pv, -, he⟩ := access_some_ite h
    simp only [Prod.mk.injEq] at he; rw [← he.2]; cases ty <;> decide
  case atomicCas ty fl pp ex x =>
    obtain ⟨-, pv, -, he⟩ := access_some_ite h
    simp only [Prod.mk.injEq] at he; rw [← he.2]; cases ty <;> decide
  case atomicLoad ty fl pp =>
    obtain ⟨-, pv, -, he⟩ := access_some_ite h
    simp only [Prod.mk.injEq] at he; rw [← he.2]; cases ty <;> decide
  case atomicStore ty fl x pp =>
    obtain ⟨pv, -, he⟩ := access_some h
    simp only [Prod.mk.injEq] at he; rw [← he.2]; cases ty <;> decide

/-- **The events of the memory instruction are the CLIF access** (module doc). -/
theorem events_at_access {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {MR : MemRelT}
    {env : Clif.Env} {p : Clif.Program} {ctx : Ctx} {inst : Clif.Inst} {results : List Nat}
    {st : LState} {rss : List (List Reg)} {st' : LState} {pre post : List MInst} {mi : MInst}
    {sb : Nat} {syms : String → Option Nat} {f : Clif.Function}
    (hok : LowerInstOk (csem F fc X) MR env p ctx inst results st rss st' (pre ++ mi :: post))
    (hMR : MemRelOk F sb syms f MR) (hres : isStore inst = false → results ≠ [])
    (hX : TlsMemFree X) (hcov : ∀ i ∈ pre ++ mi :: post, Covered fc i)
    (hpre : ∀ y ∈ pre, akinds y = []) (hpost : ∀ y ∈ post, akinds y = [])
    {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : ArmState}
    (hf : fr.func = ctx.func) (hv : ValsHeld fr ρ) (hd : DFGCons ctx fr) (hmr : MR fr.slots cm w)
    (he : Arm.r .ERR w = .None) (hal : Arm.CheckSPAlignment w)
    {vs : List Clif.Val} {cm' : Clif.Mem} (h : instOutcome env p fr cm inst = .ok (vs, cm'))
    {a n : Nat} (hacc : access fr inst = some (a, n))
    (hro : isCas inst = true → cm.readonlyAt a n = false)
    (hn : SegShape.memBytes mi = some n) (hn0 : 0 < n)
    {ρ' : Nat → CV} {w' : ArmState}
    (hrun : seqRun (csem F fc X) (pre ++ mi :: post) ρ w = some (.fall ρ' w')) :
    ∃ ρm wm ops, RunAt (csem F fc X) (pre ++ mi :: post) ρ w pre.length ρm wm ∧
      mi.operands = .ok ops ∧ cEvs F fc mi (vuses ops ρm) wm ≠ [] ∧
      AtA (BitVec.ofNat 64 a) n (cEvs F fc mi (vuses ops ρm) wm) ∧
      (∃ r, csem F fc X mi (vuses ops ρm) wm = some r) ∧ Arm.r .ERR wm = .None ∧
      Arm.CheckSPAlignment wm := by
  have hnot : ∀ k < n, ¬ RunOut (csem F fc X) (BitVec.ofNat 64 (a + k)) (pre ++ mi :: post) ρ w :=
    fun k hk => access_in_events hok hMR hres hf hv hd hmr h hacc hro hk
  have hRF := runFoot_csem (F := F) (ctx := fc) (X := X) hX (ρ := ρ) hcov he hal
  have hP : ∀ y ∈ pre, (!(akinds y).isEmpty) = false := fun y hy => by simp [hpre y hy]
  have hQ : ∀ y ∈ post, (!(akinds y).isEmpty) = false := fun y hy => by simp [hpost y hy]
  -- every covering event is an event of `mi` at its reached state
  have hcover : ∀ k < n, ∃ ρj wj ops, RunAt (csem F fc X) (pre ++ mi :: post) ρ w pre.length ρj wj ∧
      mi.operands = .ok ops ∧ ∃ e ∈ cEvs F fc mi (vuses ops ρj) wj, ∃ kk < e.n,
        e.addr + BitVec.ofNat 64 kk = BitVec.ofNat 64 (a + k) := by
    intro k hk
    obtain ⟨j, ρj, wj, i, ops, hat, hj, hops, e, hev, kk, hkk, hx⟩ :=
      cover_of_not_runOut hRF (hnot k hk)
    have hak : (!(akinds i).isEmpty) = true := by
      cases hk : akinds i with
      | nil => rw [VCodeEvents.cEvs_nil hk] at hev; cases hev
      | cons _ _ => rfl
    obtain ⟨rfl, rfl⟩ := index_unique hP hQ hj hak
    exact ⟨ρj, wj, ops, hat, hops, e, hev, kk, hkk, hx⟩
  obtain ⟨ρm, wm, ops, hat, hops, e0, he0, -⟩ := hcover 0 hn0
  have hall : ∀ k < n, ∃ e ∈ cEvs F fc mi (vuses ops ρm) wm, ∃ kk < e.n,
      e.addr + BitVec.ofNat 64 kk = BitVec.ofNat 64 (a + k) := by
    intro k hk
    obtain ⟨ρj, wj, ops', hat', hops', hc⟩ := hcover k hk
    obtain ⟨rfl, rfl⟩ := runAt_det hat' hat
    rw [hops] at hops'; cases hops'
    exact hc
  have hmid : (pre ++ mi :: post)[pre.length]? = some mi := by simp
  obtain ⟨outs, w2, hstep⟩ := runAt_step hrun hat hmid hops
  obtain ⟨hem, halm⟩ := runAt_keep hcov he hal hat
  have hcm := hcov mi (by simp)
  have hst : mi.isCtl = false → csemWF fc mi (vuses ops ρm) = true ∧ Arm.CheckSPAlignment wm :=
    fun hc => by
      rcases covered_cov hcm hops ρm with h | h
      · rw [hc] at h; cases h
      · exact ⟨h, halm⟩
  have hone := cEvs_size hem hst hstep hn
  have hvalid : cm.valid a n = true := by
    have hfa := IselMem.mem_facts h hacc hro
    cases hs : isStore inst
    · exact (hfa.2 hs).1
    · exact (hfa.1 hs).1
  have hval := hMR.valid _ _ _ a n hmr hvalid
  exact ⟨ρm, wm, ops, hat, hops, List.ne_nil_of_mem he0,
    addr_eq_of_oneAcc hn0 (by have := access_le hacc; omega) hval.1 hone hall, ⟨_, hstep⟩,
    hem, halm⟩

end Concurrency.IselVar
