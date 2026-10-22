import FV.Concurrency.IselStep
import FV.Concurrency.IselCheck
import FV.Concurrency.VCodeEvents

/-!
# A thread walking a statement's segment; the match after patching (T2h, #311, layer 2e)

* `vtrun_walk`: a VCode thread run (`PrepThread.VTRun` under `csem`/`cEvs`) through instructions
  of block `b` without memory kinds and other than `rets` steps without events and falls through,
  keeping the memory, until it reaches the end of the stretch, ends, or halts (an explicit trap);
* `vtstep_next`: a step of a memory instruction (a straight-line form or an LL/SC loop) falls
  through;
* **`mr_patch`** (the match after patching both memories with the read bytes): a read event at
  a valid CLIF access, its bytes stored in the CLIF memory (`writeBits`, little-endian) and in
  the VCode world (`VCodeThread.patch`), keeps the memory relation (`MemRelOk.store`);
  `mr_own`: storing the world's own bytes into the CLIF memory keeps it too (the world is
  unchanged).
-/

namespace Concurrency.IselSeg

open Arm ArmFoot ArmThread Backend Backend.Proof Backend.Proof.Driver VCodeThread PrepThread
  SegRun IselStep IselCheck Code

/-! ## Walking a stretch without events -/

section walk
variable {vc : VCode} {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}

theorem vtrun_halt {c : VConf CV ArmState} {tr : List (List Ev)} {w : ArmState}
    (h : VTRun vc (csem F ctx X) (cEvs F ctx) (.halt w) tr c) : tr = [] := by
  cases h with
  | nil => rfl
  | cons hs _ => cases hs

/-- **A thread walks a stretch of block `b` without memory kinds** (module doc): it reaches the
end of the stretch, its memory unchanged, with steps without events — or its run ends inside the
stretch (trace exhausted, or halted) with steps without events. -/
theorem vtrun_walk {b : Nat} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) :
    ∀ (m : Nat) {k : Nat} {ρ : Nat → CV} {w : ArmState} {tr : List (List Ev)}
      {cT : VConf CV ArmState},
    (∀ i < m, ∃ ins, vb.insts[k + i]? = some ins ∧ akinds ins = [] ∧ isRetsB ins = false) →
    k + m < vb.insts.size →
    VTRun vc (csem F ctx X) (cEvs F ctx) (.run ⟨b, k, ρ, w⟩) tr cT →
    (∃ ρ' w' pre rest, tr = pre ++ rest ∧ pre.length = m ∧ (∀ e ∈ pre, e = []) ∧
      VTRun vc (csem F ctx X) (cEvs F ctx) (.run ⟨b, k, ρ, w⟩) pre (.run ⟨b, k + m, ρ', w'⟩) ∧
      VTRun vc (csem F ctx X) (cEvs F ctx) (.run ⟨b, k + m, ρ', w'⟩) rest cT ∧ w'.mem = w.mem) ∨
    (tr.length ≤ m ∧ ∀ e ∈ tr, e = [])
  | 0, k, ρ, w, tr, cT, _, _, hr => by
    refine .inl ⟨ρ, w, [], tr, rfl, rfl, ?_, VTRun.nil, hr, rfl⟩
    intro e h; cases h
  | m + 1, k, ρ, w, tr, cT, hins, hlt, hr => by
    cases hr with
    | nil => exact .inr ⟨by simp, fun _ h => nomatch h⟩
    | @cons _ c' _ evs tr' hs hr' =>
      obtain ⟨ins, hins0, hak, hret⟩ := hins 0 (by omega)
      simp only [Nat.add_zero] at hins0
      have hev : evs = [] := by
        cases hs with
        | mk hb1 hi1 hops1 he hf1 hst1 =>
          rw [hvb] at hb1; cases hb1
          rw [hins0] at hi1; cases hi1
          rw [he]; exact VCodeEvents.cEvs_nil hak _ _
      subst hev
      obtain ⟨vb', i1, ops1, hb1, hi1, hops1, hf1, hst1⟩ := vtstep_foot hs
      rw [hvb] at hb1; cases hb1
      rw [hins0] at hi1; cases hi1
      rw [SegRun.patch_nil] at hf1 hst1
      cases hst1 with
      | step hb2 hi2 hops2 hsem hlen hnx =>
        rw [hvb] at hb2; cases hb2
        rw [hins0] at hi2; cases hi2
        rw [hops1] at hops2; cases hops2
        have hmem := ifoot_nil_mem hf1 hsem
        cases hnx with
        | next hk1 =>
          have hins' : ∀ i < m, ∃ ins, vb.insts[k + 1 + i]? = some ins ∧ akinds ins = [] ∧
              isRetsB ins = false := fun i hi => by
            obtain ⟨x, hx, h1, h2⟩ := hins (i + 1) (by omega)
            exact ⟨x, by rw [show k + 1 + i = k + (i + 1) by omega]; exact hx, h1, h2⟩
          rcases vtrun_walk hvb m hins' (by omega) hr' with
            ⟨ρ', w', pre, rest, htr, hl, he', h1, h2, hm⟩ | ⟨hl, he'⟩
          · refine .inl ⟨ρ', w', [] :: pre, rest, by rw [htr]; rfl, by simp [hl], ?_,
              by rw [show k + (m + 1) = k + 1 + m by omega]; exact .cons hs h1,
              by rw [show k + (m + 1) = k + 1 + m by omega]; exact h2,
              hm.trans hmem⟩
            intro e he''
            rcases List.mem_cons.mp he'' with h | h
            · exact h
            · exact he' e h
          · refine .inr ⟨by simp; omega, ?_⟩
            intro e he''
            rcases List.mem_cons.mp he'' with h | h
            · exact h
            · exact he' e h
        | goto hk1 _ _ => omega
        | ret hr2 => subst hr2; simp [isRetsB] at hret
        | halt =>
          have := vtrun_halt hr'
          subst this
          exact .inr ⟨by simp, by simp⟩

/-- **A memory instruction falls through**: a thread step of a straight-line form or an LL/SC
loop at instruction `k` (not the block's last) reaches instruction `k + 1`. -/
theorem vtstep_next {b k : Nat} {ρ : Nat → CV} {w : ArmState} {vb : VBlock} {i : MInst}
    (hvb : vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    (hform : i.isCtl = false ∨ (∃ ty op fl a x d r1 r2, i = .atomicRmwLoop ty op fl a x d r1 r2) ∨
      (∃ ty fl a e x d r, i = .atomicCasLoop ty fl a e x d r))
    {evs : List Ev} {c' : VConf CV ArmState}
    (h : VTStep vc (csem F ctx X) (cEvs F ctx) (.run ⟨b, k, ρ, w⟩) evs c') :
    ∃ ρ' w', c' = .run ⟨b, k + 1, ρ', w'⟩ ∧ k + 1 < vb.insts.size := by
  obtain ⟨vb', i', ops, hb', hi', hops, -, hst⟩ := vtstep_foot h
  rw [hvb] at hb'; cases hb'
  rw [hi] at hi'; cases hi'
  cases hst with
  | step hb2 hi2 hops2 hsem hlen hnx =>
    rw [hvb] at hb2; cases hb2
    rw [hi] at hi2; cases hi2
    rw [hops] at hops2; cases hops2
    have hn : ∀ {o w2 ctl}, csem F ctx X i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg))
        (patch evs w) = some (o, w2, ctl) → ctl = .next := by
      intro o w2 ctl hs
      rcases hform with hc | ⟨ty, op, fl, a, x, d, r1, r2, rfl⟩ | ⟨ty, fl, a, e, x, d, r, rfl⟩
      · exact csem_ctl hc hs
      · simp only [csem] at hs
        split at hs
        · split at hs
          · exact loopSem_next hs
          · split at hs
            · simp only [Option.some.injEq, Prod.mk.injEq] at hs; exact hs.2.2.symm
            · cases hs
        · cases hs
      · simp only [csem] at hs
        split at hs
        · split at hs
          · split at hs
            · split at hs
              · simp only [Option.some.injEq, Prod.mk.injEq] at hs; exact hs.2.2.symm
              · exact loopSem_next hs
            · cases hs
          · split at hs
            · simp only [Option.some.injEq, Prod.mk.injEq] at hs; exact hs.2.2.symm
            · cases hs
        · cases hs
    have := hn hsem
    subst this
    cases hnx with
    | next hk1 => exact ⟨_, _, rfl, hk1⟩

/-- **A thread follows a forward run through instructions without memory kinds**: its first
`n` steps have no events and reach the run's end, or its run ends earlier, without events. -/
theorem vtrun_follow :
    ∀ {n : Nat} {c0 cn : VConf CV ArmState},
      StarNP (VStep vc (csem F ctx X)) (NoMemAt vc) n c0 cn →
      ∀ {tr : List (List Ev)} {cT : VConf CV ArmState},
      VTRun vc (csem F ctx X) (cEvs F ctx) c0 tr cT →
      (∃ pre rest, tr = pre ++ rest ∧ pre.length = n ∧ (∀ e ∈ pre, e = []) ∧
        VTRun vc (csem F ctx X) (cEvs F ctx) c0 pre cn ∧
        VTRun vc (csem F ctx X) (cEvs F ctx) cn rest cT) ∨
      (tr.length < n ∧ ∀ e ∈ tr, e = [])
  | _, _, _, .refl _, tr, cT, hr => by
    refine .inl ⟨[], tr, rfl, rfl, ?_, VTRun.nil, hr⟩
    intro e h; cases h
  | _, _, _, .step hP hst t, tr, cT, hr => by
    cases hr with
    | nil => exact .inr ⟨by simp, fun _ h => nomatch h⟩
    | @cons _ c'' _ evs tr' hs hr' =>
      have hs0 := hs
      cases hs0 with
      | mk hb hi hops he hf hst' =>
        rename_i b k ρ w vb i ops
        have hev : evs = [] := by
          rw [he]; exact VCodeEvents.cEvs_nil (hP b k ρ w rfl vb i hb hi) _ _
        subst hev
        rw [SegRun.patch_nil] at hst'
        have e := vstep_det hst' hst
        subst e
        rcases vtrun_follow t hr' with ⟨pre, rest, htr, hl, hpe, h1, h2⟩ | ⟨hl, hpe⟩
        · refine .inl ⟨[] :: pre, rest, by rw [htr]; rfl, by simp [hl], ?_, .cons hs h1, h2⟩
          intro x hx
          rcases List.mem_cons.mp hx with h | h
          · exact h
          · exact hpe x h
        · refine .inr ⟨by simp; omega, ?_⟩
          intro x hx
          rcases List.mem_cons.mp hx with h | h
          · exact h
          · exact hpe x h

end walk

/-! ## The memory relation after patching -/

/-- Patching with one read event is the world with its bytes stored. -/
theorem patch_read {e : Ev} (hR : e.k.dir = .R) (w : ArmState) :
    patch [e] w = write_mem_bytes e.n e.addr e.val w := by
  simp [patch, applyR, hR, write_mem_bytes_eq]

/-- **The match after patching both memories with a read event's bytes** (module doc). -/
theorem mr_patch {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {f : Clif.Function} {MR : MemRelT} (hMR : MemRelOk F sb syms f MR)
    {sl : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {w : ArmState} (hmr : MR sl cm w) {a : Nat}
    {e : Ev} (hR : e.k.dir = .R) (ha : e.addr = BitVec.ofNat 64 a) (hv : cm.valid a e.n = true) :
    MR sl (cm.writeBits false a e.n e.val) (patch [e] w) := by
  rw [patch_read hR, ha]
  exact hMR.store sl cm w a e.n e.val hmr hv

/-- Storing the world's own bytes into the CLIF memory keeps the memory relation. -/
theorem mr_own {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {f : Clif.Function} {MR : MemRelT} (hMR : MemRelOk F sb syms f MR)
    {sl : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {w : ArmState} (hmr : MR sl cm w) {a n : Nat}
    (hv : cm.valid a n = true) :
    MR sl (cm.writeBits false a n (readM n (BitVec.ofNat 64 a) w.mem)) w := by
  have h := hMR.store sl cm w a n (readM n (BitVec.ofNat 64 a) w.mem) hmr hv
  rwa [write_mem_bytes_eq, writeM_readM, setMem_self] at h

end Concurrency.IselSeg
