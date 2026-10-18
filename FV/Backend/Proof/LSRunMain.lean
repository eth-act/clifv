import FV.Backend.Proof.LSRunInst
import FV.Backend.Proof.LSRunEdge
import FV.Backend.Proof.LSRunArgs
import FV.Backend.Proof.LSRunEntry
import FV.Backend.Proof.SpillStep4Edge

/-!
# The checker accepts the Lean allocator's validated plans (V4b-3, #275): the blocks

`verify_block`: every block's items run from its in-state (`entry_runs`, then each instruction
`inst_runs`/`good_succ`, the last one `last_edges` or, with branch arguments, `args_runs`) and
feed every successor's in-state, so the block passes `verifyBlock`. `allocChecked`: with the
entry block's in-state `EntryOk` (`inState_entryOk`), the allocation is `AllocChecked`.
-/

namespace Backend.Proof.LS

open Backend Backend.LinearScan Backend.Proof Backend.Proof.Spill
open Backend.LinearScan.Ctx (Parts blockItems)

/-- Without branch arguments, the argument copies are empty. -/
private theorem argMoves_nil {c : LinearScan.Ctx} {b g : Nat} {args : List RItem}
    (hn : c.fn.args b = []) (h : c.argMoves b g = .ok args) : args = [] := by
  unfold LinearScan.Ctx.argMoves at h
  rw [hn] at h
  split at h
  · simp only [List.zip_nil_left, List.filterMap_nil] at h
    simp only [seqMoves, cleanMoves, List.filter_nil, List.eraseDups_nil, List.length_nil,
      seqGo, pure, Except.pure, Except.ok.injEq] at h
    exact h.symm
  · simp only [List.isEmpty_nil, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
    exact h.symm

section
variable {vc : VCode} {c : LinearScan.Ctx} {rf : RFunc} {D : Nat → Nat → Bool}
  (H : Hyps vc c rf D)
include H

/-- **The instructions of a block** from instruction `k` on (`n + 1` of them). -/
private theorem body_runs {b : Nat} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) {p : Parts}
    (hp : c.blockParts b = .ok p) :
    ∀ (n k : Nat) (a : AState), k + (n + 1) = vb.insts.size →
    Good c rf (availAt vb.insts (availStart vc c.fn.succs c.fn.preds D b) k)
      (pos (c.fn.start.getD b 0 + k) 0) a →
    Runs (ctxOf vc c rf) vb k (itemsFrom vb p (restoresOf rf.saved) k) a fun k' a' =>
      k' = vb.insts.size ∧ ∀ s ∈ ((ctxOf vc c rf).succs[b]?.getD #[]).toList,
        ∃ e, (ctxOf vc c rf).edge b s a' = .ok e ∧ (inState vc c rf D s).le e = true := by
  have hPF := partsFacts hp
  have hlen : p.insts.length = vb.insts.size := by
    rw [hPF.len, H.fn.startSucc hvb]; omega
  intro n
  induction n with
  | zero =>
    intro k a hk hg
    obtain ⟨i, hi⟩ : ∃ i, vb.insts[k]? = some i :=
      ⟨_, Array.getElem?_eq_getElem (by omega)⟩
    obtain ⟨-, -, os, hos, -⟩ := H.fn.inst b vb k i hvb hi
    obtain ⟨⟨args, io⟩, hpk⟩ : ∃ x, p.insts[k]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [itemsFrom_succ hpk, itemsFrom_end (by omega), List.append_nil]
    have hlast : c.fn.start.getD b 0 + k + 1 = c.fn.start.getD (b + 1) 0 := by
      rw [H.fn.startSucc hvb]; omega
    by_cases hba : vb.branchArgs = #[]
    · have hargs : args = [] := argMoves_nil (by rw [H.fn.args hvb, hba]; rfl)
        ((hPF.inst k args io hpk).2.1 hlast)
      subst hargs
      rw [List.nil_append]
      exact (inst_runs H hvb hp hpk hi hos rfl hg).mono fun k' a' ⟨e1, hpost⟩ =>
        ⟨by omega, last_edges H hvb (by omega) hba hi hos rfl hpost⟩
    · exact (args_runs H hvb hp hpk (by omega) hba rfl hg).mono fun k' a' ⟨e1, he⟩ =>
        ⟨by omega, he⟩
  | succ n ih =>
    intro k a hk hg
    obtain ⟨i, hi⟩ : ∃ i, vb.insts[k]? = some i :=
      ⟨_, Array.getElem?_eq_getElem (by omega)⟩
    obtain ⟨-, -, os, hos, -⟩ := H.fn.inst b vb k i hvb hi
    obtain ⟨⟨args, io⟩, hpk⟩ : ∃ x, p.insts[k]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hnl : c.fn.start.getD b 0 + k + 1 ≠ c.fn.start.getD (b + 1) 0 := by
      rw [H.fn.startSucc hvb]; omega
    have hargs : args = [] := (hPF.inst k args io hpk).2.2 hnl
    subst hargs
    rw [itemsFrom_succ hpk, List.nil_append]
    refine Runs.append (inst_runs H hvb hp hpk hi hos rfl hg) fun k' a' ⟨e1, hpost⟩ => ?_
    subst e1
    refine ih (k + 1) a' (by omega) ?_
    rw [availAt_succ hi, ← Nat.add_assoc]
    exact good_succ H hvb (by omega) hi hos hpost

/-- **Every block passes `verifyBlock`** with the in-states `insOf`. -/
theorem verify_block {b : Nat} (hb : b < vc.blocks.size) :
    (ctxOf vc c rf).verifyBlock (insOf vc c rf D) b = .ok () := by
  have hvb : vc.blocks[b]? = some vc.blocks[b] := Array.getElem?_eq_getElem hb
  generalize vc.blocks[b] = vb at hvb
  obtain ⟨p, hp, hblk⟩ := H.build.block b vb hvb
  obtain ⟨T, hT, -⟩ := cfg_last H.fn.cfg hvb
  obtain ⟨hpos, -⟩ := back_get hT
  have hrun : Runs (ctxOf vc c rf) vb 0 (((if b = 0 then savesOf rf.saved else []) ++ p.entry) ++
      itemsFrom vb p (restoresOf rf.saved) 0) (inState vc c rf D b) fun k a =>
        k = vb.insts.size ∧ ∀ s ∈ ((ctxOf vc c rf).succs[b]?.getD #[]).toList,
          ∃ e, (ctxOf vc c rf).edge b s a = .ok e ∧ (inState vc c rf D s).le e = true :=
    Runs.append (entry_runs H hvb hp) fun k a ⟨hk, hg⟩ => by
      subst hk
      exact body_runs H hvb hp (vb.insts.size - 1) 0 a (by omega) hg
  obtain ⟨o, ho, hfin⟩ := Runs.run hrun
  refine verifyBlock_of (out := o) (insOf_get hb) ?_ fun s hs => ?_
  · unfold CheckCtx.runBlock
    rw [show (ctxOf vc c rf).vc = vc from rfl, show (ctxOf vc c rf).rf = rf from rfl, hvb, hblk]
    dsimp only
    rw [blockItems_eq, ← List.append_assoc]
    exact ho
  · obtain ⟨e, he, hle⟩ := hfin s hs
    have hs' : s < vc.blocks.size := by
      obtain ⟨ss, hss⟩ := cfg_succs_some H.fn.cfg hb
      rw [show (ctxOf vc c rf).succs = c.fn.succs from rfl, hss, Option.getD_some] at hs
      exact cfg_succ_lt H.fn.cfg hss hs
    exact ⟨e, _, he, insOf_get hs', hle⟩

/-- **The allocation is `AllocChecked`.** -/
theorem allocChecked : AllocChecked vc rf := by
  have hE := H.loc.2.2 _ _ H.fn.cfg
  exact ⟨ctxOf vc c rf, insOf vc c rf D, inState vc c rf D 0,
    ⟨rfl, rfl, ⟨c.fn.preds, H.fn.cfg⟩, H.build.size, hE.entry.1,
      insOf_get (Nat.pos_of_ne_zero hE.entry.1), fun b hb => verify_block H hb⟩,
    inState_entryOk⟩

end

end Backend.Proof.LS
