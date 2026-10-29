module

public import FV.Concurrency.ArmAllocMove
public import FV.Concurrency.ArmAllocLoop

@[expose] public section

/-!
# Layer 4b with the LL/SC loops (T2, #311)

The memory scope of `ArmAllocMove.arm_alloc_refines_mv` extended by Cranelift's LL/SC loops
(`atomicRmwLoop`, `atomicCasLoop`), whose per-item obligations are `ArmAllocLoop.rmw_op` and
`cas_op` (failed `stlxr` retries, interference between them, the final iteration's `ldaxr`/`stlxr`
a monitor pair matching the CLIF atomic's read-modify-write event):

* `MemFormL`, `MemScopeL`: every instruction is a memory form of `MemScope` or an LL/SC loop
  (any registers: the checker fixes them to x24–x28, `rmw_op`/`cas_op` read them off `Q`);
* `itemSim_loop`: the per-item obligation of that scope, with moves (`itemSim_of_op_ok`);
* **`arm_alloc_refines_loop`**: every precise Arm run under `OkPriv` from a `Q`-related state
  realizes a run of the allocated code with `Refines` up to its return, trap or undefined
  behaviour, for functions with LL/SC loops (`arm_alloc_refines_mv`'s conclusion).
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot VCodeThread Backend Backend.Proof AllocThread ThreadRefine

/-- The memory forms of `MemScope` and the LL/SC loops. -/
def MemFormL (ctx : FnCtx) (i : MInst) : Prop :=
  MemForm ctx i ∨ (∃ ty op fl ra ro rd r1 r2, i = .atomicRmwLoop ty op fl ra ro rd r1 r2) ∨
    ∃ ty fl ra re rx rd r1, i = .atomicCasLoop ty fl ra re rx rd r1

/-- **The scope of `arm_alloc_refines_loop`**: every instruction is a memory form or an LL/SC
loop (a superset of `MemScope`). -/
def MemScopeL (R : RL) : Prop :=
  ∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst), R.vc.blocks[b]? = some vb → vb.insts[k]? = some i →
    MemFormL R.ctx i

theorem memScopeL_of_memScope {R : RL} (h : MemScope R) : MemScopeL R :=
  fun b vb k i hb hi => .inl (h b vb k i hb hi)

/-- **The per-item obligation of the scope with LL/SC loops, with moves.** -/
theorem itemSim_loop {R : RL} (hR : R.Wf) (hsc : MemScopeL R) :
    ItemSim Policy.arm R.step (OkPriv R) (SrcStep R) (RelQ R) (Done R)
      (fun c => c.measure) (PrivA R) := by
  refine itemSim_of_op_ok hR fun s mon b k allocs its m w evs0 c0 hq hA hs ls t' hr => ?_
  have hs' := hs
  cases hs' with
  | @op _ _ _ _ _ _ vb i ops _ _ hvb hi _ _ _ _ =>
  have uniq : ∀ vb' i', R.vc.blocks[b]? = some vb' → vb'.insts[k]? = some i' → i' = i :=
    fun vb' i' h1 h2 => by rw [hvb] at h1; cases h1; rw [hi] at h2; cases h2; rfl
  rcases hsc b vb k i hvb hi with
    (h | h | ⟨ty, rt, rn, fl, rfl, hfo⟩ | ⟨ty, rt, rn, fl, rfl, hfo⟩) | hl | hl
  · exact noev_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ h) hr
  · exact fence_op hR hq hA hs (fun vb' i' h1 h2 => (uniq vb' i' h1 h2).trans h) hr
  · exact oneEv_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ ldar_form hfo) hr
  · exact oneEv_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ stlr_form hfo) hr
  · exact rmw_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ hl) hr
  · exact cas_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ hl) hr

/-- **Layer 4b with the LL/SC loops** (module doc): every precise Arm run under `OkPriv` from a
`Q`-related state realizes a run of the allocated code (`MTRun`) with `Refines` (equal kinds, the
addresses outside the world private, the atomic updates monitor pairs), up to the allocated code's
return, trap or undefined behaviour (`Done`), for functions whose instructions are event-free,
`fence`, `ldar`, `stlr` or LL/SC loops (`MemScopeL`), whatever their moves. -/
theorem arm_alloc_refines_loop {R : RL} (hR : R.Wf) (hsc : MemScopeL R)
    {s : ArmState} {mon : Mon} {c : MConf CV ArmState} (hq : Q R s c) (hA : AInv R c)
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm R.step (OkPriv R) (s, mon) ls t') :
    ∃ n trS cE ψ, n ≤ ls.length ∧ MTRun R.vc R.rf R.sem ckeep (cEvs R.F R.ctx) c trS cE ∧
      Refines (· = ·) (PrivA R) (MonPair (evTr (ls.take n))) (PrepThread.conv trS)
        (PrepThread.conv (evTr (ls.take n))) ψ ∧ (n = ls.length ∨ Done R cE) := by
  obtain ⟨n, trS, cE, ψ, hn, hs, href, hend⟩ :=
    refines_of_itemSim (itemSim_loop hR hsc) hr ⟨hq, hA⟩
  exact ⟨n, trS, cE, ψ, hn, mtrun_of_srun hs, href, hend⟩

end Concurrency.ArmAllocThread
