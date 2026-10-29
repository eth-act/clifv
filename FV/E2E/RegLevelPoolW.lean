import FV.E2E.RegLevelPool
import FV.E2E.RegLevelCallW

/-!
# The literal-pool load with its writes (#565)

`realizes_poolLoad` with `RL.GoodXW` (`realizes_poolLoadW`): the `ldr (literal)` stores nothing.
-/

namespace Backend.Proof

open Backend E2E

/-- **The literal-pool load on the machine** (`realizes_poolLoad`) with `GoodXW`. -/
theorem realizes_poolLoadW {R : RL} (hR : R.Wf) {s : Arm.ArmState}
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} {ops : Array Operand} {outs : List CV} {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hform : i.isPoolLoad = true)
    (hops : i.operands = .ok ops) (hsz : allocs.size = ops.size)
    (hsem : R.sem i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.GoodXW (iterN R.step i s) := by
  obtain ⟨sz, d, v, fl, rfl, hsz32⟩ := isPoolLoad_form hform
  refine realizes_op_coreXW hR hq hvb hi hops hsz hsem hlen hk (exec := fun _ => poolExec)
    (fun _ => (((os_poolLoad hform).at (fun _ => RL.FK_F) s).toI _).v R.gv) (Pre := fun _ => True)
    trivial (fun regs i' hasg _ hex _ => ?_) (pool_errW (q_stRel hq) hsem)
  obtain ⟨_, s0, s1, hex⟩ := hex
  obtain ⟨n, rfl, hl, hpl⟩ := pool_lines (R := R) hasg ⟨s0, s1, hex⟩
  refine ⟨_, hl, hpl, fun _ h => MInst.noConfusion h, fun _ h => MInst.noConfusion h,
    fun j T s m w s' hd hst hpc _ hex => ?_⟩
  obtain ⟨hj, hs, hpc', hg, -⟩ := RL.pool_run hR hsz32 hd hst hpc hex
  refine ⟨1, by simpa [iterN] using hs, hpc', fun i hi => ?_⟩
  obtain rfl : i = 0 := by omega
  exact ⟨hg, RL.writesAt_noStore hR hj hpc rfl⟩

end Backend.Proof
