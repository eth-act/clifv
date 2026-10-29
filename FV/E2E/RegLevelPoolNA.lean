import FV.E2E.RegLevelPoolN
import FV.E2E.RegLevelCallNA

/-!
# The literal-pool load from `QW` (#565)

`realizes_poolLoadNR` from `QW` (`realizes_poolLoadNAF` with the segment's lines,
`realizes_poolLoadNA`): one straight step.
-/

namespace Backend.Proof

open Backend E2E

/-- **`realizes_poolLoadNA` with the segment's lines** (`RL.FRFree`). -/
theorem realizes_poolLoadNAF {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState}
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    {j : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} {ops : Array Operand} {outs : List CV} {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hform : i.isPoolLoad = true)
    (hops : i.operands = .ok ops) (hsz : allocs.size = ops.size)
    (hsem : R.sem i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      R.SegNA Y s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' n ∧ R.FRFree s n := by
  have hq' : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩) := hq.q
  obtain ⟨sz, d, v, fl, rfl, hsz32⟩ := isPoolLoad_form hform
  refine (fun H => ?_) (realizes_op_coreXSW hR hq hvb hi hops hsz hsem hlen hk
    (exec := fun _ => poolExec)
    (fun _ => (((os_poolLoad hform).at (fun _ => RL.FK_F) s).toI _).v R.gv) (Pre := fun _ => True)
    trivial (SegJ := fun ls1 j s n => R.StraightSeg Y ls1 j s n ∧
      ∀ x t, Line.ins x t ∈ ls1 → x.frLine = false) (fun regs i' hasg _ hex _ => ?_)
    (pool_errW (q_stRel hq') hsem))
  · obtain ⟨n, c'', ls1, hms, hqn, ⟨⟨hg, hin, hn0⟩, hfl⟩, hWn, hS, hT, hpl, hpn⟩ := H
    exact ⟨n, c'', hms, ⟨hqn, hg, RL.segLen_straight_of hR hS hWn hT hpl hpn hin hn0⟩,
      RL.frFree_straight hR hT hpl hfl hq.pc hin hn0⟩
  obtain ⟨_, s0, s1, hex⟩ := hex
  obtain ⟨n, rfl, hl, hpl⟩ := pool_lines (R := R) hasg ⟨s0, s1, hex⟩
  refine ⟨_, hl, hpl, fun _ h => MInst.noConfusion h, fun _ h => MInst.noConfusion h,
    fun j T s m w s' hd hst hpc _ hex => ?_⟩
  obtain ⟨hj, hs, hpc', hg, hrd⟩ := RL.pool_run hR hsz32 hd hst hpc hex
  refine ⟨1, by simpa [iterN] using hs, hpc', ⟨fun i hi => ?_, RL.Inside.one, by simp⟩,
    fun x t hx => ?_⟩
  · obtain rfl : i = 0 := by omega
    exact ⟨⟨hg, RL.noCallAt_of_noCall hR hj hpc
      ⟨fun _ h => Insn.noConfusion h, fun _ h => Insn.noConfusion h⟩⟩, hrd Y⟩
  · simp only [List.mem_singleton, Line.ins.injEq] at hx
    obtain ⟨rfl, -⟩ := hx
    rfl

/-- **The literal-pool load on the machine, at a witness** (`realizes_poolLoadNR`). -/
theorem realizes_poolLoadNA {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState}
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    {j : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} {ops : Array Operand} {outs : List CV} {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hform : i.isPoolLoad = true)
    (hops : i.operands = .ok ops) (hsz : allocs.size = ops.size)
    (hsem : R.sem i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      R.SegNA Y s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' n :=
  let ⟨n, c'', h1, h2, _⟩ := realizes_poolLoadNAF (Y := Y) hR hq hvb hi hform hops hsz hsem hlen hk
  ⟨n, c'', h1, h2⟩

end Backend.Proof
