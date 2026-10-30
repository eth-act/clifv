import FV.E2E.RegLevelNext
import FV.E2E.RegLevelNoCall
import FV.E2E.RegLevelGotoNR

/-!
# `trapIf` that falls through with no call state (SEM1 #537, step 2k)

`realizes_trapIf_next` with `RL.GoodXNR` (docs/plans/uninit.md §5.5).
-/

namespace Backend.Proof

open Backend E2E

/-- **`trapIf` whose condition does not hold**: one conditional branch (to the trap section),
not taken. -/
theorem realizes_trapIf_nextNR {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState}
    {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {c' : MConf CV Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {kk : CondBrKind}
    {code : Clif.TrapCode} (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.trapIf kk code))
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c')
    (hnh : ∀ w', c' ≠ .halt w') :
    ∃ n, Q R (iterN R.step n s) c' ∧ ∀ i < n, R.GoodXNY Y (iterN R.step i s) := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, rfl, hit, hsplit,
    hasg, hc1', hops, hstat, hchk', hc2, h1, h2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  have hkk : ∀ r sz, kk = .zero r sz ∨ kk = .notZero r sz → r.isVregInt = true := by
    intro r sz hr
    have := ctlCheck_inst hck hvb hi
    rcases hr with rfl | rfl <;> simpa [ctlInstOk] using this
  obtain ⟨k', rfl, hkr⟩ := kind_alloc hkk (mk := fun k => MInst.trapIf k code) rfl
    (fun f => rfl) (fun f => rfl) hops hstat hasg m
  obtain rfl : c1 = [.inst (.trapIf k' code)] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  have hl1 := codeLinesE_single h1
  simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
  obtain ⟨rfl, -⟩ := hl1
  cases h with
  | @op b k allocs its m w vb' i ops' outs outs' w' ctl m2 c' hvb' hi' hops' hsz hsem hlen hho hcl hn =>
  rw [hvb] at hvb'; cases hvb'
  rw [hi] at hi'; cases hi'
  rw [hops] at hops'; cases hops'
  obtain rfl := hho.2.1 rfl
  simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
  obtain ⟨rfl, rfl, hctl⟩ := hsem
  cases hn with
  | halt => exact absurd rfl (hnh _)
  | ret h => cases h
  | goto _ _ _ => split at hctl <;> cases hctl
  | next hk =>
  have hnot : kk.holds (((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isUse)).map (m ·.2)) w = false := by
    split at hctl
    · cases hctl
    · rename_i hh
      simpa using hh
  rw [store_nodefs rfl hcl]
  -- the branch to the trap label is not taken
  have hZ : ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  have hft := ftList_kind_trap k' ps1.traps.size (ls2 ++ nxtOf R.af b) hZ
  have hdrop' : R.L.drop j0 = relaxLine R.far (.ins (k'.insn (.trap ps1.traps.size)) none) ++
      (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T) := by
    rw [hdrop, List.singleton_append, hft, relaxLines_cons, List.append_assoc]
  have hform : (∃ c, k'.insn (.trap ps1.traps.size) = .bcond c (.trap ps1.traps.size)) ∨
      (∃ nz w r, k'.insn (.trap ps1.traps.size) = .cbz nz w r (.trap ps1.traps.size)) ∨
      (∃ nz r bit, k'.insn (.trap ps1.traps.size) = .tbz nz r bit (.trap ps1.traps.size)) := by
    cases k' <;> simp [CondBrKind.insn]
  obtain ⟨n, jl, hn, -, hjf, -, -, hg⟩ := reach_rcbXNR (Y := Y) hR hdrop' hform (by simp) false
    (fun env a ha => by rw [kind_brCond hst hkr _ ha, hnot])
    (fun hct env a ha => by rw [kind_brCond_inv hst hkr _ _ hct ha, hnot])
    (by rw [hst.prog]) hpc hst.err hst.sp
  refine ⟨n, ?_, hg⟩
  rw [hn]
  exact q_next hvb hit hsplit hchk' hc2 h2 htr hdrop (by rw [List.singleton_append, hft]; rfl)
    (by rw [Arm.r_of_w_same, hjf rfl]; simp [relaxLines]) (hst.pc _)

end Backend.Proof
