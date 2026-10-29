import FV.E2E.RegLevelMemTrap
import FV.E2E.RegLevelGotoW
import FV.E2E.RegLevelWrites

/-!
# The trapping loops and the `trapIf` trap on the machine with their writes (A3, #412, slice F8b)

`RegLevelMemTrap`'s `trap_trapIf_line` and `realizes_haltLoop` with `RL.GoodXW` (`GoodX` and the
writes `RL.WritesAt` of the unhooked instruction at the pc, which avoids the kept addresses
`R.G`): the branch to the trap label writes no memory.
-/

namespace Backend.Proof

open Backend E2E

/-- **A realisation of `sem` is one of `haltLoop c A sem`**: off the halting loops they agree;
at a halting loop the allocated code halts (the machine is unchanged). -/
theorem realizes_haltLoopW {R : RL} {sem₀ : Sem} {c : Clif.TrapCode} {A : BitVec 64 → Nat → Prop}
    (hreal : Realizes R.vc R.rf sem₀ ckeep R.step (QA R) R.GoodXW) :
    Realizes R.vc R.rf (haltLoop c A sem₀) ckeep R.step (QA R)
      R.GoodXW := by
  intro s c0 c' hq hm
  cases hm with
  | move =>
    obtain ⟨n, c'', hm'', hq'', ht⟩ := hreal s _ _ hq .move
    exact ⟨n, c'', mstep_congr hm'' (fun _ _ _ _ _ _ _ _ _ hc => by cases hc), hq'', ht⟩
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsem hlen hho hcl hn =>
    have hstep : MStep R.vc (haltLoop c A sem₀) ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c' :=
      MStep.op hvb hi hops hsz hsem hlen hho hcl hn
    by_cases hh : HaltsAt c A i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2))
    · rw [haltLoop_of hh] at hsem
      simp only [Option.some.injEq, Prod.mk.injEq] at hsem
      obtain ⟨-, -, rfl⟩ := hsem
      cases hn with
      | halt => exact ⟨0, _, hstep, .inl ⟨trivial, trivial⟩, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    · rw [haltLoop_of_not hh] at hsem
      obtain ⟨n, c'', hm'', hq'', ht⟩ := hreal s _ _ hq (MStep.op hvb hi hops hsz hsem hlen hho hcl hn)
      refine ⟨n, c'', mstep_congr hm'' fun b' k' allocs' its' m' w'' vb' i' ops' hc hvb' hi' hops' => ?_,
        hq'', ht⟩
      cases hc
      rw [hvb] at hvb'; cases hvb'
      rw [hi] at hi'; cases hi'
      rw [hops] at hops'; cases hops'
      exact congrFun (haltLoop_of_not hh).symm w


/-- `trap_trapIf` with the trap site's `udf` line. -/
theorem trap_trapIf_lineW {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {kk : CondBrKind}
    {code : Clif.TrapCode} (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.trapIf kk code)) {ops : Array Operand}
    (hops : (MInst.trapIf kk code).operands = .ok ops)
    (hholds : kk.holds (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = true) :
    ∃ n, TrapAt R.fb R.base code (iterN R.step n s) ∧ UdfLine R.fa R.base (iterN R.step n s) ∧
      ∀ i < n, R.GoodXW (iterN R.step i s) := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops', rfl, hit, hsplit,
    hasg, hc1', hops', hstat, hchk', hc2, h1, h2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  rw [hops] at hops'; cases hops'
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
  obtain ⟨rfl, hpsm⟩ := hl1
  -- the branch (relaxed or not) to the trap label is taken
  have hZ : ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  have hdrop' : R.L.drop j0 = relaxLine R.far (.ins (k'.insn (.trap ps1.traps.size)) none) ++
      (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T) := by
    rw [hdrop, List.singleton_append, ftList_kind_trap k' ps1.traps.size _ hZ, relaxLines_cons,
      List.append_assoc]
  have hform : (∃ c, k'.insn (.trap ps1.traps.size) = .bcond c (.trap ps1.traps.size)) ∨
      (∃ nz w r, k'.insn (.trap ps1.traps.size) = .cbz nz w r (.trap ps1.traps.size)) ∨
      (∃ nz r bit, k'.insn (.trap ps1.traps.size) = .tbz nz r bit (.trap ps1.traps.size)) := by
    cases k' <;> simp [CondBrKind.insn]
  obtain ⟨nst, jl, hnst, hjt, -, -, -, hgx⟩ := reach_rcbXW hR hdrop' hform (by simp) true
    (fun env a ha => by rw [kind_brCond hst hkr _ ha, hholds])
    (fun hct env a ha => by rw [kind_brCond_inv hst hkr _ _ hct ha, hholds])
    (by rw [hst.prog]) hpc hst.err hst.sp
  have hjl := hjt rfl
  -- the trap section entry of this trap
  have hpre : psm.traps.toList <+: R.psF.traps.toList :=
    (codeLinesE_traps h2).trans htr
  have hn : R.psF.traps.toList[ps1.traps.size]? = some (.trap ps1.traps.size, code) := by
    obtain ⟨t, ht⟩ := hpre
    rw [← ht, ← hpsm]
    simp
  obtain ⟨body, psF', hb, hL, -⟩ := emit_block hR.emit
  rw [relaxLines_append, relaxLines_trapLines, List.append_assoc,
    show emitFar ⟨R.fa.k, R.af.slotBase⟩ R.af = R.far from rfl] at hL
  obtain ⟨body', hb'⟩ := hR.psF
  have hk : R.ctx = ⟨R.fa.k, R.af.slotBase⟩ := rfl
  rw [hk, hb] at hb'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hb'
  obtain ⟨-, rfl⟩ := hb'
  obtain ⟨hlab, hudf⟩ := trapLines_get_append _ _ _ _ hn
  have hlab' : R.L[(relaxLines R.far (ftList body)).length + 2 * ps1.traps.size]? = some (.label (.trap ps1.traps.size)) := by
    simp only [RL.L, hL]; rw [List.getElem?_append_right (by omega)]; simpa using hlab
  have hudf' : R.L[(relaxLines R.far (ftList body)).length + 2 * ps1.traps.size + 1]? =
      some (.ins (.udf 0xc11f) (some code)) := by
    simp only [RL.L, hL]; rw [List.getElem?_append_right (by omega)]
    simpa [Nat.add_assoc] using hudf
  -- the branch reaches the label's offset, which is the trap site's
  have hoff : R.pcOf jl = R.pcOf ((relaxLines R.far (ftList body)).length + 2 * ps1.traps.size + 1) := by
    have e1 := labelOffsets_label hR.lm hjl
    have e2 := labelOffsets_label hR.lm hlab'
    simp only [RL.pcOf]
    rw [lineOffset_succ _ _ _ hlab']
    simp only [RL.L] at e1 e2 ⊢
    rw [e1] at e2
    simp only [Option.some.injEq] at e2
    rw [e2]; simp [Line.size]
  have hpcF : Arm.r .PC (iterN R.step nst s) =
      R.pcOf ((relaxLines R.far (ftList body)).length + 2 * ps1.traps.size + 1) := by
    rw [hnst, Arm.r_of_w_same, hoff]
  have herrF : Arm.r .ERR (iterN R.step nst s) = .None := by
    rw [hnst, Arm.r_of_w_different (by simp)]; exact hst.err
  exact ⟨nst, trapAt_line hR hudf' hpcF herrF, ⟨_, _, hudf', hpcF⟩, hgx⟩

end Backend.Proof
