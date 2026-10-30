import FV.E2E.RegLevelGoodXNR
import FV.E2E.RegLevelCallNA
import FV.E2E.RegLevelTls

/-!
# `ElfTlsGetAddr`, at a witness (SEM1 #537, item (3), route (a))

`realizes_tlsNR` from `QW`: two steps inside the sequence's lines, to the next item at the
straight witness.
-/

namespace Backend.Proof

open Backend E2E

/-- **`realizes_tlsNA` with the segment's lines** (`RL.FRFree`). -/
theorem realizes_tlsNAF {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} (hT : TlsOk R.F R.K R.X R.H)
    {s : Arm.ArmState}
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    {j : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {n : String} {d t : Nat} {ops : Array Operand} {outs : List CV}
    {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.elfTlsGetAddr n (.vreg d .int) (.vreg t .int)))
    (hops : (MInst.elfTlsGetAddr n (.vreg d .int) (.vreg t .int)).operands = .ok ops)
    (hsz : allocs.size = ops.size)
    (hsem : R.sem (.elfTlsGetAddr n (.vreg d .int) (.vreg t .int))
      (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = some (outs, w', .next))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      R.SegNA Y s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' n ∧ R.FRFree s n := by
  have hq' : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩) := hq.q
  have hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program := by
    have herr : Arm.r .ERR w = .None := by
      have hst := q_stRel hq'
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    have hsem := R.sem_csem hsem
    simp only [csem, Option.some.injEq, Prod.mk.injEq] at hsem
    obtain ⟨-, rfl, -⟩ := hsem
    exact ⟨by rw [r_write_pstate_other (fun fl => by simp)]; exact herr,
      by simp [Arm.write_pstate, Arm.w_program]⟩
  refine (fun H => ?_) (realizes_op_coreXSW hR hq hvb hi hops hsz hsem hlen hk
    (exec := fun _ => tlsExec R.H)
    (fun _ => ((RL.callAt hR (os_tls hT n d t) (q_stRel hq').sp).toI _).v R.gv)
    (Pre := fun _ => True) trivial (SegJ := fun ls1 j s n => R.StraightSeg Y ls1 j s n ∧
      ∀ x t, Line.ins x t ∈ ls1 → x.frLine = false) (fun regs i' _ _ hex _ => ?_) hW')
  · obtain ⟨n, c'', ls1, hms, hqn, ⟨⟨hg, hin, hn0⟩, hfl⟩, hWn, hS, hT', hpl, hpn⟩ := H
    exact ⟨n, c'', hms, ⟨hqn, hg, RL.segLen_straight_of hR hS hWn hT' hpl hpn hin hn0⟩,
      RL.frFree_straight hR hT' hpl hfl hq.pc hin hn0⟩
  obtain ⟨_, s0, _, hex⟩ := hex
  cases i' with
  | elfTlsGetAddr n' rd tmp =>
    have hc : rd = .x 0 ∧ tmp ≠ .x 0 := by
      simp only [tlsExec] at hex
      split at hex
      · assumption
      · cases hex
    obtain ⟨rfl, htmp⟩ := hc
    have hl : ∀ ps, (MInst.elfTlsGetAddr n' (.x 0) tmp).lines R.ctx ps =
        .ok ([.ins (.adrpTlsDesc (.x 0) n'), .ins (.ldrTlsDescLo12 tmp (.x 0) n'),
          .ins (.addTlsDescLo12 (.x 0) (.x 0) n'), .ins (.blrTlsDesc tmp n'),
          .ins (.mrsTpidrEl0 tmp), .ins (.aluRRR .add true (.x 0) (.x 0) tmp)], ps) := by
      intro ps
      have : (tmp == Reg.x 0) = false := by simpa using htmp
      simp [MInst.lines, this, pure, Except.pure]
    refine ⟨_, hl, ?_, fun _ h => MInst.noConfusion h, fun _ h => MInst.noConfusion h,
      RunsAsSJ.and_lines (SegJ := R.StraightSeg Y) ?_ (P := fun ls1 =>
        ∀ x t, Line.ins x t ∈ ls1 → x.frLine = false) (by
        intro x t hx
        simp only [List.mem_cons, List.not_mem_nil, or_false, Line.ins.injEq] at hx
        rcases hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl)⟩
    · intro ln hln
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hln
      rcases hln with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Line.plain, Insn.condTarget?]
    · intro j T s _ _ s' hd hst hpc _ hex
      have hprog := hst.prog
      have herr := hst.err
      have hj : R.L[j]? = some (.ins (.adrpTlsDesc (.x 0) n')) := by
        have := congrArg (·[0]?) hd
        simpa [List.getElem?_drop] using this
      have hj1 : R.L[j + 1]? = some (.ins (.ldrTlsDescLo12 tmp (.x 0) n')) := by
        have := congrArg (·[1]?) hd
        simpa [List.getElem?_drop] using this
      have hj5 : R.L[j + 5]? = some (.ins (.aluRRR .add true (.x 0) (.x 0) tmp)) := by
        have := congrArg (·[5]?) hd
        simpa [List.getElem?_drop] using this
      simp only [tlsExec, htmp, ne_eq, not_false_eq_true, and_self, ↓reduceIte,
        Option.some.injEq] at hex
      subst hex
      have h1 := step_adrpTlsDesc hR hj hprog hpc
      have hprog1 : (Arm.w .PC (Arm.r .PC s + 4) s).program = R.fb.program R.base := by
        simp [Arm.w_program, hprog]
      have hpc1 : Arm.r .PC (Arm.w .PC (Arm.r .PC s + 4) s) = R.pcOf (j + 1) := by
        rw [Arm.r_of_w_same, hpc, pcOf_succ hj]
      have h2 := step_ldrTlsDescLo12 hR hj1 hprog1 hpc1
      have herr1 : Arm.r .ERR (Arm.w .PC (Arm.r .PC s + 4) s) = .None := by
        rw [Arm.r_of_w_different (by simp)]; exact herr
      have hfin : Arm.r .PC (R.H.tls n' tmp (Arm.w .PC (Arm.r .PC s + 4) s)) = R.pcOf (j + 5 + 1) := by
        rw [hT.pc _ _ _ herr1, Arm.r_of_w_same, hpc]
        have hins : ∀ ln ∈ [Line.ins (.adrpTlsDesc (.x 0) n'), .ins (.ldrTlsDescLo12 tmp (.x 0) n'),
            .ins (.addTlsDescLo12 (.x 0) (.x 0) n'), .ins (.blrTlsDesc tmp n'),
            .ins (.mrsTpidrEl0 tmp), .ins (.aluRRR .add true (.x 0) (.x 0) tmp)],
            ∃ i t, ln = .ins i t := by
          intro ln hln
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hln
          rcases hln with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
        have e6 := lineOffset_drop_ins (by simpa [RL.L] using hd) hins
        simp only [List.length_cons, List.length_nil] at e6
        simp only [RL.pcOf, RL.L, e6, BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]
      have e1 : iterN R.step 1 s = Arm.w .PC (Arm.r .PC s + 4) s := by simp only [iterN, h1]
      refine ⟨2, by simp only [iterN, h1, h2], ?_, fun i hi => ?_, fun i h0 hi => ?_, by simp⟩
      · rw [hfin]; rfl
      · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · show R.GoodXNY Y s
          exact RL.goodXNR_line hR hj hpc ⟨fun _ h => Insn.noConfusion h, fun _ h => Insn.noConfusion h⟩
            rfl (RL.good_of_sp hst.sp) herr hprog
            (RL.nextOk_pc4 (by rw [h1, Arm.r_of_w_same])) (fun _ _ _ h => by cases h)
            (fun _ h => by cases h) (not_call_insn (fun _ h => by cases h) fun _ h => by cases h)
            (RL.readsIn_hooked hR hj hpc rfl)
        · rw [e1]
          exact RL.goodXNR_line hR hj1 hpc1
            ⟨fun _ h => Insn.noConfusion h, fun _ h => Insn.noConfusion h⟩ rfl
            (R.good_succ hR hj (fun _ h => by cases h) (fun _ h => by cases h) hpc1) herr1 hprog1
            (RL.nextOk_succ hj5 rfl (by rw [h2, hfin])) (fun _ _ _ h => by cases h)
            (fun _ h => by cases h) (not_call_insn (fun _ h => by cases h) fun _ h => by cases h)
            (RL.readsIn_hooked hR hj1 hpc1 rfl)
      · obtain rfl : i = 1 := by omega
        exact ⟨j + 1, _, _, by omega, by simp, hj1, by rw [e1]; exact hpc1⟩
  | _ => simp [tlsExec] at hex

/-- **`ElfTlsGetAddr` on the machine, at a witness** (`realizes_tlsNR`). -/
theorem realizes_tlsNA {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} (hT : TlsOk R.F R.K R.X R.H)
    {s : Arm.ArmState}
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    {j : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {n : String} {d t : Nat} {ops : Array Operand} {outs : List CV}
    {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.elfTlsGetAddr n (.vreg d .int) (.vreg t .int)))
    (hops : (MInst.elfTlsGetAddr n (.vreg d .int) (.vreg t .int)).operands = .ok ops)
    (hsz : allocs.size = ops.size)
    (hsem : R.sem (.elfTlsGetAddr n (.vreg d .int) (.vreg t .int))
      (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = some (outs, w', .next))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      R.SegNA Y s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' n :=
  let ⟨n, c'', h1, h2, _⟩ := realizes_tlsNAF (Y := Y) hR hT hq hvb hi hops hsz hsem hlen hk
  ⟨n, c'', h1, h2⟩

end Backend.Proof
