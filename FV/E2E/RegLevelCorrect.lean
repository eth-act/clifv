import FV.E2E.RegLevelFrame
import FV.Backend.Proof.RegallocCover
import FV.Backend.Proof.RegallocCSemWorld

/-!
# The register-level theorem (M6): `RegLevelCorrect` for the backend's code

* `realizes_all`: the machine `ArmStepX X H fa` realises the allocated code under `Q ∧ AInv`,
  by cases on the item (moves, `realizes_op_next` via `formOk_sound` for the covered
  straight-line forms, `Args`, calls, symbol addresses, islands, `trapIf` not taken, branches,
  jump tables; returns and traps end the run, their `Q` is `True`);
* `forward_last`: along a VCode step from a related configuration the machine reaches the
  allocated-code configuration whose next `MStep` is related to the VCode's successor;
* `regLevelCorrect_backend`: the prologue (`q_init`) puts the machine at the entry
  configuration; `checkAlloc_sound`'s relation, `forward` and `forward_last` bring it to the
  `Rets` item (then `ret_machine`: `ArmRet`, values, memory; callee-saved registers from the
  checker's `keep` conclusion) or to the halting `udf`/`trapIf` item (`trap_udf`/`trap_trapIf`).
-/

namespace Backend.Proof

open Backend E2E

/-! ## Control outcomes of `csem` -/

set_option maxHeartbeats 4000000 in
theorem ispec_ctl {i : MInst} {uses : List CV} {w : Arm.ArmState} {outs : List CV}
    {w' : Arm.ArmState} {ctl : Ctl} (h : ispec i uses w = some (outs, w', ctl)) :
    ctl = .next ∨ i.isCtl = true := by
  revert h
  unfold ispec
  split
  all_goals (repeat' split)
  all_goals intro h
  all_goals first
    | (right; rfl)
    | (left
       simp only [Option.map_eq_some_iff, Option.some.injEq, Prod.mk.injEq, reduceCtorEq,
         false_and, and_false] at h <;>
       first
         | exact h.2.2.symm
         | (obtain ⟨_, -, -, -, h⟩ := h; exact h.symm))

theorem mspec_ctl {sb : Nat} {i : MInst} {uses : List CV} {w : Arm.ArmState} {outs : List CV}
    {w' : Arm.ArmState} {ctl : Ctl} (h : mspec sb i uses w = some (outs, w', ctl)) :
    ctl = .next ∨ i.isCtl = true := by
  revert h
  unfold mspec
  split
  · split
    · simp
    · simp only [Option.map_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
      rintro ⟨_, -, -, -, rfl⟩; exact .inl rfl
  · split
    · simp
    · simp only [Option.map_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
      rintro ⟨_, -, -, -, rfl⟩; exact .inl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq]
    rintro ⟨-, -, rfl⟩; exact .inl rfl
  · exact ispec_ctl

/-- A non-control form falls through. -/
theorem csem_ctl {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst} {uses : List CV}
    {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState} {ctl : Ctl}
    (hc : i.isCtl = false) (h : csem F ctx X i uses w = some (outs, w', ctl)) : ctl = .next := by
  unfold csem at h
  split at h
  all_goals first
    | (simp [MInst.isCtl] at hc; done)
    | skip
  split at h
  · exact (straightSem_some h).1
  · rcases mspec_ctl h with h | h
    · exact h
    · rw [hc] at h; cases h

/-- `csem` halts only at a `udf` or a taken `trapIf`. -/
theorem csem_halt {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst} {uses : List CV}
    {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState}
    (h : csem F ctx X i uses w = some (outs, w', .halt)) :
    outs = [] ∧ ((∃ c, i = .udf c) ∨ (∃ kk c, i = .trapIf kk c ∧ kk.holds uses w = true)) := by
  cases hc : i.isCtl
  · exact absurd (csem_ctl hc h) (by simp)
  cases i <;> simp only [MInst.isCtl, reduceCtorEq] at hc
  all_goals simp only [csem, Option.map_eq_some_iff, Option.some.injEq, Prod.mk.injEq,
    reduceCtorEq, and_false, false_and, exists_false] at h
  all_goals first
    | (obtain ⟨rfl, -, -⟩ := h; exact ⟨rfl, .inl ⟨_, rfl⟩⟩)
    | (obtain ⟨rfl, -, h⟩ := h
       split at h
       · exact ⟨rfl, .inr ⟨_, _, rfl, by assumption⟩⟩
       · cases h)
    | (split at h <;> simp_all)
    | skip
  all_goals (split at h <;> (try split at h) <;> simp_all)

theorem udf_ops {c : Clif.TrapCode} {ops : Array Operand} (h : (MInst.udf c).operands = .ok ops) :
    ops = #[] := by
  have : (MInst.udf c).operands = .ok #[] := rfl
  rw [this] at h; cases h; rfl

theorem trapIf_nodefs {kk : CondBrKind} {c : Clif.TrapCode} {ops : Array Operand}
    (h : (MInst.trapIf kk c).operands = .ok ops) : ops.toList.filter Operand.isDef = [] := by
  cases kk with
  | cond cd =>
    have : (MInst.trapIf (.cond cd) c).operands = .ok #[] := rfl
    rw [this] at h; cases h; rfl
  | zero r sz =>
    cases r with
    | vreg n cls =>
      have : (MInst.trapIf (.zero (.vreg n cls) sz) c).operands =
          .ok #[⟨n, cls, OpSpec.use.kind, OpSpec.use.pos, OpSpec.use.con⟩] := rfl
      rw [this] at h; cases h; rfl
    | _ =>
      revert h
      simp only [MInst.operands, MInst.visitOperands, CondBrKind.visit]
      split <;> intro h <;> (try cases h) <;> rfl
  | notZero r sz =>
    cases r with
    | vreg n cls =>
      have : (MInst.trapIf (.notZero (.vreg n cls) sz) c).operands =
          .ok #[⟨n, cls, OpSpec.use.kind, OpSpec.use.pos, OpSpec.use.con⟩] := rfl
      rw [this] at h; cases h; rfl
    | _ =>
      revert h
      simp only [MInst.operands, MInst.visitOperands, CondBrKind.visit]
      split <;> intro h <;> (try cases h) <;> rfl

/-! ## Forward to the last step -/

section
variable {V W S : Type} {vc : VCode} {rf : RFunc} {sem : ISem V W} {keep : Reg → V → V}

/-- Along a VCode step `vs → v1` from a related configuration, the machine reaches (past the
pending moves) a configuration `c'` related to `vs` whose `MStep` successor `c''` is related to
`v1`. -/
theorem forward_last {Rl : MConf V W → VConf V W → Prop} (hR : IsSimulation vc rf sem keep Rl)
    {step : S → S} {Q : S → MConf V W → Prop} (hQ : Realizes vc rf sem keep step Q)
    {vs : VState V W} {v1 : VConf V W} (h1 : VStep vc sem (.run vs) v1) :
    ∀ k (c : MConf V W) s, c.measure ≤ k → Rl c (.run vs) → Q s c →
      ∃ n c' c'', Q (iterN step n s) c' ∧ Rl c' (.run vs) ∧ MStep vc sem keep rf c' c'' ∧
        Rl c'' v1 := by
  intro k
  induction k with
  | zero =>
    intro c s hk hr hq
    obtain ⟨c', hc'⟩ := hR.progress hr h1
    obtain ⟨n1, c'', hs, hq'⟩ := hQ s c c' hq hc'
    rcases hR.step hr hs with ⟨_, hlt⟩ | ⟨v'', hv'', hr''⟩
    · omega
    · rw [VStep_det hv'' h1] at hr''
      exact ⟨0, c, c'', hq, hr, hs, hr''⟩
  | succ k ihk =>
    intro c s hk hr hq
    obtain ⟨c', hc'⟩ := hR.progress hr h1
    obtain ⟨n1, c'', hs, hq'⟩ := hQ s c c' hq hc'
    rcases hR.step hr hs with ⟨hr'', hlt⟩ | ⟨v'', hv'', hr''⟩
    · obtain ⟨n2, c3, c4, hq3, hr3, hs3, hr4⟩ := ihk c'' _ (by omega) hr'' hq'
      exact ⟨n1 + n2, c3, c4, by rw [iterN_add]; exact hq3, hr3, hs3, hr4⟩
    · rw [VStep_det hv'' h1] at hr''
      exact ⟨0, c, c'', hq, hr, hs, hr''⟩

end

/-! ## `Realizes` by cases -/

/-- **The machine realises the allocated code** under `Q ∧ AInv`: every item case. -/
theorem realizes_all {R : RL} (hR : R.Wf) (hC : CalleeOk R.F R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) :
    Realizes R.vc R.rf R.sem ckeep R.step (fun s c => Q R s c ∧ AInv c) := by
  intro s c c' ⟨hq, hA⟩ h
  have fin : ∀ n c'', MStep R.vc R.sem ckeep R.rf c c'' → Q R (iterN R.step n s) c'' →
      ∃ n c'', MStep R.vc R.sem ckeep R.rf c c'' ∧ (Q R (iterN R.step n s) c'' ∧ AInv c'') :=
    fun n c'' hm hq' => ⟨n, c'', hm, hq', aInv_step hR hq hA hm⟩
  have hck := (lowerRFunc_ok hR.alloc).2.2.2
  cases h with
  | move =>
    obtain ⟨n, hn⟩ := realizes_move hR hq
    exact fin n _ MStep.move hn
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsem hlen hho hcl hn =>
    have hstep : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c' :=
      MStep.op hvb hi hops hsz hsem hlen hho hcl hn
    have herrw : Arm.r .ERR w = .None := by
      have hst := q_stRel hq
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    cases hct : i.isCtl
    · -- a covered straight-line form
      have hfo := (hcov b vb k i hvb hi).resolve_left (by simp [hct])
      obtain ⟨hOS, hL⟩ := formOk_sound (F := R.F) (X := R.X) hfo
      obtain rfl := csem_ctl hct hsem
      cases hn with
      | next hk =>
        have hnc : ∀ info, i ≠ .call info := by rintro info rfl; simp [MInst.isCtl] at hct
        obtain ⟨n, c'', hm, hq'⟩ := realizes_op_next hR hq hvb hi hops hsz hsem hlen hk hOS hL
          (csem_next_world' hsem hnc herrw)
        exact fin n c'' hm hq'
    · cases i <;> simp only [MInst.isCtl, reduceCtorEq] at hct
      case call info =>
        have hc : ctl = .next := by
          simp only [RL.sem, csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
          obtain ⟨_, -, -, -, h⟩ := hsem; exact h.symm
        subst hc
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq'⟩ := realizes_call hR hC hq hvb hi hops hsz hsem hlen hk
          exact fin n c'' hm hq'
      case args ds => exact fin 0 c' hstep (realizes_args hR hq hA hvb hi hstep)
      case rets us =>
        simp only [RL.sem, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        cases hn with
        | ret _ => exact fin 0 _ hstep trivial
      case loadExtNameGot rd nm =>
        obtain ⟨d, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
        have hsem' := hsem
        simp only [RL.sem, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq'⟩ := realizes_symAddr hR hq hvb hi (.inl ⟨d, nm, rfl⟩) hops hsz
            hsem hlen hk
          exact fin n c'' hm hq'
      case loadExtNameNear rd nm off =>
        obtain ⟨d, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
        have hsem' := hsem
        simp only [RL.sem, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq'⟩ := realizes_symAddr hR hq hvb hi (.inr ⟨d, nm, off, rfl⟩) hops
            hsz hsem hlen hk
          exact fin n c'' hm hq'
      case jump l =>
        obtain ⟨n, hq'⟩ := realizes_goto hR hq hvb hi (.inl ⟨l, rfl⟩) hstep
        exact fin n c' hstep hq'
      case condBr t e kk =>
        obtain ⟨n, hq'⟩ := realizes_goto hR hq hvb hi (.inr (.inl ⟨t, e, kk, rfl⟩)) hstep
        exact fin n c' hstep hq'
      case testBitAndBranch kd t e rn bit =>
        obtain ⟨n, hq'⟩ := realizes_goto hR hq hvb hi (.inr (.inr ⟨kd, t, e, rn, bit, rfl⟩)) hstep
        exact fin n c' hstep hq'
      case trapIf kk code =>
        by_cases hh : ∃ w'', c' = .halt w''
        · obtain ⟨w'', rfl⟩ := hh
          exact fin 0 _ hstep trivial
        · obtain ⟨n, hq'⟩ := realizes_trapIf_next hR hq hvb hi hstep
            (fun w'' e => hh ⟨w'', e⟩)
          exact fin n c' hstep hq'
      case udf code =>
        simp only [RL.sem, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        cases hn with
        | halt => exact fin 0 _ hstep trivial
      case emitIsland nb => exact fin 0 c' hstep (realizes_island hq hvb hi hstep)
      case jtSequence d ts ridx t1 t2 =>
        obtain ⟨n, c'', hm, hq'⟩ := realizes_jt hR hq hvb hi hstep
        exact fin n c'' hm hq'

end Backend.Proof
