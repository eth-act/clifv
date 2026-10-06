import FV.E2E.RegLevelTls
import FV.E2E.RegLevelFrame
import FV.E2E.RegLevelTry
import FV.Backend.Proof.RegallocCover
import FV.Backend.Proof.RegallocCSemWorld
import FV.E2E.RegLevelAtomic

/-!
# The register-level theorem (M6): `RegLevelCorrect` for the backend's code

* `realizes_all`: the machine `ArmStepX X H fa` realises the allocated code under `Q ∧ AInv`,
  by cases on the item (moves, `realizes_op_next` via `formOk_sound` for the covered
  straight-line forms, `Args`, calls, symbol addresses, islands, `trapIf` not taken, branches,
  jump tables, the LL/SC loops; returns and traps end the run, their `Q` is `True`);
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
  · split
    · simp only [Option.some.injEq, Prod.mk.injEq]
      rintro ⟨-, -, rfl⟩; exact .inl rfl
    · simp
  · split
    · simp only [Option.some.injEq, Prod.mk.injEq]
      rintro ⟨-, -, rfl⟩; exact .inl rfl
    · simp
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
  case atomicRmwLoop =>
    exact absurd (csem_loop_ctl (.inl ⟨_, _, _, _, _, _, _, _, rfl⟩) h) (by simp)
  case atomicCasLoop =>
    exact absurd (csem_loop_ctl (.inr ⟨_, _, _, _, _, _, _, rfl⟩) h) (by simp)
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
    {step : S → S} {Q : S → MConf V W → Prop} {T : S → Prop}
    (hQ : Realizes vc rf sem keep step Q T)
    {vs : VState V W} {v1 : VConf V W} (h1 : VStep vc sem (.run vs) v1) :
    ∀ k (c : MConf V W) s, c.measure ≤ k → Rl c (.run vs) → Q s c →
      ∃ n c' c'', Q (iterN step n s) c' ∧ Rl c' (.run vs) ∧ MStep vc sem keep rf c' c'' ∧
        Rl c'' v1 ∧ ∀ i < n, T (iterN step i s) := by
  intro k
  induction k with
  | zero =>
    intro c s hk hr hq
    obtain ⟨c', hc'⟩ := hR.progress hr h1
    obtain ⟨n1, c'', hs, hq', -⟩ := hQ s c c' hq hc'
    rcases hR.step hr hs with ⟨_, hlt⟩ | ⟨v'', hv'', hr''⟩
    · omega
    · rw [VStep_det hv'' h1] at hr''
      exact ⟨0, c, c'', hq, hr, hs, hr'', fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ k ihk =>
    intro c s hk hr hq
    obtain ⟨c', hc'⟩ := hR.progress hr h1
    obtain ⟨n1, c'', hs, hq', ht1⟩ := hQ s c c' hq hc'
    rcases hR.step hr hs with ⟨hr'', hlt⟩ | ⟨v'', hv'', hr''⟩
    · obtain ⟨n2, c3, c4, hq3, hr3, hs3, hr4, ht2⟩ := ihk c'' _ (by omega) hr'' hq'
      exact ⟨n1 + n2, c3, c4, by rw [iterN_add]; exact hq3, hr3, hs3, hr4, trace_add ht1 ht2⟩
    · rw [VStep_det hv'' h1] at hr''
      exact ⟨0, c, c'', hq, hr, hs, hr'', fun _ h => absurd h (Nat.not_lt_zero _)⟩

end

/-! ## `Realizes` by cases -/

/-- **The machine realises the allocated code** under `Q ∧ AInv`: every item case. -/
theorem realizes_all {R : RL} (hR : R.Wf) (hC : CalleeOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true → CalleeTryOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) :
    Realizes R.vc R.rf R.sem ckeep R.step (fun s c => Q R s c ∧ AInv R c) R.Good := by
  intro s c c' ⟨hq, hA⟩ h
  have fin : ∀ n c'', MStep R.vc R.sem ckeep R.rf c c'' → Q R (iterN R.step n s) c'' →
      (∀ i < n, R.Good (iterN R.step i s)) →
      ∃ n c'', MStep R.vc R.sem ckeep R.rf c c'' ∧ (Q R (iterN R.step n s) c'' ∧ AInv R c'') ∧
        ∀ i < n, R.Good (iterN R.step i s) :=
    fun n c'' hm hq' ht => ⟨n, c'', hm, ⟨hq', aInv_step hR hq hA hm⟩, ht⟩
  have nil : ∀ i < 0, R.Good (iterN R.step i s) := fun _ h => absurd h (Nat.not_lt_zero _)
  have hck := (lowerRFunc_ok hR.alloc).2.2
  cases h with
  | move =>
    obtain ⟨n, hn, ht⟩ := realizes_move hR hq
    exact fin n _ MStep.move hn ht
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
      obtain rfl := csem_ctl hct (R.sem_csem hsem)
      cases hn with
      | next hk =>
        have hnc : ∀ info, i ≠ .call info := by rintro info rfl; simp [MInst.isCtl] at hct
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_op_next hR hq hvb hi hops hsz hsem hlen hk hOS hL
          (csem_next_world' (R.sem_csem hsem) hnc herrw)
        exact fin n c'' hm hq' ht
    · cases i <;> simp only [MInst.isCtl, reduceCtorEq] at hct
      case call info =>
        have hc : ctl = .next := by
          have hsem := R.sem_csem hsem
          simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
          obtain ⟨_, -, -, -, h⟩ := hsem; exact h.symm
        subst hc
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_call hR hC hq hvb hi hops hsz hsem hlen hk
          exact fin n c'' hm hq' ht
      case args ds => exact fin 0 c' hstep (realizes_args hR hq hA hvb hi hstep) nil
      case rets us =>
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        cases hn with
        | ret _ => exact fin 0 _ hstep trivial nil
      case loadExtNameGot rd nm =>
        obtain ⟨d, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_symAddr hR hq hvb hi (.inl ⟨d, nm, rfl⟩) hops hsz
            hsem hlen hk
          exact fin n c'' hm hq' ht
      case loadExtNameNear rd nm off =>
        obtain ⟨d, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_symAddr hR hq hvb hi (.inr ⟨d, nm, off, rfl⟩) hops
            hsz hsem hlen hk
          exact fin n c'' hm hq' ht
      case jump l =>
        obtain ⟨n, hq', ht⟩ := realizes_goto hR hq hvb hi (.inl ⟨l, rfl⟩) hstep
        exact fin n c' hstep hq' ht
      case condBr t e kk =>
        obtain ⟨n, hq', ht⟩ := realizes_goto hR hq hvb hi (.inr (.inl ⟨t, e, kk, rfl⟩)) hstep
        exact fin n c' hstep hq' ht
      case testBitAndBranch kd t e rn bit =>
        obtain ⟨n, hq', ht⟩ := realizes_goto hR hq hvb hi (.inr (.inr ⟨kd, t, e, rn, bit, rfl⟩)) hstep
        exact fin n c' hstep hq' ht
      case trapIf kk code =>
        by_cases hh : ∃ w'', c' = .halt w''
        · obtain ⟨w'', rfl⟩ := hh
          exact fin 0 _ hstep trivial nil
        · obtain ⟨n, hq', ht⟩ := realizes_trapIf_next hR hq hvb hi hstep
            (fun w'' e => hh ⟨w'', e⟩)
          exact fin n c' hstep hq' ht
      case udf code =>
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        cases hn with
        | halt => exact fin 0 _ hstep trivial nil
      case emitIsland nb => exact fin 0 c' hstep (realizes_island hq hvb hi hstep) nil
      case jtSequence d ts ridx t1 t2 =>
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_jt hR hq hvb hi hstep
        exact fin n c'' hm hq' ht
      case atomicRmwLoop ty op fl ra ro rd r1 r2 =>
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_rmwLoop hR hq hvb hi hstep
        exact fin n c'' hm hq' ht
      case atomicCasLoop ty fl ra re rx rd r1 =>
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_casLoop hR hq hvb hi hstep
        exact fin n c'' hm hq' ht
      case tryCall info ti =>
        have hc : ctl = .goto ti.handlers.length := by
          have hsem := R.sem_csem hsem
          simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
          obtain ⟨_, -, -, -, h⟩ := hsem; exact h.symm
        subst hc
        cases hn with
        | goto hk1 hsucc hitems =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_tryCall hR hC (hT (hasTryCall_of_mem hvb hi)) hq hvb
            hi hops hsz hsem hlen hk1 hsucc hitems rfl
          exact fin n c'' hm hq' ht
      case elfTlsGetAddr nm rd tmp =>
        have hv := ctlCheck_inst hck hvb hi
        simp only [ctlInstOk, Bool.and_eq_true] at hv
        obtain ⟨d, rfl⟩ := isVregInt_iff hv.1
        obtain ⟨t, rfl⟩ := isVregInt_iff hv.2
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_tls hR (hTls (hasTls_of_mem hvb hi)) hq hvb hi
            hops hsz hsem hlen hk
          exact fin n c'' hm hq' ht

/-! ## The register-level theorem -/

theorem runX_eq (f : Arm.ArmState → Arm.ArmState) :
    ∀ (n : Nat) (s : Arm.ArmState), E2E.runX f n s = iterN f n s
  | 0, _ => rfl
  | n + 1, s => runX_eq f n (f s)

theorem setWidth128_inj {x y : BitVec 64} (h : x.setWidth 128 = y.setWidth 128) : x = y := by
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  have hx := x.isLt
  have hy := y.isLt
  simp only [BitVec.toNat_setWidth] at this
  omega

theorem calleeSaved_x {n : Nat} (h1 : 19 ≤ n) (h2 : n ≤ 28) :
    Reg.x n ∈ calleeSaved ∧ (Reg.x n).allocatable = true := by
  refine ⟨?_, ?_⟩
  · simp only [calleeSaved, List.mem_append, List.mem_map, List.mem_range]
    exact .inl ⟨n - 19, by omega, by congr 1; omega⟩
  · have : n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨
        n = 28 := by omega
    rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem calleeSaved_v {n : Nat} (h1 : 8 ≤ n) (h2 : n < 16) :
    Reg.v n ∈ calleeSaved ∧ (Reg.v n).allocatable = true := by
  refine ⟨?_, ?_⟩
  · simp only [calleeSaved, List.mem_append, List.mem_map, List.mem_range]
    exact .inr ⟨n - 8, by omega, by congr 1; omega⟩
  · have : n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by omega
    rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

/-- The store after a `Rets` step is the store before it (no defs, no clobbers). -/
theorem rets_store {us : List (Reg × Reg)} {ops : Array Operand} {allocs : Array Loc}
    {outs outs' : List CV} {m m2 : Loc → CV} {ctl : Ctl}
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hnil : outs = []) (hho : HavocOuts (MInst.rets us) ctl outs outs')
    (hcl : Clobbered ckeep (MInst.rets us).clobbers
      (writeM m ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs').filter (·.1.1.isEarly))) m2) :
    writeM m2 ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs').filter (·.1.1.isLate)) = m := by
  have h0 : outs' = [] := by
    have := hho.1; rw [hnil] at this; exact List.eq_nil_of_length_eq_zero this
  subst h0
  simp only [List.zip_nil_right, List.filter_nil] at hcl ⊢
  funext l
  exact hcl.1 l (by simp [MInst.clobbers])

/-- `regLevelCorrect_world` from verified in-states (`CheckedAt`) with an `EntryOk` entry state
`a0`, for the initial vreg file `ρsel m₀` chosen from the allocated code's initial store `m₀`
(any choice satisfying the entry state). -/
theorem regLevelCorrect_world_at {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt vcp rf cc ins a0) (hok : EntryOk a0) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : CalleeOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → CalleeTryOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K X H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀)
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r))) :
    ∃ m₀ : Loc → CV,
    (∀ us vals w, VReturns vcp (csemV gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) (ρsel m₀) w₀ us vals w →
      ∃ n, ArmRet ra s (E2E.runX (ArmStepX X H fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (ArmStepX X H fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a → (E2E.runX (ArmStepX X H fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (ArmStepX X H fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (ArmStepX X H fa) n s).mem a = s.mem a) ∧
        (E2E.runX (ArmStepX X H fa) n s).program = s.program ∧
        ∀ i, 0 < i → i < n → PostCall fa base (Arm.r .PC (E2E.runX (ArmStepX X H fa) i s)) →
          spv (E2E.runX (ArmStepX X H fa) i s) = spv s - BitVec.ofNat 64 (frameDrop af)) ∧
    (∀ c, VTraps vcp (csemV gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) (ρsel m₀) w₀ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX X H fa) n s)) := by
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨body, psF, hb, -, hk⟩ := emitFunc_ok hemit
  subst hk
  let R : RL := ⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, G, gv⟩
  have hR : R.Wf := ⟨⟨cc, ins, a0, hcheck, hok⟩, halloc, hemit, hlayout, hlm, by show 4 * fb.words.size ≤ 2 ^ 64; have := hent.fits; omega, hres,
    ⟨body, hb⟩, hent.program, hG⟩
  have hck := (lowerRFunc_ok hR.alloc).2.2
  obtain ⟨n0, ht0, hq0, hA0, hf0⟩ := q_init hR hent hbe
  obtain ⟨Rl, hSim, hinit, hkeep⟩ :=
    checkedAt_sound R.vc R.rf R.sem ckeep hcheck (locVal R.fr (iterN R.step n0 s))
      (ρsel (locVal R.fr (iterN R.step n0 s))) w₀ (hsel _)
  have hRz := realizes_all hR hC hCT hTls hcov
  refine ⟨locVal R.fr (iterN R.step n0 s), fun us vals w hret => ?_, fun c htr => ?_⟩
  · -- a return
    obtain ⟨b, k, ρ, w₁, vb, ops, outs, hstar, hvb, hi, hops, hvals, hsem⟩ := hret
    obtain ⟨n1, c1, ⟨hq1, hA1⟩, hr1, ht1⟩ := forward hSim hRz hstar hinit ⟨hq0, hA0⟩
    obtain ⟨ns, rfl⟩ := ctlCheck_rets hck hvb hi
    rw [operands_rets] at hops
    cases hops
    have hsem' := hsem
    simp only [csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
    obtain ⟨rfl, rfl, -⟩ := hsem'
    have h1 : VStep R.vc R.sem (.run ⟨b, k, ρ, w₁⟩) (.ret vals w₁) := by
      rw [hvals]
      refine VStep.step hvb hi (operands_rets ns) (by rw [hvals] at hsem; exact hsem) ?_ (VNext.ret rfl)
      rw [List.toList_toArray, filter_isDef_retOps]; rfl
    obtain ⟨n2, c', c'', ⟨hq2, -⟩, hr2, hms, hr3, ht2⟩ :=
      forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 ⟨hq1, hA1⟩
    have hfin : ∀ n3, E2E.runX (ArmStepX X H fa) (n0 + n1 + n2 + n3) s =
        iterN R.step n3 (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s))) := by
      intro n3; rw [runX_eq]; simp only [iterN_add]; rfl
    cases c'' with
    | run s' => obtain ⟨_, e⟩ := hSim.run hr3; cases e
    | halt w'' => cases hSim.halt hr3
    | ret uses m' w'' =>
      have hks := hkeep hr3
      cases hms with
      | op hvb' hi' hops' hsz hsem2 hlen2 hho hcl hn =>
        obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
        simp only at hb' hk' hw'
        subst hb' hk' hw'
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        rw [operands_rets] at hops'; cases hops'
        have hsem3 := hsem2
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem3
        obtain ⟨rfl, rfl, rfl⟩ := hsem3
        cases hn with
        | ret _ =>
        rw [rets_store hlen2 rfl hho hcl] at hks
        have hst := q_stRel hq2
        obtain ⟨n3, ht3, hpc, herr, hsp, hx29, hregs, hmem, hfld, hprogF, hvalsM⟩ :=
          ret_machine hR hent hq2 hvb hi
        -- every state of the run before the return (but the entry) is `Good`
        have htr : ∀ i, 0 < i → i < n0 + n1 + n2 + n3 →
            R.Good (E2E.runX (ArmStepX X H fa) i s) := by
          intro i hi0 hi
          rw [runX_eq]
          have hb := trace_add ht1 (trace_add ht2 ht3)
          by_cases h : i < n0
          · exact ht0 i hi0 h
          · have := hb (i - n0) (by omega)
            rwa [← iterN_add, show n0 + (i - n0) = i by omega] at this
        have hm0 : ∀ r, locVal R.fr (iterN R.step n0 s) (.reg r) = regVal (iterN R.step n0 s) r :=
          fun _ => rfl
        have hms : ∀ r, r.allocatable = true → _ = regVal _ r := fun r hr =>
          hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
        refine ⟨n0 + n1 + n2 + n3, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, fun i hi0 hi hpcall => ?_⟩
        rotate_right
        · exact (htr i hi0 hi).resolve_left (fun h => h hpcall)
        all_goals rw [hfin]
        · exact hpc
        · exact herr
        · exact hsp
        · intro n hn
          simp only [calleeSavedX, List.mem_map, List.mem_range] at hn
          obtain ⟨a, ha, rfl⟩ := hn
          by_cases h29 : a = 10
          · subst h29; exact hx29
          obtain ⟨hcs, hal⟩ := calleeSaved_x (n := 19 + a) (by omega) (by omega)
          have k1 := hks _ hcs
          simp only [ckeep, hm0] at k1
          rw [hms _ hal] at k1
          have hne : ∀ q, q < 32 → q ≠ 19 + a →
              Arm.StateField.GPR (rnum (19 + a)) ≠ .GPR (BitVec.ofNat 5 q) :=
            fun q h1 h2 e => rnum_ne (a := 19 + a) (b := q) (by omega) h1 (Ne.symm h2)
              (Arm.StateField.GPR.inj e)
          have k2 := hregs _ hal
          simp only [regVal] at k1 k2
          rw [hf0 _ (by simp) (hne 29 (by omega) (by omega)) (hne 31 (by omega) (by omega))
            (hne 16 (by omega) (by omega))] at k1
          exact setWidth128_inj (k2.trans k1)
        · intro n h8 h16
          obtain ⟨hcs, hal⟩ := calleeSaved_v h8 h16
          have k1 := hks _ hcs
          simp only [ckeep, hm0] at k1
          rw [hms _ hal] at k1
          have k2 := hregs _ hal
          simp only [regVal] at k1 k2
          rw [hf0 _ (by simp) (by simp) (by simp) (by simp)] at k1
          show (Arm.r (.SFP (rnum n)) _).setWidth 64 = (Arm.r (.SFP (rnum n)) s).setWidth 64
          rw [k2]
          exact setWidth128_inj k1
        · intro j v p x hj hx
          have e1 := hSim.ret hr3
          simp only [VConf.ret.injEq] at e1
          rw [e1.1] at hx
          exact hvalsM _ (operands_rets ns) j v p x hj hx
        · intro a ha
          rw [hmem]
          exact hst.world.2.1 a ha
        · intro f hf h29 h31
          rw [hfld f hf h29 h31]
          exact hst.world.1 f hf
        · intro a ha
          rw [hmem]
          exact hst.gkeep a ha
        · rw [hprogF, hst.prog]
          exact hent.program.symm
  · -- a trap
    obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hstar, hvb, hi, hops, hsem, htc⟩ := htr
    obtain ⟨n1, c1, ⟨hq1, hA1⟩, hr1, -⟩ := forward hSim hRz hstar hinit ⟨hq0, hA0⟩
    obtain ⟨hnil, hform⟩ := csem_halt (csemV_sub hsem)
    subst hnil
    have hdefs : ops.toList.filter Operand.isDef = [] := by
      rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
      · rw [udf_ops hops]; rfl
      · exact trapIf_nodefs hops
    have h1 : VStep R.vc R.sem (.run ⟨b, k, ρ, w⟩) (.halt w') :=
      VStep.step hvb hi hops hsem (by rw [hdefs]; rfl) VNext.halt
    obtain ⟨n2, c', c'', ⟨hq2, -⟩, hr2, hms, hr3, -⟩ :=
      forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 ⟨hq1, hA1⟩
    have hfin : ∀ n3, E2E.runX (ArmStepX X H fa) (n0 + n1 + n2 + n3) s =
        iterN R.step n3 (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s))) := by
      intro n3; rw [runX_eq]; simp only [iterN_add]; rfl
    cases c'' with
    | run s' => obtain ⟨_, e⟩ := hSim.run hr3; cases e
    | ret vs m' w'' => cases hSim.ret hr3
    | halt w'' =>
      cases hms with
      | op hvb' hi' hops' hsz hsem2 hlen2 hho hcl hn =>
        obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
        simp only at hb' hk' hw'
        subst hb' hk' hw'
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
        · simp only [trapCode?, Option.some.injEq] at htc
          subst htc
          exact ⟨n0 + n1 + n2 + 0, by rw [hfin]; exact trap_udf hR hq2 hvb hi⟩
        · cases hn with
          | halt =>
          obtain ⟨-, hform2⟩ := csem_halt (csemV_sub hsem2)
          rcases hform2 with ⟨_, e⟩ | ⟨kk', cd', e, hholds⟩
          · cases e
          · cases e
            simp only [trapCode?, Option.some.injEq] at htc
            subst htc
            obtain ⟨n3, htrap⟩ := trap_trapIf hR hq2 hvb hi hops' hholds
            exact ⟨n0 + n1 + n2 + n3, by rw [hfin]; exact htrap⟩

/-- **The register-level theorem with kept addresses and the final world** (M6 + M5, for
linking): `RegLevelCorrect`'s simulation for the activation entered in `s` whose addresses
outside the world are `frameWG K … G s` (the frame, the callees' dead stack and addresses `G`
it keeps: its callers' frames, the program's code), from a body-entry world `w₀` that agrees
with `s` only outside them and on the registers the entry `Args` reads (`BodyEntryW`), with the
callee contract required only at the states that keep `G` (`CalleeOkG`). A return additionally
leaves every unmasked field but x29/`sp` as the VCode run's final world `w` (the flags, x18, …),
the memory at `G` as at entry and the program unchanged. -/
theorem regLevelCorrect_world {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ()) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : CalleeOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → CalleeTryOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K X H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀) (ρ₀ : Nat → CV) :
    (∀ us vals w, VReturns vcp (csemV gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ us vals w →
      ∃ n, ArmRet ra s (E2E.runX (ArmStepX X H fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (ArmStepX X H fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a → (E2E.runX (ArmStepX X H fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (ArmStepX X H fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (ArmStepX X H fa) n s).mem a = s.mem a) ∧
        (E2E.runX (ArmStepX X H fa) n s).program = s.program ∧
        ∀ i, 0 < i → i < n → PostCall fa base (Arm.r .PC (E2E.runX (ArmStepX X H fa) i s)) →
          spv (E2E.runX (ArmStepX X H fa) i s) = spv s - BitVec.ofNat 64 (frameDrop af)) ∧
    (∀ c, VTraps vcp (csemV gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX X H fa) n s)) := by
  obtain ⟨cc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  obtain ⟨_, h⟩ := regLevelCorrect_world_at hat (entryOk_of_le hle) halloc hemit hlayout hcov hent
    hres hG hC hCT hTls hbe (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  exact h

/-- `regLevelCorrect_world` for an `AllocChecked` allocation (V4), for one initial vreg file of the
theorem's choice (`entryRho`: the values the entry state places in the initial store). -/
theorem regLevelCorrect_world_ex {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : AllocChecked vcp rf) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : CalleeOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → CalleeTryOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K X H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀) :
    ∃ ρ₀ : Nat → CV,
    (∀ us vals w, VReturns vcp (csemV gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ us vals w →
      ∃ n, ArmRet ra s (E2E.runX (ArmStepX X H fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (ArmStepX X H fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a → (E2E.runX (ArmStepX X H fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (ArmStepX X H fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (ArmStepX X H fa) n s).mem a = s.mem a) ∧
        (E2E.runX (ArmStepX X H fa) n s).program = s.program ∧
        ∀ i, 0 < i → i < n → PostCall fa base (Arm.r .PC (E2E.runX (ArmStepX X H fa) i s)) →
          spv (E2E.runX (ArmStepX X H fa) i s) = spv s - BitVec.ofNat 64 (frameDrop af)) ∧
    (∀ c, VTraps vcp (csemV gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX X H fa) n s)) := by
  obtain ⟨cc, ins, a0, hat, hok⟩ := hcheck
  obtain ⟨_, h⟩ := regLevelCorrect_world_at hat hok halloc hemit hlayout hcov hent hres hG hC hCT
    hTls hbe (entryRho a0) (Inv_entryRho ckeep hok)
  exact ⟨_, h⟩

/-- **`RegLevelCorrect` for the backend's code** (M6 + M5): for the allocated, lowered, emitted
and laid-out function, the machine `ArmStepX X H fa` realises every return and every trap of
the prepared VCode under `csem` (addresses outside the world `frameW K`: the frame and the
callees' dead stack of `K` bytes; function context `⟨fa.k, af.slotBase⟩`, external semantics
`X`), given the form coverage `FormsCovered` (decided by `formsCoveredB`), the callee contract
`CalleeOk` of every activation (with stack budget `K`, for the call sites of `vcp`), and (for code with a `tls_value`) the
TLSDESC contract `TlsOk`. (`regLevelCorrect_world` without kept addresses.) -/
theorem regLevelCorrect_backend {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ()) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {K : Nat} (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : vcp.hasTryCall = true → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : vcp.hasTls = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H) :
    RegLevelCorrect
      (fun s => csem (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
        ⟨fa.k, af.slotBase⟩ X)
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af) K
      (ArmStepX X H fa) vcp af fb := by
  intro base ra s hent hres w₀ hbe ρ₀
  have e := frameWG_false K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s
  have h := regLevelCorrect_world (G := fun _ => False) (gv := fun _ _ => False) hcheck halloc hemit
    hlayout hcov hent.toCall hres
    (fun _ h => h.elim) (by rw [e]; exact (hC s).g _ s _ _) (by rw [e]; exact fun h => (hCT h s).g _ _ s _ _)
    (by rw [e]; exact fun h => hTls h s)
    (by rw [e]; exact hbe.w _ fun r ⟨_, _, hvb, hi, _, hv⟩ =>
      ((ctlCheck_args (lowerRFunc_ok halloc).2.2 hvb hi).2.2 _ hv).2) ρ₀
  rw [e, csemV_bot] at h
  exact ⟨fun us vals w hret => by
    obtain ⟨n, h1, h2, h3, -⟩ := h.1 us vals w hret
    exact ⟨n, h1, h2, h3⟩, h.2⟩

/-- `regLevelCorrect_backend` for an `AllocChecked` allocation (V4): `RegLevelCorrectEx`. -/
theorem regLevelCorrect_backend_ex {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : AllocChecked vcp rf) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {K : Nat} (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : vcp.hasTryCall = true → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : vcp.hasTls = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H) :
    RegLevelCorrectEx
      (fun s => csem (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
        ⟨fa.k, af.slotBase⟩ X)
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af) K
      (ArmStepX X H fa) vcp af fb := by
  intro base ra s hent hres w₀ hbe
  have e := frameWG_false K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s
  obtain ⟨ρ₀, h⟩ := regLevelCorrect_world_ex (G := fun _ => False) (gv := fun _ _ => False) hcheck halloc hemit
    hlayout hcov hent.toCall hres
    (fun _ h => h.elim) (by rw [e]; exact (hC s).g _ s _ _) (by rw [e]; exact fun h => (hCT h s).g _ _ s _ _)
    (by rw [e]; exact fun h => hTls h s)
    (by rw [e]; exact hbe.w _ fun r ⟨_, _, hvb, hi, _, hv⟩ =>
      ((ctlCheck_args (lowerRFunc_ok halloc).2.2 hvb hi).2.2 _ hv).2)
  rw [e, csemV_bot] at h
  exact ⟨ρ₀, fun us vals w hret => by
    obtain ⟨n, h1, h2, h3, -⟩ := h.1 us vals w hret
    exact ⟨n, h1, h2, h3⟩, h.2⟩

end Backend.Proof
