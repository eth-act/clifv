import FV.E2E.RegLevelCorrectC
import FV.E2E.RegLevelMoveNR
import FV.E2E.RegLevelNextNR
import FV.E2E.RegLevelCallNR
import FV.E2E.RegLevelTryNR
import FV.E2E.RegLevelJTNR
import FV.E2E.RegLevelAtomicNR
import FV.E2E.RegLevelTlsNR

/-!
# The counted register-level theorem with guarded world reads (SEM1 #537, item (2))

`RegLevelCorrectCR` gives `RL.ReadsIn` along the activation's run: every read is a jump-table
byte, a frame byte, or a byte outside the frame addresses `F`. The lock-step of two runs needs
the third kind narrowed to bytes the two runs agree on. That set is a per-step fact of the VCode
run (in the pair run of `vcode_niIG`: the bytes outside `Zof F D cm`), so it enters as a guard on
the VCode semantics:

* `MInst.wReads`: the instructions whose lines may read world bytes (the straight-line forms and
  the atomic loops);
* `WGuard F ctx X Ok i us w`: some `Y ⊇ F` with `Ok w Y` at which, for a world-reading `i`,
  `csem Y` also gives a result;
* `csemVG gv F ctx X Ok`: `csemV` where `WGuard` holds, undefined elsewhere (`RL.semG`);
* `RL.WReadsIn Ok u`: the reads at `u` are `ReadsInY Y` for a `Y ⊇ F` that is everything (no
  world byte read) or admitted by `Ok` at some world;
* `MStep.guardLift`: a step of `sem` from a configuration that has a step of the guarded
  semantics is one of the guarded semantics;
* **`realizes_allCY`**, `realizes_allC_spY`: `realizes_allCR`/`realizes_allC_spR` for the guarded
  semantics, the segments' states satisfying `GoodX` and `WReadsIn`.
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.Driver

/-- The atomic loops. -/
def _root_.Backend.MInst.isAtomicLoop : MInst → Bool
  | .atomicRmwLoop .. => true
  | .atomicCasLoop .. => true
  | _ => false

/-- The instructions whose allocated lines may read world bytes: the straight-line forms
(`isCtl = false`) and the atomic loops. -/
def _root_.Backend.MInst.wReads (i : MInst) : Bool := !i.isCtl || i.isAtomicLoop

/-- **The guard of the world reads** at an instruction, its use values and the world: a set
`Y ⊇ F` admitted by `Ok` at the world at which, for a world-reading instruction, `csem` also
gives a result. -/
def WGuard (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem)
    (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop) (i : MInst) (us : List CV) (w : Arm.ArmState) :
    Prop :=
  ∃ Y, (∀ a, F a → Y a) ∧ Ok w Y ∧ (i.wReads = true → ∃ r, csem Y ctx X i us w = some r)

open Classical in
/-- **The guarded semantics of the world reads**: `csemV` where `WGuard` holds, undefined
elsewhere. -/
noncomputable def csemVG (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (X : ExtSem) (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop) : ISem CV Arm.ArmState :=
  fun i us w => if WGuard F ctx X Ok i us w then csemV gv F ctx X i us w else none

/-- **The counted guarded semantics**: `csemVG` with call number `n`'s external semantics. -/
noncomputable def csemVIG (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (X : ExtSemI) (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop) :
    ISem CV (Arm.ArmState × Nat) :=
  ISem.counted fun n => csemVG gv F ctx (X.at n) Ok

theorem csemVG_inv {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop} {i : MInst} {us : List CV}
    {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    (h : csemVG gv F ctx X Ok i us w = some r) :
    WGuard F ctx X Ok i us w ∧ csemV gv F ctx X i us w = some r := by
  unfold csemVG at h
  split at h
  · exact ⟨‹_›, h⟩
  · cases h

/-- A step of the counted guarded semantics is one of `csemVI`. -/
theorem csemVIG_sub {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx}
    {X : ExtSemI} {Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop} {i : MInst} {us : List CV}
    {w : Arm.ArmState × Nat} {r : List CV × (Arm.ArmState × Nat) × Ctl}
    (h : csemVIG gv F ctx X Ok i us w = some r) : csemVI gv F ctx X i us w = some r := by
  simp only [csemVIG, csemVI, ISem.counted, Option.map_eq_some_iff] at h ⊢
  obtain ⟨r', h1, h2⟩ := h
  exact ⟨r', (csemVG_inv h1).2, h2⟩

/-- **The guard at `Y := F` is no restriction**: `csemVG … (fun _ Y => Y = F)` is `csemV`. -/
theorem csemVG_eqF (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    csemVG gv F ctx X (fun _ Y => Y = F) = csemV gv F ctx X := by
  funext i us w
  unfold csemVG
  split
  · rfl
  · rename_i hg
    cases h : csemV gv F ctx X i us w with
    | none => rfl
    | some r => exact absurd ⟨F, fun _ h => h, rfl, fun _ => ⟨r, csemV_sub h⟩⟩ hg

theorem csemVIG_eqF (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSemI) :
    csemVIG gv F ctx X (fun _ Y => Y = F) = csemVI gv F ctx X := by
  simp only [csemVIG, csemVI, csemVG_eqF]

/-- The activation's guarded semantics. -/
noncomputable def RL.semG (R : RL) (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop) :
    ISem CV Arm.ArmState :=
  csemVG R.gv R.F R.ctx R.X Ok

/-- **The located reads at `u`, the world reads guarded**: `ReadsInY Y` for a `Y ⊇ F` that is
everything (the line reads no world byte) or admitted by `Ok` at some world. -/
def RL.WReadsIn (R : RL) (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop) (u : Arm.ArmState) :
    Prop :=
  ∃ Y, (∀ a, R.F a → Y a) ∧ ((∀ a, Y a) ∨ ∃ w, Ok w Y) ∧ R.ReadsInY Y u

theorem RL.WReadsIn.readsIn {R : RL} {Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop}
    {u : Arm.ArmState} (h : R.WReadsIn Ok u) : R.ReadsIn u :=
  let ⟨_, _, _, h⟩ := h; h.readsIn

section
variable {V W : Type} {vc : VCode} {rf : RFunc} {keep : Reg → V → V}

/-- **A step of `sem` from a configuration with a step of `sem'` is one of `sem'`** when `sem'`
agrees with `sem` wherever `sem'` is defined. -/
theorem MStep.guardLift {sem sem' : ISem V W} {c c' c'' : MConf V W}
    (h : MStep vc sem keep rf c c'') (h' : MStep vc sem' keep rf c c')
    (hle : ∀ i us w r r', sem' i us w = some r → sem i us w = some r' → sem' i us w = some r') :
    MStep vc sem' keep rf c c'' := by
  cases h with
  | move => exact .move
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c'' hvb hi hops hsz hsem hlen hho hcl hn =>
    cases h' with
    | @op _ _ _ _ _ _ vb2 i2 ops2 _ _ _ _ _ _ hvb2 hi2 hops2 _ hsem2 =>
      rw [hvb] at hvb2; cases hvb2
      rw [hi] at hi2; cases hi2
      rw [hops] at hops2; cases hops2
      exact .op hvb hi hops hsz (hle _ _ _ _ _ hsem2 hsem) hlen hho hcl hn

end

theorem RL.semG_inv {R : RL} {Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop} {i : MInst}
    {us : List CV} {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    (h : R.semG Ok i us w = some r) : WGuard R.F R.ctx R.X Ok i us w ∧ R.sem i us w = some r :=
  csemVG_inv h

theorem RL.semG_le {R : RL} {Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop} :
    ∀ i us w r r', R.semG Ok i us w = some r → R.sem i us w = some r' → R.semG Ok i us w = some r' := by
  intro i us w r r' h h'
  have hg := (RL.semG_inv h).1
  simp only [RL.semG, csemVG, if_pos hg]
  exact h'

/-- A `Rets` step of the guarded semantics ends the run. -/
theorem rets_mstepG {R : RL} {Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop} {b k : Nat}
    {a : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    {c' : MConf CV Arm.ArmState} {vb : VBlock} {us : List (Reg × Reg)}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.rets us))
    (h : MStep R.vc (R.semG Ok) ckeep R.rf (.run ⟨b, .op k a :: its, m, w⟩) c') :
    ∃ vals m' w', c' = .ret vals m' w' := by
  cases h with
  | op hvb' hi' hops hsz hsemG hlen hho hcl hn =>
    rw [hvb] at hvb'; cases hvb'
    rw [hi] at hi'; cases hi'
    obtain ⟨-, hsem⟩ := RL.semG_inv hsemG
    simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
    obtain ⟨rfl, rfl, rfl⟩ := hsem
    cases hn with
    | ret _ => exact ⟨_, _, _, rfl⟩

set_option maxHeartbeats 4000000 in
/-- **One step of the allocated code from `Q ∧ AInv`** that is not a restore move, with the
guarded semantics (`realizes_allCY`'s non-restore case). -/
theorem realizes_stepCY {R : RL} (hR : R.Wf) {P : Arm.ArmState → Prop}
    (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hC : CalleeOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) :
    ∀ s c c', Q R s c → AInv R c → P s → MStep R.vc (R.semG Ok) ckeep R.rf c c' →
      (∀ b src dst its m w, c = .run ⟨b, .move src dst :: its, m, w⟩ → src.isSave = false) →
      ∃ n c'', MStep R.vc (R.semG Ok) ckeep R.rf c c'' ∧ (Q R (iterN R.step n s) c'' ∧ AInv R c'') ∧
        (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.WReadsIn Ok (iterN R.step i s)) ∧
        countIn R.CallSt R.step s n = opCalls R.vc c := by
  intro s c c' hq hA hP hG hns
  have lift : ∀ c'', MStep R.vc R.sem ckeep R.rf c c'' → MStep R.vc (R.semG Ok) ckeep R.rf c c'' :=
    fun c'' h'' => MStep.guardLift h'' hG RL.semG_le
  have fin1 : ∀ Y, (∀ a, R.F a → Y a) → ((∀ a, Y a) ∨ ∃ w, Ok w Y) →
      ∀ n c'', MStep R.vc R.sem ckeep R.rf c c'' → Q R (iterN R.step n s) c'' →
      (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.ReadsInY Y (iterN R.step i s)) →
      countIn R.CallSt R.step s n = opCalls R.vc c →
      ∃ n c'', MStep R.vc (R.semG Ok) ckeep R.rf c c'' ∧ (Q R (iterN R.step n s) c'' ∧ AInv R c'') ∧
        (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.WReadsIn Ok (iterN R.step i s)) ∧
        countIn R.CallSt R.step s n = opCalls R.vc c :=
    fun Y hYF hYO n c'' hm hq' ht hc => ⟨n, c'', lift c'' hm, ⟨hq', aInv_step hR hq hA hm⟩,
      fun i hi => ⟨(ht i hi).1, Y, hYF, hYO, (ht i hi).2⟩, hc⟩
  have fin : ∀ Y, (∀ a, R.F a → Y a) → ((∀ a, Y a) ∨ ∃ w, Ok w Y) →
      ∀ n c'', MStep R.vc R.sem ckeep R.rf c c'' → Q R (iterN R.step n s) c'' →
      (∀ i < n, R.GoodXNY Y (iterN R.step i s)) → opCalls R.vc c = 0 →
      ∃ n c'', MStep R.vc (R.semG Ok) ckeep R.rf c c'' ∧ (Q R (iterN R.step n s) c'' ∧ AInv R c'') ∧
        (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.WReadsIn Ok (iterN R.step i s)) ∧
        countIn R.CallSt R.step s n = opCalls R.vc c :=
    fun Y hYF hYO n c'' hm hq' ht h0 => fin1 Y hYF hYO n c'' hm hq'
      (fun i hi => ⟨(ht i hi).1.1, (ht i hi).2⟩)
      (by rw [h0]; exact countIn_zero_of fun i hi => (ht i hi).1.2)
  have finT := fin (fun _ => True) (fun _ _ => trivial) (.inl fun _ => trivial)
  have fin1T := fin1 (fun _ => True) (fun _ _ => trivial) (.inl fun _ => trivial)
  have nil : ∀ i < 0, R.GoodXNY (fun _ => True) (iterN R.step i s) :=
    fun _ h => absurd h (Nat.not_lt_zero _)
  have hck := (lowerRFunc_ok hR.alloc).2.2
  cases hG with
  | move =>
    obtain ⟨n, hn, ht⟩ := realizes_moveNR (Y := fun _ => True) hR hq (hns _ _ _ _ _ _ rfl)
    exact finT n _ MStep.move hn ht rfl
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsemG hlen hho hcl hn =>
    obtain ⟨hguard, hsem⟩ := RL.semG_inv hsemG
    have hoc : opCalls R.vc (.run ⟨b, .op k allocs :: its, m, w⟩) = if i.isCallI then 1 else 0 := by
      simp only [opCalls, hvb, hi]
    have hoc0 : i.isCallI = false → opCalls R.vc (.run ⟨b, .op k allocs :: its, m, w⟩) = 0 :=
      fun h => by rw [hoc, h]; rfl
    have hstep : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c' :=
      MStep.op hvb hi hops hsz hsem hlen hho hcl hn
    have herrw : Arm.r .ERR w = .None := by
      have hst := q_stRel hq
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    obtain ⟨Y, hYF, hOk, hwr⟩ := hguard
    have hYO : (∀ a, Y a) ∨ ∃ w, Ok w Y := .inr ⟨w, hOk⟩
    cases hct : i.isCtl
    · -- a covered straight-line form
      have hfo := (hcov b vb k i hvb hi).resolve_left (by simp [hct])
      obtain ⟨hOS, hL⟩ := formOk_sound (F := R.F) (X := R.X) hfo
      obtain rfl := csem_ctl hct (R.sem_csem hsem)
      have hwi : i.wReads = true := by
        simp [MInst.wReads, hct]
      obtain ⟨rY, hsemY⟩ := hwr hwi
      cases hn with
      | next hk =>
        have hnc : ∀ info, i ≠ .call info := by rintro info rfl; simp [MInst.isCtl] at hct
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_op_nextNY hR hYF hq hvb hi hops hsz hsem hsemY hlen
          hk hOS hL
          (fun ha hasg hl hw he hal hs env => formOk_reads hfo hops ha hasg hl hw he hal hs env)
          (csem_next_world' (R.sem_csem hsem) hnc herrw)
        exact fin Y hYF hYO n c'' hm hq' ht
          (hoc0 (by cases i <;> first | rfl | simp [MInst.isCtl] at hct))
    · cases i <;> simp only [MInst.isCtl, reduceCtorEq] at hct
      case call info =>
        have hc : ctl = .next := by
          have hsem := R.sem_csem hsem
          simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
          obtain ⟨_, -, -, -, h⟩ := hsem; exact h.symm
        subst hc
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht, i0, hi0, hc0, hnc⟩ := realizes_callNR (Y := fun _ => True)
            hR hC hP hq hvb hi hops hsz hsem hlen hk
          exact fin1T n c'' hm hq' ht (by rw [hoc]; exact countIn_one_of hi0 hc0 hnc)
      case args ds => exact finT 0 c' hstep (realizes_args hR hq hA hvb hi hstep) nil (hoc0 rfl)
      case rets us =>
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        cases hn with
        | ret _ => exact finT 0 _ hstep trivial nil (hoc0 rfl)
      case loadExtNameGot rd nm =>
        obtain ⟨d, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_symAddrNR (Y := fun _ => True) hR hq hvb hi
            (.inl ⟨d, nm, rfl⟩) hops hsz hsem hlen hk
          exact finT n c'' hm hq' ht (hoc0 rfl)
      case loadExtNameNear rd nm off =>
        obtain ⟨d, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_symAddrNR (Y := fun _ => True) hR hq hvb hi
            (.inr ⟨d, nm, off, rfl⟩) hops hsz hsem hlen hk
          exact finT n c'' hm hq' ht (hoc0 rfl)
      case jump l =>
        obtain ⟨n, hq', ht⟩ := realizes_gotoNR (Y := fun _ => True) hR hq hvb hi (.inl ⟨l, rfl⟩) hstep
        exact finT n c' hstep hq' ht (hoc0 rfl)
      case condBr t e kk =>
        obtain ⟨n, hq', ht⟩ := realizes_gotoNR (Y := fun _ => True) hR hq hvb hi
          (.inr (.inl ⟨t, e, kk, rfl⟩)) hstep
        exact finT n c' hstep hq' ht (hoc0 rfl)
      case testBitAndBranch kd t e rn bit =>
        obtain ⟨n, hq', ht⟩ := realizes_gotoNR (Y := fun _ => True) hR hq hvb hi
          (.inr (.inr ⟨kd, t, e, rn, bit, rfl⟩)) hstep
        exact finT n c' hstep hq' ht (hoc0 rfl)
      case trapIf kk code =>
        by_cases hh : ∃ w'', c' = .halt w''
        · obtain ⟨w'', rfl⟩ := hh
          exact finT 0 _ hstep trivial nil (hoc0 rfl)
        · obtain ⟨n, hq', ht⟩ := realizes_trapIf_nextNR (Y := fun _ => True) hR hq hvb hi hstep
            (fun w'' e => hh ⟨w'', e⟩)
          exact finT n c' hstep hq' ht (hoc0 rfl)
      case udf code =>
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        cases hn with
        | halt => exact finT 0 _ hstep trivial nil (hoc0 rfl)
      case emitIsland nb => exact finT 0 c' hstep (realizes_island hR hq hvb hi hstep) nil (hoc0 rfl)
      case jtSequence d ts ridx t1 t2 =>
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_jtNR (Y := fun _ => True) hR hq hvb hi hstep
        exact finT n c'' hm hq' ht (hoc0 rfl)
      case atomicRmwLoop ty op fl ra ro rd r1 r2 =>
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_rmwLoopNY hR hq hvb hi hstep fun ops' hops' => by
          rw [hops] at hops'; cases hops'; exact hwr rfl
        exact fin Y hYF hYO n c'' hm hq' ht (hoc0 rfl)
      case atomicCasLoop ty fl ra re rx rd r1 =>
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_casLoopNY hR hq hvb hi hstep fun ops' hops' => by
          rw [hops] at hops'; cases hops'; exact hwr rfl
        exact fin Y hYF hYO n c'' hm hq' ht (hoc0 rfl)
      case tryCall info ti =>
        have hc : ctl = .goto ti.handlers.length := by
          have hsem := R.sem_csem hsem
          simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
          obtain ⟨_, -, -, -, h⟩ := hsem; exact h.symm
        subst hc
        cases hn with
        | goto hk1 hsucc hitems =>
          obtain ⟨n, c'', hm, hq', ht, i0, hi0, hc0, hnc⟩ := realizes_tryCallNR (Y := fun _ => True)
            hR hC (hT (hasTryCall_of_mem hvb hi)) hP hq hvb hi hops hsz hsem hlen hk1 hsucc hitems rfl
          exact fin1T n c'' hm hq' ht (by rw [hoc]; exact countIn_one_of hi0 hc0 hnc)
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
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_tlsNR (Y := fun _ => True) hR
            (hTls (hasTls_of_mem hvb hi)) hq hvb hi hops hsz hsem hlen hk
          exact finT n c'' hm hq' ht (hoc0 rfl)

/-- **The machine realises the allocated code** under `QA` with the guarded semantics:
`realizes_allCR` whose segments' states satisfy `WReadsIn` (the world reads of a straight-line
form or an atomic loop avoid the guard set of its step). -/
theorem realizes_allCY {R : RL} (hR : R.Wf) {P : Arm.ArmState → Prop}
    (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hC : CalleeOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) :
    RealizesCP R.vc R.rf (R.semG Ok) ckeep R.step (QA R)
      (fun u => R.GoodX u ∧ R.WReadsIn Ok u) R.CallSt P :=
  realizesQA_CP hR (realizes_stepCY hR Ok hC hT hTls hcov)
    (fun _ _ _ _ _ _ _ hq hs => let ⟨n, h1, h2⟩ := realizes_moveNR (Y := fun _ => True) hR hq hs
      ⟨n, h1, fun i hi => ⟨(h2 i hi).1.1, fun _ => True, fun _ _ => trivial, .inl fun _ => trivial,
        (h2 i hi).2⟩, countIn_zero_of fun i hi => (h2 i hi).1.2⟩)
    (fun _ _ _ _ _ _ _ _ _ hvb hi h => rets_mstepG hvb hi h)

/-- **`realizes_allCY` with the body `sp` at the contract's states.** -/
theorem realizes_allC_spY {R : RL} (hR : R.Wf) {P : Arm.ArmState → Prop}
    (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hC : CalleeOkGP (fun u => P u ∧ spOf u = R.spB) R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H
      R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGP (fun u => P u ∧ spOf u = R.spB) R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H
        R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) :
    RealizesCP R.vc R.rf (R.semG Ok) ckeep R.step (QA R)
      (fun u => R.GoodX u ∧ R.WReadsIn Ok u) R.CallSt P := by
  intro s c c' hqa hP h
  have hsp : spOf s = R.spB := by
    cases c with
    | run st => obtain ⟨b, its, m, w⟩ := st; obtain ⟨mt, hq⟩ := qa_q hqa; exact (q_stRel hq).sp
    | _ => cases h
  exact realizes_allCY hR Ok hC hT hTls hcov s c c' hqa ⟨hP, hsp⟩ h

end Backend.Proof
