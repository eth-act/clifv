import FV.E2E.BackendTwoRunT
import FV.E2E.LinkArmStepLine
import FV.E2E.ExecWrites

/-!
# The machine lock of two activations (SEM1 #537, `docs/plans/uninit.md` §5.9, machine lock)

The lock-step premises of `backend_twoRunPRIYT` at a concrete lock: two activations of one
compiled function, one entered with world `w₀`, the other with `w₀'`, the same outside `F ∪ D`,
run in lock-step equal but for `x30` and the bytes of

  `Zc c c' a := ¬ FrameRd false a ∧ ¬ JTByte a ∧ ¬ StackBelow K spB a ∧ (F a ∨ WDiff c c' a)`

(`RL.Zc`): outside the activation's own frame bytes but its saved-LR word, outside the jump
tables, outside the callees' dead stack below the body's `sp` (equal at entry by `EntryAgree`,
written only by the callees, which keep it equal by the call premise: the caller's return
agreement needs it), and in `F` or where the two VCode worlds of the current configurations
differ. The reads of the body avoid `Zc`: a world read is outside a guard set containing `F` and
the difference set (`OkDiff`), a frame read is of the frame but its saved-LR word, a table read
is code.

* `RL.JTByte`, `MConf.WDiff`, `RL.Zc`, `OkDiff`;
* `readsAvoid_stepiEvs`, `RL.notZc_of_readInY`, `stEqOutX_lineZ`, `rdOk_X`,
  `mstep_guard_of_match`, `pGuard_of_stepPair`, `mstep_okDiff_fst`, `mstep_okDiff_snd`, `KJL`,
  `QW.stRel`, `QWA.stRel`, `stEqOutX_zc_end`;
* **`backend_twoRunL`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **A byte of a jump table** (a `.word` line) of the activation's code. -/
def _root_.Backend.Proof.RL.JTByte (R : RL) (a : BitVec 64) : Prop :=
  ∃ j tg bs, R.L[j]? = some (.word tg bs) ∧ ∃ i < 4, a = R.pcOf j + BitVec.ofNat 64 i

/-- **The bytes where the worlds of two configurations differ** (everything when one is no run
configuration). -/
def _root_.Backend.MConf.WDiff : MConf CV Arm.ArmState → MConf CV Arm.ArmState →
    BitVec 64 → Prop
  | .run ms, .run ms' => fun a => ms.w.mem a ≠ ms'.w.mem a
  | _, _ => fun _ => True

/-- **The lock set** at configurations `c`, `c'` (module doc). -/
def _root_.Backend.Proof.RL.Zc (R : RL) (c c' : MConf CV Arm.ArmState) (a : BitVec 64) : Prop :=
  ¬ R.FrameRd false a ∧ ¬ R.JTByte a ∧ ¬ StackBelow R.K R.spB a ∧ (R.F a ∨ MConf.WDiff c c' a)

/-- **The guard of the lock**: a set containing `F` and the bytes where the worlds of `c`, `c'`
differ. -/
def OkDiff (F : BitVec 64 → Prop) (c c' : MConf CV Arm.ArmState) :
    Arm.ArmState → (BitVec 64 → Prop) → Prop :=
  fun _ Y => (∀ a, F a → Y a) ∧ ∀ a, MConf.WDiff c c' a → Y a

/-- The read events of `stepi` are those of the decoded instruction. -/
theorem readsAvoid_stepiEvs {Z : BitVec 64 → Prop} {t : Arm.ArmState}
    (h : ∀ a, Concurrency.ArmFoot.decodeAt t = some a → ReadsAvoid Z (Concurrency.ArmInstFoot.instEvs a t)) :
    ReadsAvoid Z (stepiEvs t) := by
  unfold stepiEvs
  split
  · split
    · intro e he; simp at he
    · rename_i w hw
      split
      · intro e he; simp at he
      · rename_i a ha
        exact h a (by
          simp only [Concurrency.ArmFoot.decodeAt]
          have hw' : Arm.fetch_inst (Arm.r .PC t) t = some w := hw
          rw [hw']; exact ha)
  · intro e he; simp at he


/-- **A located read guarded by a set containing the difference set is outside the lock set.** -/
theorem RL.notZc_of_readInY {R : RL} {Y : BitVec 64 → Prop} {c c' : MConf CV Arm.ArmState}
    {a : BitVec 64} (h : R.ReadInY Y false a) (hY : ∀ b, MConf.WDiff c c' b → Y b) :
    ¬ R.Zc c c' a := by
  rintro ⟨hfr, hjt, -, hFD⟩
  rcases h with hj | hf | ⟨hF, hYa⟩
  · exact hjt hj
  · exact hfr hf
  · rcases hFD with h1 | h1
    · exact hF h1
    · exact hYa (hY _ h1)

theorem insn_hooked_cases {x : Insn} (h : x.hooked = true) :
    (∃ n, x = .bl n) ∨ (∃ r, x = .blr r) ∨ (∃ rd n, x = .adrpGot rd n) ∨
      (∃ a b c, x = .ldrGotLo12 a b c) ∨ (∃ rd n off, x = .adrp rd n off) ∨
      (∃ a b c d, x = .addLo12 a b c d) ∨ (∃ a b, x = .adrpTlsDesc a b) ∨
      (∃ a b c, x = .ldrTlsDescLo12 a b c) := by
  cases x <;> simp_all [Insn.hooked]

/-- **One step of the lock at an instruction line** that is no `ret` and no frame-record
line (`stEqOutX_line` with the reads needed of unhooked lines only: the GOT/`adrp` lines read no
memory, a TLS hook and a call hook keep the lock by premise). -/
theorem stEqOutX_lineZ {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {fb : FnBin}
    {lm : Std.HashMap Lbl Nat} {base : BitVec 64} {Z : BitVec 64 → Prop} {s t : Arm.ArmState}
    {x : Insn} (ht : OnLine fa fb lm base t x) (hc : fa.x30Free lm = true)
    (hx : x.x30Exempt = true → (∃ n, x = .bl n) ∨ ∃ r', x = .blr r')
    (h : StEqOutX Z s t) (hZ : x.hooked = false → ReadsAvoid Z (stepiEvs t))
    (hcall : ((∃ n, x = .bl n) ∨ ∃ r', x = .blr r') → ∀ d, StEqOutX Z (H.call d s) (H.call d t))
    (htls : ∀ n r', (∃ a b c, x = .ldrTlsDescLo12 a b c) →
      StEqOutX Z (H.tls n r' s) (H.tls n r' t)) :
    StEqOutX Z (ArmStepX X H fa s) (ArmStepX X H fa t) := by
  cases hE : x.x30Exempt with
  | true => exact stEqOutX_line_call ht (hx hE) h (hcall (hx hE))
  | false =>
    cases hk : x.hooked with
    | false => exact stEqOutX_line_free ht hc hE h (hZ hk) htls
    | true =>
      have hpb : progBase s = progBase t := by simp only [progBase, h.2.1]
      have hpc' : Arm.r .PC s = Arm.r .PC t := h.1 .PC (by simp)
      have hi := ht.insnAt_eq
      rcases insn_hooked_cases hk with ⟨n, rfl⟩ | ⟨r', rfl⟩ | ⟨rd, n, rfl⟩ | ⟨a, b, c, rfl⟩ |
          ⟨rd, n, off, rfl⟩ | ⟨a, b, c, d, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, c, rfl⟩
      · simp [Insn.x30Exempt] at hE
      · simp [Insn.x30Exempt] at hE
      · simp only [ArmStepX, hpb, hpc', hi]
        exact stEqOutX_w (stEqOutX_w h _ _) _ _
      · simp only [ArmStepX, hpb, hpc', hi]
        exact stEqOutX_w h _ _
      · simp only [ArmStepX, hpb, hpc', hi]
        exact stEqOutX_w (stEqOutX_w h _ _) _ _
      · simp only [ArmStepX, hpb, hpc', hi]
        exact stEqOutX_w h _ _
      · simp only [ArmStepX, hpb, hpc', hi]
        exact stEqOutX_w h _ _
      · simp only [ArmStepX, hpb, hpc', hi]
        exact htls _ _ ⟨_, _, _, rfl⟩

/-- **The reads of a load form do not depend on the external semantics.** -/
theorem rdOk_X {Y : BitVec 64 → Prop} {ctx : FnCtx} {X X' : ExtSem} {i : MInst} {us : List CV}
    {w : Arm.ArmState} (h : RdOk Y ctx X i us w) : RdOk Y ctx X' i us w := by
  rcases h with ⟨r, hr⟩ | h
  · cases hlf : i.loadForm
    · exact .inr hlf
    · left
      refine ⟨r, ?_⟩
      cases i <;> simp only [MInst.loadForm, reduceCtorEq, Bool.false_eq_true] at hlf <;> exact hr
  · exact .inr h

/-- **The guard of an allocated step from the pair step's**: an allocated op step related by
`Match` to a VCode configuration whose instruction's reads avoid a set `Y ⊇ F ∪ D` is a step of
the semantics guarded by `F ∪ D`. -/
theorem mstep_guard_of_match {vc : VCode} {rf : RFunc} {ckc : CheckCtx}
    {ins : Array (Option AState)} {a0 : AState} (hck : CheckedAt vc rf ckc ins a0)
    {r₀ : Reg → CV} {gv : Nat → String → Prop} {F D : BitVec 64 → Prop} {ctx : FnCtx}
    {X : ExtSem} {b k : Nat} {ρ : Nat → CV} {its : List RItem} {m : Loc → CV}
    {w : Arm.ArmState} {n : Nat}
    (hm : MatchRun ckc ins ckeep r₀ ⟨b, its, m, (w, n)⟩ ⟨b, k, ρ, (w, n)⟩)
    (hY : ∀ vb i ops, vc.blocks[b]? = some vb → vb.insts[k]? = some i → i.operands = .ok ops →
      ∃ Y, (∀ a, F a → Y a) ∧ (∀ a, D a → Y a) ∧
        ∀ X', RdOk Y ctx X' i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w)
    {d : MConf CV Arm.ArmState}
    (h : MStep vc (csemVGS gv F ctx X (fun _ Y => Y = F)) ckeep rf (.run ⟨b, its, m, w⟩) d) :
    MStep vc (csemVGS gv F ctx X (fun _ Y => (∀ a, F a → Y a) ∧ ∀ a, D a → Y a)) ckeep rf
      (.run ⟨b, its, m, w⟩) d := by
  cases h with
  | move => exact .move
  | @op _ k2 allocs its' _ _ vb i ops outs outs' w' ctl m2 _ hvb hi hops hsz hsem hlen hho hcl hn =>
    obtain ⟨-, -, vb', a, out, hvb', hrun, hinv, -⟩ := hm
    rw [hck.vc_eq, hvb] at hvb'
    cases hvb'
    obtain ⟨-, hk, i', ops', a', hi', hops', hstep, -⟩ := runItems_op hrun
    subst hk
    rw [hi] at hi'
    cases hi'
    rw [hops] at hops'
    cases hops'
    obtain ⟨-, huse, -⟩ := op_sound hstep hinv hlen hho hcl
    obtain ⟨Y, hYF, hYD, hrd⟩ := hY vb i ops hvb hi hops
    obtain ⟨-, hs⟩ := csemVGS_inv hsem
    refine .op hvb hi hops hsz ?_ hlen hho hcl hn
    have hg : WGuardS F ctx X (fun _ Y => (∀ a, F a → Y a) ∧ ∀ a, D a → Y a) i
        (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w :=
      ⟨Y, hYF, ⟨hYF, hYD⟩, fun _ => by rw [huse]; exact hrd X⟩
    simp only [csemVGS, if_pos hg]
    exact hs

/-- The pair guard at a paired step from `pc` gives `mstep_guard_of_match`'s guard on each
world. -/
theorem pGuard_of_stepPair {vc : VCode} {semP : ExtSem → Sem} {F : BitVec 64 → Prop}
    {ctx : FnCtx} {XI : ExtSemI} {b k : Nat} {ρ : Nat → CV} {w w' : Arm.ArmState} {n : Nat}
    {y : VConf CV ((Arm.ArmState × Arm.ArmState) × Nat)}
    (hy : VStep vc (pairDI semP F ctx XI) (.run ⟨b, k, ρ, ((w, w'), n)⟩) y) :
    ∀ vb i ops, vc.blocks[b]? = some vb → vb.insts[k]? = some i → i.operands = .ok ops →
      PGuard F ctx (XI.at n) i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) (w, w') := by
  intro vb i ops hvb hi hops
  cases hy with
  | step hvb' hi' hops' hsem _ _ =>
    rw [hvb] at hvb'; cases hvb'
    rw [hi] at hi'; cases hi'
    rw [hops] at hops'; cases hops'
    obtain ⟨hs, -⟩ := ISem.counted_some hsem
    exact (pairSemD_sub hs).1

/-- **The first activation's steps at a paired configuration are guarded by the difference
set.** -/
theorem mstep_okDiff_fst {vc : VCode} {rf : RFunc} {ckc : CheckCtx}
    {ins : Array (Option AState)} {a0 : AState} (hck : CheckedAt vc rf ckc ins a0)
    {r₀ r₀' : Reg → CV} {gv : Nat → String → Prop} {semP : ExtSem → Sem} {F : BitVec 64 → Prop}
    {ctx : FnCtx} {XI : ExtSemI} {X : ExtSem}
    {e e' : MConf CV (Arm.ArmState × Nat)} {pc : VConf CV ((Arm.ArmState × Arm.ArmState) × Nat)}
    (hm : Match ckc ins ckeep r₀ e (pc.mapW pairFst))
    (hm' : Match ckc ins ckeep r₀' e' (pc.mapW pairSnd))
    (hp : StepOrRet vc (pairDI semP F ctx XI) pc) {d : MConf CV Arm.ArmState}
    {Fs : BitVec 64 → Prop} (hFs : Fs = F)
    (h : MStep vc (csemVGS gv Fs ctx X (fun _ Y => Y = F)) ckeep rf (e.mapW Prod.fst) d) :
    MStep vc (csemVGS gv Fs ctx X (OkDiff F (e.mapW Prod.fst) (e'.mapW Prod.fst))) ckeep rf
      (e.mapW Prod.fst) d := by
  subst hFs
  rcases hp with ⟨y, hy⟩ | ⟨vals, wr, rfl⟩
  · obtain ⟨b, k, ρ, ⟨⟨w, w'⟩, n⟩⟩ | _ | _ := pc
    · obtain ⟨⟨b1, its, m, ⟨w1, n1⟩⟩⟩ | _ | _ := e
      · obtain ⟨⟨b2, its2, m2, ⟨w2, n2⟩⟩⟩ | _ | _ := e'
        · obtain ⟨hb, hw, hrest⟩ := hm
          obtain ⟨hb2, hw2, -⟩ := hm'
          simp only [VConf.mapW, pairFst, pairSnd, Prod.mk.injEq] at hb hw hb2 hw2
          obtain ⟨rfl, rfl⟩ := hw
          obtain ⟨rfl, rfl⟩ := hw2
          subst hb hb2
          exact mstep_guard_of_match hck (D := MConf.WDiff _ _) ⟨rfl, rfl, hrest⟩
            (fun vb i ops hvb hi hops => by
              obtain ⟨Y, hYF, hYD, h1, -⟩ := pGuard_of_stepPair hy vb i ops hvb hi hops
              exact ⟨Y, hYF, fun a ha => hYD a ha, fun _ => rdOk_X h1⟩) h
        · exact hm'.elim
        · exact hm'.elim
      · exact hm.elim
      · exact hm.elim
    · cases hy
    · cases hy
  · obtain ⟨⟨b1, its, m, w1⟩⟩ | _ | _ := e
    · exact hm.elim
    · cases h
    · cases h

/-- **The second activation's steps at a paired configuration are guarded by the difference
set.** -/
theorem mstep_okDiff_snd {vc : VCode} {rf : RFunc} {ckc : CheckCtx}
    {ins : Array (Option AState)} {a0 : AState} (hck : CheckedAt vc rf ckc ins a0)
    {r₀ r₀' : Reg → CV} {gv : Nat → String → Prop} {semP : ExtSem → Sem} {F : BitVec 64 → Prop}
    {ctx : FnCtx} {XI : ExtSemI} {X : ExtSem}
    {e e' : MConf CV (Arm.ArmState × Nat)} {pc : VConf CV ((Arm.ArmState × Arm.ArmState) × Nat)}
    (hm : Match ckc ins ckeep r₀ e (pc.mapW pairFst))
    (hm' : Match ckc ins ckeep r₀' e' (pc.mapW pairSnd))
    (hp : StepOrRet vc (pairDI semP F ctx XI) pc) {d : MConf CV Arm.ArmState}
    {Fs : BitVec 64 → Prop} (hFs : Fs = F)
    (h : MStep vc (csemVGS gv Fs ctx X (fun _ Y => Y = F)) ckeep rf (e'.mapW Prod.fst) d) :
    MStep vc (csemVGS gv Fs ctx X (OkDiff F (e.mapW Prod.fst) (e'.mapW Prod.fst))) ckeep rf
      (e'.mapW Prod.fst) d := by
  subst hFs
  rcases hp with ⟨y, hy⟩ | ⟨vals, wr, rfl⟩
  · obtain ⟨b, k, ρ, ⟨⟨w, w'⟩, n⟩⟩ | _ | _ := pc
    · obtain ⟨⟨b1, its, m, ⟨w1, n1⟩⟩⟩ | _ | _ := e
      · obtain ⟨⟨b2, its2, m2, ⟨w2, n2⟩⟩⟩ | _ | _ := e'
        · obtain ⟨hb, hw, -⟩ := hm
          obtain ⟨hb2, hw2, hrest⟩ := hm'
          simp only [VConf.mapW, pairFst, pairSnd, Prod.mk.injEq] at hb hw hb2 hw2
          obtain ⟨rfl, rfl⟩ := hw
          obtain ⟨rfl, rfl⟩ := hw2
          subst hb hb2
          exact mstep_guard_of_match hck (D := MConf.WDiff _ _) ⟨rfl, rfl, hrest⟩
            (fun vb i ops hvb hi hops => by
              obtain ⟨Y, hYF, hYD, -, h2⟩ := pGuard_of_stepPair hy vb i ops hvb hi hops
              exact ⟨Y, hYF, fun a ha => hYD a ha, fun _ => rdOk_X h2⟩) h
        · exact hm'.elim
        · exact hm'.elim
      · exact hm.elim
      · exact hm.elim
    · cases hy
    · cases hy
  · obtain ⟨⟨b2, its2, m2, w2⟩⟩ | _ | _ := e'
    · exact hm'.elim
    · cases h
    · cases h

/-- **The pair facts of the lock at two allocated configurations**: every step of either
activation from them is guarded by the difference set of their worlds (`OkDiff`). -/
def KJL (R : RL) (XI : ExtSemI) (t0 : Arm.ArmState) (G' F : BitVec 64 → Prop)
    (c c' : MConf CV Arm.ArmState) : Prop :=
  (∀ n d, MStep R.vc (({ R with X := XI.at n } : RL).semGS (fun _ Y => Y = F)) ckeep R.rf c d →
    MStep R.vc (({ R with X := XI.at n } : RL).semGS (OkDiff F c c')) ckeep R.rf c d) ∧
  (∀ n d, MStep R.vc (({ R with s0 := t0, G := G', X := XI.at n } : RL).semGS
      (fun _ Y => Y = F)) ckeep R.rf c' d →
    MStep R.vc (({ R with s0 := t0, G := G', X := XI.at n } : RL).semGS (OkDiff F c c')) ckeep
      R.rf c' d)

/-- `QW` at a run configuration gives `StRel`. -/
theorem QW.stRel {R : RL} {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    {b : Nat} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (h : QW R s j ps1 T (.run ⟨b, its, m, w⟩)) : StRel R s m w := by
  obtain ⟨_, _, _, _, _, _, -, -, -, -, -, -, -, -, -, hst⟩ := h
  exact hst

/-- `QWA` at a run configuration gives `StRel` at some store (the machine's in a return tail). -/
theorem QWA.stRel {R : RL} {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    {b : Nat} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (h : QWA R s j ps1 T (.run ⟨b, its, m, w⟩)) : ∃ mt, StRel R s mt w := by
  rcases h with ⟨hq, -⟩ | h
  · exact ⟨m, QW.stRel hq⟩
  · simp only [RetTailW] at h
    obtain ⟨mt, -, hq, -⟩ := h
    exact ⟨mt, QW.stRel hq⟩

/-- `QWA` of an activation gives `QA` of the activation at another external semantics (the
prologue, hence the frame top `StRel.fplr` compares with, does not read it). -/
theorem QWA.qaX {R : RL} {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    {c : MConf CV Arm.ArmState} (h : QWA R s j ps1 T c) {X : ExtSem}
    (hR : ({ R with X := X } : RL).Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0) :
    QA { R with X := X } s c :=
  (RL.QA_withX R X (RL.sP_withX (R := R) (⟨hR.check, hR.alloc, hR.emit, hR.layout, hR.lm, hR.fit,
    hR.stack, hR.psF, hR.prog0, hR.gfree⟩ : R.Wf) hent X) s c).2 h.qa

/-- **The lock carries over a segment end** (`hend`): at configurations `d`, `d'` related to the
states by `QWA`, a byte outside `Zc d d'` and inside `Zc c c'` is outside `F` where the two worlds
agree, so the states agree on it. -/
theorem stEqOutX_zc_end {R R' : RL} (hF : R'.F = R.F) {c c' d d' : MConf CV Arm.ArmState}
    {u u' : Arm.ArmState} {W : Nat × PState × List Line} (hq : QWA R u W.1 W.2.1 W.2.2 d)
    (hq' : QWA R' u' W.1 W.2.1 W.2.2 d') (h : StEqOutX (R.Zc c c') u u') :
    StEqOutX (R.Zc d d') u u' := by
  refine ⟨h.1, h.2.1, fun a ha => ?_⟩
  by_cases hz : R.Zc c c' a
  · obtain ⟨hfr, hjt, hds, -⟩ := hz
    have hn : ¬ (R.F a ∨ MConf.WDiff d d' a) := fun h' => ha ⟨hfr, hjt, hds, h'⟩
    obtain ⟨⟨b, its, m, w⟩⟩ | _ | _ := d
    · obtain ⟨⟨b', its', m', w'⟩⟩ | _ | _ := d'
      · have e1 := (QWA.stRel hq).choose_spec.world.2.1 a fun h' => hn (.inl h')
        have e2 := (QWA.stRel hq').choose_spec.world.2.1 a fun h' => hn (.inl (hF ▸ h'))
        rw [e1, e2]
        exact Classical.byContradiction fun h' => hn (.inr h')
      · exact absurd (.inr trivial) hn
      · exact absurd (.inr trivial) hn
    · exact absurd (.inr trivial) hn
    · exact absurd (.inr trivial) hn
  · exact h.2.2 a hz

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

set_option maxHeartbeats 4000000 in
/-- **Two activations of a compiled function along one CLIF run, in lock-step on the machine
lock** (module doc): `backend_twoRunPRIYT` at `Lk := StEqOutX (Zc c c')`, `KJ := KJL`,
`OkS := OkDiff F`. Premises left: the `x30` check of the code (`hx30`), that the segments of the
body hold no `ret` and no frame-record line (`hfr`), the call and TLS hooks keeping the lock
(`hcall`, `htls`, the call lines of item (2)), and the lock after the two prologues (`hpro`). -/
theorem backend_twoRunL (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hNI : ∀ s n, ReachN env p cs s n → XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg (env.only (Clif.Invoked env p s)) (f.externs.map (·.2)) (indSigs f)) (XI.at n))
    (hTls : ∀ n, XTls F (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop} (ρ₀ : Nat → CV) (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hrel' : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem
      w₀')
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hsw : SameWorld (fun b => F b ∨ D b) w₀ w₀')
    (hreg : ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r)
    (hstk : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
      w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
        w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k))
    (htr : TrapsExplicit env p cs) (fuel : Nat)
    {lm : Std.HashMap Lbl Nat} (hlm : labelOffsets fa.lines = .ok lm) {body : List Line}
    {psF : PState} (hpsF : blocksLinesE ⟨fa.k, af.slotBase⟩ af af.blocks.toList {} = .ok (body, psF))
    {H : ArmHooks} {G G' : BitVec 64 → Prop}
    {base ra ra' : BitVec 64} {Kp Kp' : Nat} {cc cc' : BitVec 64} {P P' : Nat → BitVec 64 → BitVec 8}
    {Rr Rr' : Nat → Arm.ArmState} {s t0 : Arm.ArmState}
    (he : ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P Rr s w₀)
    (he' : ActEntryPR vcp rf af fa fb K F G' XI H base ra' Kp' cc' P' Rr' t0 w₀')
    {R : RL} (hR : R = actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp))
    (hcov : FormsCovered R.ctx R.vc)
    (hx30 : fa.x30Free lm = true)
    (hfr : ∀ n Ok c i u x, ({ R with X := XI.at n } : RL).InSeg Ok c i u →
      ({ R with X := XI.at n } : RL).AtLine u x → x.x30Exempt = true → x.tlsTail = false →
      (∃ m, x = .bl m) ∨ ∃ r, x = .blr r)
    (hcall : ∀ n n' c c' i u u', ({ R with X := XI.at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with s0 := t0, G := G', X := XI.at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      ({ R with X := XI.at n } : RL).GoodX u →
      ({ R with s0 := t0, G := G', X := XI.at n' } : RL).GoodX u' →
      StEqOutX (R.Zc c c') u u' →
      ((∃ m, ({ R with X := XI.at n } : RL).AtLine u (.bl m)) ∨
        ∃ r, ({ R with X := XI.at n } : RL).AtLine u (.blr r)) →
      ∀ d, StEqOutX (R.Zc c c') (H.call d u) (H.call d u'))
    (htls : ∀ n n' c c' i u u', ({ R with X := XI.at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with s0 := t0, G := G', X := XI.at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      ({ R with X := XI.at n } : RL).GoodX u →
      ({ R with s0 := t0, G := G', X := XI.at n' } : RL).GoodX u' →
      StEqOutX (R.Zc c c') u u' →
      (∃ a b c, ({ R with X := XI.at n } : RL).AtLine u (.ldrTlsDescLo12 a b c)) →
      ∀ m r, StEqOutX (R.Zc c c') (H.tls m r u) (H.tls m r u'))
    (hpro : StEqOutX
      (R.Zc (MConf.init R.rf (locVal R.fr (iterN ({ R with X := XI.at 0 } : RL).step
          (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length R.s0)) w₀)
        (MConf.init R.rf (locVal R.fr (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length t0)) w₀'))
      (iterN ({ R with X := XI.at 0 } : RL).step (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length R.s0)
      (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length t0)) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
    ∃ N e e',
      (∀ i < (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length,
        ({ R with X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with X := XI.at 0 } : RL).step i R.s0) ∧
        ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step i t0)) ∧
      (∀ i < N, ∃ c c', StEqOutX (R.Zc c c')
        (iterN ({ R with X := XI.at 0 } : RL).step ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + i) R.s0)
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + i) t0)) ∧
      JR R ({ R with s0 := t0, G := G' } : RL) (KJL R XI t0 G' F)
        (fun d d' u u' => StEqOutX (R.Zc d d') u u')
        (iterN ({ R with X := XI.at 0 } : RL).step ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N) R.s0) e
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N) t0) e' ∧
      (∀ i < R.retLen,
        ({ R with X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with X := XI.at 0 } : RL).step
            ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N + i) R.s0) ∧
        ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
            ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N + i) t0)) ∧
      Arm.r .PC (iterN ({ R with X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N + R.retLen) R.s0) = ra ∧
      Arm.r .PC (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N + R.retLen) t0) = ra' ∧
      R.RetsAt e ∧ R.RetsAt e' := by
  intro vals cm hrun
  have hRF : R.F = F := by subst hR; exact he.hF
  have hRF' : ({ R with s0 := t0, G := G' } : RL).F = F := by subst hR; exact he'.hF
  have hfit : 4 * fb.words.size ≤ 2 ^ 64 := by have := he.abi.fits; omega
  have hlay : fa.layout = .ok fb := hc.layout
  have key := backend_twoRunPRIYT hsub hc hone htc hX hNI hTls hsym hslot ρ₀ hce hrel hrel' hargs
    hsw hreg hstk htr fuel hlm hpsF he he' hR hcov (KJL R XI t0 G' F)
    (fun d d' u u' => StEqOutX (R.Zc d d') u u') (fun c c' => OkDiff F c c')
    (fun c c' => OkDiff F c c') (fun n c c' d hK h => hK.1 n d h) (fun n c c' d hK h => hK.2 n d h)
    (fun c c' _ u u' => StEqOutX (R.Zc c c') u u') (fun _ _ _ _ _ h => h.1 .PC (by simp))
    (fun _ _ _ _ _ h => h)
    (fun n n' c c' i u u' _ hin hin' ⟨hg, hwr⟩ ⟨hg', _⟩ hl => by
      subst hR
      obtain ⟨x, ⟨j, tc, hj, hpc⟩, htl⟩ := hg.line
      have ht : OnLine fa fb lm base u x := ⟨hlay, hlm, hfit, hg.prog, hg.err, ⟨j, tc, hj, hpc⟩⟩
      have hat : ({ actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp) with X := XI.at n } :
          RL).AtLine u x := ⟨j, tc, hj, hpc⟩
      have hx := hfr n _ c i u x hin hat
      have hx' : x.x30Exempt = true → (∃ m, x = .bl m) ∨ ∃ r', x = .blr r' := fun h => hx h htl
      have hld : x.ldpFR = false := by
        cases hl2 : x.ldpFR with
        | false => rfl
        | true =>
          exfalso
          have e : x = .ldp .fp .lr (.spPostIndexed 16) := by simpa [Insn.ldpFR] using hl2
          subst e
          rcases hx' (by decide) with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
      have hZ : x.hooked = false → ReadsAvoid
          ((actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp)).Zc c c') (stepiEvs u) := by
        intro hk
        apply readsAvoid_stepiEvs
        intro a ha ev hev hdir k hk'
        obtain ⟨j', a', ha', hd⟩ := ht.decodeAt
        rw [hd, Option.some.injEq] at ha
        subst ha
        have hcov := (ExecBytes.instEvs_cover hev).1 hdir
        obtain ⟨Y, -, hYO, hrd⟩ := hwr
        have hr := hrd j x tc hj hpc hk _ a' ha' (ev.addr, ev.n) hcov k hk'
        rw [hld] at hr
        refine RL.notZc_of_readInY hr fun b hb => ?_
        rcases hYO with hall | ⟨_, -, hYD⟩
        · exact hall b
        · exact hYD b hb
      have hstep1 := stEqOutX_lineZ (X := XI.at 0) (H := H) ht hx30 hx' hl.symm hZ
        (fun hb d => (hcall n n' c c' i u u' hin hin' hg hg' hl
          (hb.imp (fun ⟨m, e⟩ => ⟨m, e ▸ hat⟩) fun ⟨r', e⟩ => ⟨r', e ▸ hat⟩) d).symm)
        (fun m r' hb => (htls n n' c c' i u u' hin hin' hg hg' hl
          (let ⟨a, b, c, e⟩ := hb; ⟨a, b, c, e ▸ hat⟩) m r').symm)
      exact hstep1.symm)
    (fun c c' d d' i u u' _ _ _ ⟨W, hq, hq'⟩ hl =>
      stEqOutX_zc_end (hRF'.trans hRF.symm) hq hq' hl)
    (fun ckc ins a0 hck e e' x x' hm hm' ⟨pc, hx, hx', hp⟩ => by
      subst hx hx' hR
      exact ⟨fun n d h => mstep_okDiff_fst hck hm hm' hp hRF h,
        fun n d h => mstep_okDiff_snd hck hm hm' hp hRF' h⟩)
    hpro vals cm hrun
  obtain ⟨N, e, e', h1, h2, h3, h4, h5, h6, h7⟩ := key
  exact ⟨N, e, e', h1, fun i hi => let ⟨c, c', _, h⟩ := h2 i hi; ⟨c, c', h⟩, h3, h4, h5, h6, h7⟩

end

end E2E
