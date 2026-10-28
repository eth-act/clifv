import FV.E2E.BackendTwoRunT
import FV.E2E.LinkArmStepLine
import FV.E2E.ExecWrites

/-!
# The machine lock of two activations (SEM1 #537, `docs/plans/uninit.md` §5.9, machine lock)

The lock-step premises of `backend_twoRunPRIYT` at a concrete lock: two activations of one
compiled function, one entered with world `w₀`, the other with `w₀'`, the same outside `F ∪ D`,
run in lock-step equal but for `x30` and the bytes of

  `Zc c c' a := ¬ FrameRd false a ∧ ¬ JTByte a ∧ (F a ∨ WDiff c c' a)`

(`RL.Zc`): outside the activation's own frame bytes but its saved-LR word, outside the jump
tables, and in `F` or where the two VCode worlds of the current configurations differ. The reads
of the body avoid `Zc`: a world read is outside a guard set containing `F` and the difference
set (`OkDiff`), a frame read is of the frame but its saved-LR word, a table read is code.

* `RL.JTByte`, `MConf.WDiff`, `RL.Zc`, `OkDiff`;
* `readsAvoid_stepiEvs`, `RL.readInY_notZc`.
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
  ¬ R.FrameRd false a ∧ ¬ R.JTByte a ∧ (R.F a ∨ MConf.WDiff c c' a)

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
  rintro ⟨hfr, hjt, hFD⟩
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
    (h : MStep vc (csemVGS gv F ctx X (fun _ Y => Y = F)) ckeep rf (e.mapW Prod.fst) d) :
    MStep vc (csemVGS gv F ctx X (OkDiff F (e.mapW Prod.fst) (e'.mapW Prod.fst))) ckeep rf
      (e.mapW Prod.fst) d := by
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
    (h : MStep vc (csemVGS gv F ctx X (fun _ Y => Y = F)) ckeep rf (e'.mapW Prod.fst) d) :
    MStep vc (csemVGS gv F ctx X (OkDiff F (e.mapW Prod.fst) (e'.mapW Prod.fst))) ckeep rf
      (e'.mapW Prod.fst) d := by
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
end E2E
