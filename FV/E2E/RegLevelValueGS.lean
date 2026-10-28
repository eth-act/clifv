import FV.E2E.RegLevelCorrectCYSF
import FV.E2E.DeadCleanupRealizes

/-!
# The guarded value semantics and its realizer with the segment's lines (SEM1 #537, cleanup path)

The register-level two-run chain (`RL.jointSegT`, …, `RL.twoRunPRTN`) runs the guarded semantics
`RL.semGS Ok` (`csemV` under the read guard `WGuardS`) of `Compiled` code. The shipped compiler
uses the cleanup path (`CompiledCleanup`), whose code runs the value semantics `valueSemV`
(`DeadCleanupRealizes.lean`: pure producers and compares by their specification `mspec`, the
other forms by `csemV`). Here the guarded value semantics, with the same guard:

* `specForm_loadForm`, `valueSemVGS`, `valueSemVIGS`, `RL.valueSemGS` (+ `_inv`, `_nspec`,
  `RL.valueSemGS_agree`, `valueSemVGS_eqF`, `valueSemVIGS_eqF`);
* `QW.world_change`, `aInv_step_anySem`, `MConf.shapeEq_rfl`;
* **`realizes_value_allCWSF`**: `realizes_allCWSF` for `RL.valueSemGS` (as `realizes_value_allC`
  is `realizes_allC` for `RL.valueSem`). Each value step is matched by an `RL.semGS` step of the
  same configuration (a specification form by its `csem` step, whose world is related to the
  value step's by `SameWorld F`, `spec_mspec_csem`), realised by the same machine segment; the
  theorem also returns that `RL.semGS` step (`d₀`, shape-equal, at the same segment length), which
  is what `RL.InSeg` (the lock step's position premise) speaks of, so the lock premises of the
  two-run chain keep their legacy form.
-/

namespace Backend.Proof

open Backend E2E Backend.DeadCleanup Backend.Proof.Driver

/-- A specification form (pure producer or compare) is not a load form. -/
theorem specForm_loadForm {i : MInst} (h : specForm i = true) : i.loadForm = false := by
  cases i <;> first | rfl | (simp [specForm, pureForm, cmpForm] at h)

open Classical in
/-- **The guarded value semantics**: `valueSemV` where `WGuardS` holds, undefined elsewhere. -/
noncomputable def valueSemVGS (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (X : ExtSem) (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop) : ISem CV Arm.ArmState :=
  fun i us w => if WGuardS F ctx X Ok i us w then valueSemV gv F ctx X i us w else none

/-- **The counted guarded value semantics.** -/
noncomputable def valueSemVIGS (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (X : ExtSemI) (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop) :
    ISem CV (Arm.ArmState × Nat) :=
  ISem.counted fun n => valueSemVGS gv F ctx (X.at n) Ok

/-- The activation's guarded value semantics. -/
noncomputable def RL.valueSemGS (R : RL) (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop) :
    ISem CV Arm.ArmState :=
  valueSemVGS R.gv R.F R.ctx R.X Ok

section
variable {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
  {Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop} {i : MInst} {us : List CV} {w : Arm.ArmState}
  {r : List CV × Arm.ArmState × Ctl}

theorem valueSemVGS_inv (h : valueSemVGS gv F ctx X Ok i us w = some r) :
    WGuardS F ctx X Ok i us w ∧ valueSemV gv F ctx X i us w = some r := by
  unfold valueSemVGS at h
  split at h
  · exact ⟨‹_›, h⟩
  · cases h

/-- Off the specification forms the guarded value semantics is the guarded one. -/
theorem valueSemVGS_nspec (hp : specForm i = false) :
    valueSemVGS gv F ctx X Ok i us w = csemVGS gv F ctx X Ok i us w := by
  simp only [valueSemVGS, csemVGS, valueSemV, hp, Bool.false_eq_true, ite_false]

end

/-- Two guarded value semantics of one activation agree where both are defined. -/
theorem RL.valueSemGS_agree {R : RL} {Ok Ok' : Arm.ArmState → (BitVec 64 → Prop) → Prop} :
    ∀ i us w r r', R.valueSemGS Ok' i us w = some r → R.valueSemGS Ok i us w = some r' →
      R.valueSemGS Ok' i us w = some r' := by
  intro i us w r r' h h'
  have e : r = r' := by
    have a := (valueSemVGS_inv h).2
    have b := (valueSemVGS_inv h').2
    rw [a] at b
    exact Option.some.inj b
  rw [h, e]

/-- **The guard at `Y := F` is no restriction**: `valueSemVGS … (fun _ Y => Y = F)` is
`valueSemV`. -/
theorem valueSemVGS_eqF (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (X : ExtSem) : valueSemVGS gv F ctx X (fun _ Y => Y = F) = valueSemV gv F ctx X := by
  funext i us w
  unfold valueSemVGS
  split
  · rfl
  · rename_i hg
    cases h : valueSemV gv F ctx X i us w with
    | none => rfl
    | some r =>
      refine absurd ⟨F, fun _ h => h, rfl, fun _ => ?_⟩ hg
      by_cases hp : specForm i = true
      · exact .inr (specForm_loadForm hp)
      · left
        refine ⟨r, csemV_sub (gv := gv) ?_⟩
        simpa [valueSemV, hp] using h

theorem valueSemVIGS_eqF (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (X : ExtSemI) :
    valueSemVIGS gv F ctx X (fun _ Y => Y = F) = ISem.counted fun n => valueSemV gv F ctx (X.at n) := by
  simp only [valueSemVIGS, valueSemVGS_eqF]

/-- `QW` admits a change of the configuration's world within `SameWorld F`. -/
theorem QW.world_change {R : RL} {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    {b : Nat} {its : List RItem} {m : Loc → CV} {w w' : Arm.ArmState}
    (hq : QW R s j ps1 T (.run ⟨b, its, m, w⟩)) (hw : SameWorld R.F w w') :
    QW R s j ps1 T (.run ⟨b, its, m, w'⟩) := by
  obtain ⟨vb, items, pre, code, ls, ps2, h1, h2, h3, h4, h5, h6, h7, h8, h9, hst⟩ := hq
  exact ⟨vb, items, pre, code, ls, ps2, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    { hst with world := hst.world.trans hw }⟩

/-- `AInv` is kept by every step of the allocated code from a `Q` state, in any semantics. -/
theorem aInv_step_anySem {R : RL} {sem : ISem CV Arm.ArmState} (hR : R.Wf)
    {s : Arm.ArmState} {c c' : MConf CV Arm.ArmState}
    (hq : Q R s c) (hA : AInv R c) (h : MStep R.vc sem ckeep R.rf c c') : AInv R c' := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  cases h with
  | @move b src dst its m w =>
    intro hb hop
    subst hb
    obtain ⟨j, vb, items, pre, -, -, -, -, -, -, hit, hsplit, -⟩ := hq
    obtain ⟨hmv, hrd⟩ := ctlCheck_before hck hit hsplit hop
    have hA' := hA rfl (by obtain ⟨a, ha⟩ := hop; exact ⟨a, List.mem_cons_of_mem _ ha⟩)
    intro r hr
    have hne : Loc.reg r ≠ dst := by
      intro e; subst e; simp [RItem.regDst] at hrd
    rw [upd_other hne]
    exact hA' r hr
  | op _ _ _ _ _ _ _ _ hn =>
    cases hn with
    | next =>
      intro hb hop
      subst hb
      obtain ⟨j, vb0, items, pre, -, -, -, -, -, -, hit, hsplit, -⟩ := hq
      have := (ctlCheck_before hck hit hsplit hop).1
      simp [RItem.isMove] at this
    | goto _ hs _ =>
      intro hb
      exact absurd hb (ctlCheck_succ hck hs)
    | ret => trivial
    | halt => trivial

theorem MConf.shapeEq_rfl {V W : Type} : ∀ c : MConf V W, MConf.ShapeEq c c
  | .run ⟨_, _, _, _⟩ => ⟨rfl, rfl⟩
  | .ret .. => trivial
  | .halt _ => trivial

set_option maxHeartbeats 4000000 in
/-- **`realizes_allCWSF` for the guarded value semantics** (module doc): besides the value step's
target `c''`, the `RL.semGS` step `d₀` the segment realises (shape-equal to `c''`, the same
segment length). -/
theorem realizes_value_allCWSF {R : RL} (hR : R.Wf) {P : Arm.ArmState → Prop}
    (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hC : CalleeOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    {c c' : MConf CV Arm.ArmState} (hq : QW R s j ps1 T c) (hA : AInv R c) (hP : P s)
    (hG : MStep R.vc (R.valueSemGS Ok) ckeep R.rf c c') :
    ∃ n c'' d₀, MStep R.vc (R.valueSemGS Ok) ckeep R.rf c c'' ∧
      MStep R.vc (R.semGS Ok) ckeep R.rf c d₀ ∧ MConf.ShapeEq d₀ c'' ∧
      MConf.ShapeEq c'' c' ∧ AInv R c'' ∧
      QW R (iterN R.step n s) (R.nextW j ps1 T c c'').1 (R.nextW j ps1 T c c'').2.1
        (R.nextW j ps1 T c c'').2.2 c'' ∧
      (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.WReadsIn Ok (iterN R.step i s)) ∧
      countIn R.CallSt R.step s n = opCalls R.vc c ∧ R.SegLenA j ps1 T c c'' s n ∧
      R.SegLenA j ps1 T c d₀ s n ∧ R.FRFree s n := by
  cases hG with
  | move =>
    obtain ⟨n, c'', hm, hsh, hA', hq', ht, hcnt, hs, hf⟩ :=
      realizes_allCWSF hR Ok hC hT hTls hcov hq hA hP MStep.move
    cases hm with
    | move => exact ⟨n, _, _, MStep.move, MStep.move, ⟨rfl, rfl⟩, hsh, hA', hq', ht, hcnt, hs, hs, hf⟩
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hb hi hop hsz hs hl hho hcl hn =>
    obtain ⟨hg, hsV⟩ := valueSemVGS_inv hs
    by_cases hp : specForm i = true
    · have hspec : mspec R.ctx.slotBase i
          (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = some (outs, w', ctl) := by
        simpa [valueSemV, hp] using hsV
      have hc := mspec_spec_next hp hspec
      subst ctl
      obtain ⟨wc, hconcrete, hworld⟩ := spec_mspec_csem (F := R.F) (X := R.X) hp hspec
      have hsem0 : R.sem i
          (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = some (outs, wc, .next) := by
        rw [R.sem_eq]
        · exact hconcrete
        · intro info he; subst i; simp [specForm, pureForm, cmpForm] at hp
        · intro info ti he; subst i; simp [specForm, pureForm, cmpForm] at hp
      have hsem : R.semGS Ok i
          (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = some (outs, wc, .next) := by
        simp only [RL.semGS, csemVGS, hg, ↓reduceIte]
        exact hsem0
      cases hn with
      | next hk =>
        have hold : MStep R.vc (R.semGS Ok) ckeep R.rf
            (.run ⟨b, .op k allocs :: its, m, w⟩)
            (.run ⟨b, its, writeM m2
              ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs').filter (·.1.1.isLate)), wc⟩) :=
          MStep.op hb hi hop hsz hsem hl hho hcl (MNext.next hk)
        obtain ⟨n, c'', hactual, -, hA', hq', ht, hcnt, hs', hf⟩ :=
          realizes_allCWSF hR Ok hC hT hTls hcov hq hA hP hold
        cases hactual with
        | @op _ _ _ _ _ _ vb' i' ops' os os' ww ct m3 cc hb' hi' hop' hsz' hsem' hl' hho' hcl' hn' =>
          rw [hb] at hb'; cases hb'
          rw [hi] at hi'; cases hi'
          rw [hop] at hop'; cases hop'
          rw [hsem] at hsem'; cases hsem'
          cases hn' with
          | next hk' =>
            have hnew : MStep R.vc (R.valueSemGS Ok) ckeep R.rf
                (.run ⟨b, .op k allocs :: its, m, w⟩)
                (.run ⟨b, its, writeM m3
                  ((((ops.zip allocs).toList.filter (·.1.isDef)).zip os').filter (·.1.1.isLate)), w'⟩) :=
              MStep.op hb hi hop hsz hs hl hho' hcl' (MNext.next hk')
            exact ⟨n, _, _, hnew, MStep.op hb hi hop hsz hsem hl hho' hcl' (MNext.next hk'),
              ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, aInv_step_anySem hR hq.q hA hnew,
              QW.world_change hq' hworld, ht, hcnt, hs', hs', hf⟩
    · have hnsp : specForm i = false := by simpa using hp
      have hsG : R.semGS Ok i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
          some (outs, w', ctl) := by
        have := hs
        simp only [RL.valueSemGS, valueSemVGS_nspec hnsp] at this
        exact this
      obtain ⟨n, c'', hactual, hsh, hA', hq', ht, hcnt, hs', hf⟩ :=
        realizes_allCWSF hR Ok hC hT hTls hcov hq hA hP (MStep.op hb hi hop hsz hsG hl hho hcl hn)
      cases hactual with
      | @op _ _ _ _ _ _ vb' i' ops' os os' ww ct m3 cc hb' hi' hop' hsz' hsem' hl' hho' hcl' hn' =>
        rw [hb] at hb'; cases hb'
        rw [hi] at hi'; cases hi'
        have hnew : MStep R.vc (R.valueSemGS Ok) ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) _ :=
          MStep.op hb hi hop' hsz' (by simp only [RL.valueSemGS, valueSemVGS_nspec hnsp]; exact hsem')
            hl' hho' hcl' hn'
        exact ⟨n, _, _, hnew, MStep.op hb hi hop' hsz' hsem' hl' hho' hcl' hn',
          MConf.shapeEq_rfl _, hsh, hA', hq', ht, hcnt, hs', hs', hf⟩

end Backend.Proof
