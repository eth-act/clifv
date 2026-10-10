import FV.E2E.RegLevelCorrect
import FV.Backend.Proof.DeadCleanupAdapter

namespace Backend.Proof
open Backend Backend.DeadCleanup

/-- Only proof bookkeeping changes: pure producers leave the abstract world
unchanged, while calls and other effects keep the existing activation semantics. -/
noncomputable def valueSemV (gv : Nat → String → Prop) (F : BitVec 64 → Prop)
    (ctx : FnCtx) (X : ExtSem) : Sem :=
  fun i us w => if pureForm i then mspec ctx.slotBase i us w else csemV gv F ctx X i us w

noncomputable def RL.valueSem (R : RL) : Sem := valueSemV R.gv R.F R.ctx R.X

private theorem valueSemV_bot (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    valueSemV (fun _ _ => False) F ctx X = valueSem F ctx X := by
  funext i us w
  simp [valueSemV, valueSem, csemV_bot]

private theorem q_world_change {R : RL} {s : Arm.ArmState} {b : Nat} {its : List RItem}
    {m : Loc → CV} {w w' : Arm.ArmState} (hq : Q R s (.run ⟨b, its, m, w⟩))
    (hw : SameWorld R.F w w') : Q R s (.run ⟨b, its, m, w'⟩) := by
  obtain ⟨j, vb, items, pre, code, ls, ps1, ps2, T,
    hb, hi, hsplit, hc, hcode, hlines, htr, hdrop, hpc, hst⟩ := hq
  exact ⟨j, vb, items, pre, code, ls, ps1, ps2, T,
    hb, hi, hsplit, hc, hcode, hlines, htr, hdrop, hpc,
    { hst with world := hst.world.trans hw }⟩

private theorem aInv_step_sem {R : RL} {sem : Sem} (hR : R.Wf)
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

/-- The existing concrete realizer also realizes the pure value semantics.
It transports only the abstract world's scratch-register bookkeeping. -/
theorem realizes_value_all {R : RL} (hR : R.Wf)
    (hC : CalleeOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true → CalleeTryOkG R.F R.K R.G R.s0
      (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) :
    Realizes R.vc R.rf R.valueSem ckeep R.step (fun s c => Q R s c ∧ AInv R c) R.GoodX := by
  intro s c c' ⟨hq, hA⟩ hm
  have hreal := realizes_all hR hC hT hTls hcov
  cases hm with
  | move =>
    obtain ⟨n, c'', hstep, hq', ht⟩ := hreal s _ _ ⟨hq, hA⟩ MStep.move
    cases hstep with
    | move => exact ⟨n, _, MStep.move, hq', ht⟩
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hb hi hop hsz hs hl hho hcl hn =>
    by_cases hp : pureForm i = true
    · have hspec : mspec R.ctx.slotBase i
          (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = some (outs, w', ctl) := by
        simpa [RL.valueSem, valueSemV, RL.sem, hp] using hs
      obtain ⟨hw, hc⟩ := mspec_pure hp hspec
      subst w' ctl
      obtain ⟨wc, hconcrete, hworld⟩ := pure_mspec_csem (F := R.F) (X := R.X) hp hspec
      have hsem : R.sem i
          (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = some (outs, wc, .next) := by
        rw [R.sem_eq]
        · exact hconcrete
        · intro info he; subst i; simp [pureForm] at hp
        · intro info ti he; subst i; simp [pureForm] at hp
      cases hn with
      | next hk =>
        have hold : MStep R.vc R.sem ckeep R.rf
            (.run ⟨b, .op k allocs :: its, m, w⟩)
            (.run ⟨b, its, writeM m2
              ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs').filter (·.1.1.isLate)), wc⟩) :=
          MStep.op hb hi hop hsz hsem hl hho hcl (MNext.next hk)
        obtain ⟨n, c'', hactual, ⟨hq', _⟩, ht⟩ := hreal s _ _ ⟨hq, hA⟩ hold
        cases hactual with
        | @op _ _ _ _ _ _ vb' i' ops' os os' ww ct m3 cc hb' hi' hop' hsz' hsem' hl' hho' hcl' hn' =>
          rw [hb] at hb'; cases hb'
          rw [hi] at hi'; cases hi'
          rw [hop] at hop'; cases hop'
          rw [hsem] at hsem'; cases hsem'
          cases hn' with
          | next hk' =>
            have hnew : MStep R.vc R.valueSem ckeep R.rf
                (.run ⟨b, .op k allocs :: its, m, w⟩)
                (.run ⟨b, its, writeM m3
                  ((((ops.zip allocs).toList.filter (·.1.isDef)).zip os').filter (·.1.1.isLate)), w⟩) :=
              MStep.op hb hi hop hsz hs hl hho' hcl' (MNext.next hk')
            exact ⟨n, _, hnew, ⟨q_world_change hq' hworld, aInv_step_sem hR hq hA hnew⟩, ht⟩
    · have hold : MStep R.vc R.sem ckeep R.rf
          (.run ⟨b, .op k allocs :: its, m, w⟩) c' :=
        MStep.op hb hi hop hsz (by simpa [RL.valueSem, valueSemV, RL.sem, hp] using hs) hl hho hcl hn
      obtain ⟨n, c'', hactual, ⟨hq', _⟩, ht⟩ := hreal s _ _ ⟨hq, hA⟩ hold
      cases hactual with
      | @op _ _ _ _ _ _ vb' i' ops' os os' ww ct m3 cc hb' hi' hop' hsz' hsem' hl' hho' hcl' hn' =>
        rw [hb] at hb'; cases hb'
        rw [hi] at hi'; cases hi'
        have hnew : MStep R.vc R.valueSem ckeep R.rf
            (.run ⟨b, .op k allocs :: its, m, w⟩) _ :=
          MStep.op hb hi hop' hsz' (by simpa [RL.valueSem, valueSemV, RL.sem, hp] using hsem') hl' hho' hcl' hn'
        exact ⟨n, _, hnew, ⟨hq', aInv_step_sem hR hq hA hnew⟩, ht⟩

end Backend.Proof
