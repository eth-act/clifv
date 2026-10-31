import FV.E2E.RegLevelTwoRunW
import FV.E2E.RegLevelCorrectPRSY
import FV.E2E.BackendWorldI

/-!
# Two activations along a paired VCode run, at the prophecy level (SEM1 #537, item (3))

`RL.twoRunC` from the allocation checker (`checkAlloc`) and two activation entries with their
prophecies (`ActEntryPR`, as `backend_correct_worldPRIY` consumes them): the activation `R`
(`actRL`, entered at `s`, kept set `G`, external semantics `XI`) and `R` entered at `t0` (kept set
`G'`, external semantics `XI'`), along one pair VCode run of the allocated code's counted guarded
semantics from one vreg file.

* **`RL.twoRunPR`**.
-/

namespace Backend.Proof

open Backend E2E

set_option maxHeartbeats 2000000 in
/-- **Two activations along a returning pair VCode run, from two `ActEntryPR` entries** (module
doc; the lock premises are `RL.twoRunC`'s). -/
theorem RL.twoRunPR {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {k : Nat}
    (hcheck : checkAlloc vcp rf = .ok ()) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb)
    {lm : Std.HashMap Lbl Nat} (hlm : labelOffsets fa.lines = .ok lm) {body : List Line}
    {psF : PState} (hpsF : blocksLinesE ⟨fa.k, af.slotBase⟩ af af.blocks.toList {} = .ok (body, psF))
    {XI XI' : ExtSemI} {H : ArmHooks} {K : Nat} {F F' G G' : BitVec 64 → Prop}
    {base ra ra' : BitVec 64} {Kp Kp' : Nat} {cc cc' : BitVec 64} {P P' : Nat → BitVec 64 → BitVec 8}
    {Rr Rr' : Nat → Arm.ArmState} {s t0 w₀ w₀' : Arm.ArmState}
    (he : ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P Rr s w₀)
    (he' : ActEntryPR vcp rf af fa fb K F' G' XI' H base ra' Kp' cc' P' Rr' t0 w₀')
    {R : RL} (hR : R = actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp))
    (hcov : FormsCovered R.ctx R.vc) (ρ₀ : Nat → CV)
    (OkG OkG' : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (KJ : MConf CV Arm.ArmState → MConf CV Arm.ArmState → Prop)
    (LB : MConf CV Arm.ArmState → MConf CV Arm.ArmState → Arm.ArmState → Arm.ArmState → Prop)
    (OkS OkS' : MConf CV Arm.ArmState → MConf CV Arm.ArmState →
      Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hG : ∀ n c c' d, KJ c c' → MStep R.vc (({ R with X := XI.at n } : RL).semG OkG) ckeep R.rf c d →
      MStep R.vc (({ R with X := XI.at n } : RL).semG (OkS c c')) ckeep R.rf c d)
    (hG' : ∀ n c c' d, KJ c c' →
      MStep R.vc (({ R with s0 := t0, G := G', X := XI'.at n } : RL).semG OkG') ckeep R.rf c' d →
      MStep R.vc (({ R with s0 := t0, G := G', X := XI'.at n } : RL).semG (OkS' c c')) ckeep R.rf
        c' d)
    (Lk : MConf CV Arm.ArmState → MConf CV Arm.ArmState → Nat → Arm.ArmState → Arm.ArmState → Prop)
    (hLpc : ∀ c c' i u u', Lk c c' i u u' → Arm.r .PC u = Arm.r .PC u')
    (hstart : ∀ c c' s s', KJ c c' → LB c c' s s' → Lk c c' 0 s s')
    (hstep : ∀ n n' c c' i u u', KJ c c' →
      (({ R with X := XI.at n } : RL).GoodX u ∧
        ({ R with X := XI.at n } : RL).WReadsIn (OkS c c') u) →
      (({ R with s0 := t0, G := G', X := XI'.at n' } : RL).GoodX u' ∧
        ({ R with s0 := t0, G := G', X := XI'.at n' } : RL).WReadsIn (OkS' c c') u') →
      Lk c c' i u u' → Lk c c' (i + 1) (({ R with X := XI.at 0 } : RL).step u)
        (({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step u'))
    (hend : ∀ c c' d d' i u u', KJ c c' → KJ d d' → MConf.ShapeEq d d' →
      (∃ W : Nat × PState × List Line, QWA R u W.1 W.2.1 W.2.2 d ∧
        QWA ({ R with s0 := t0, G := G' } : RL) u' W.1 W.2.1 W.2.2 d') →
      Lk c c' i u u' → LB d d' u u')
    {PI : VConf CV (Arm.ArmState × Nat) → VConf CV (Arm.ArmState × Nat) → Prop}
    (hK : ∀ (ckc : CheckCtx) (ins : Array (Option AState)) (a0 : AState),
      CheckedAt R.vc R.rf ckc ins a0 → ∀ e e' x x',
      Match ckc ins ckeep (fun r => locVal R.fr (iterN ({ R with X := XI.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) R.s0) (.reg r)) e x →
      Match ckc ins ckeep (fun r => locVal R.fr (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } :
        RL).step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) t0) (.reg r)) e' x' →
      PI x x' → KJ (e.mapW Prod.fst) (e'.mapW Prod.fst))
    (hpro : LB
      (MConf.init R.rf (locVal R.fr (iterN ({ R with X := XI.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) R.s0)) w₀)
      (MConf.init R.rf (locVal R.fr (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) t0)) w₀')
      (iterN ({ R with X := XI.at 0 } : RL).step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) R.s0)
      (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) t0))
    {x x' : VConf CV (Arm.ArmState × Nat)} {vals vals' : List CV} {wr wr' : Arm.ArmState × Nat}
    (hp : Star (PStep R.vc (csemVIG R.gv R.F R.ctx XI OkG)
      (csemVIG R.gv ({ R with s0 := t0, G := G' } : RL).F R.ctx XI' OkG') PI)
      (VConf.init ρ₀ (w₀, 0), VConf.init ρ₀ (w₀', 0)) (x, x'))
    (hpi0 : PI (VConf.init ρ₀ (w₀, 0)) (VConf.init ρ₀ (w₀', 0))) (hpix : PI x x')
    (hy : PStep R.vc (csemVIG R.gv R.F R.ctx XI OkG)
      (csemVIG R.gv ({ R with s0 := t0, G := G' } : RL).F R.ctx XI' OkG') PI (x, x')
      (.ret vals wr, .ret vals' wr')) :
    ∃ N e e',
      (∀ i < (prologueSteps R.af.saves R.af.frameSize R.af.isCaller),
        ({ R with X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with X := XI.at 0 } : RL).step i R.s0) ∧
        ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step i t0)) ∧
      (∀ i < N, ∃ c c' j, Lk c c' j
        (iterN ({ R with X := XI.at 0 } : RL).step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + i) R.s0)
        (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + i) t0)) ∧
      JR R ({ R with s0 := t0, G := G' } : RL) KJ LB
        (iterN ({ R with X := XI.at 0 } : RL).step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N) R.s0) e
        (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N) t0) e' ∧
      (∀ i < R.retLen,
        ({ R with X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with X := XI.at 0 } : RL).step
            (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N + i) R.s0) ∧
        ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
            (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N + i) t0)) ∧
      Arm.r .PC (iterN ({ R with X := XI.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N + R.retLen) R.s0) = ra ∧
      Arm.r .PC (iterN ({ R with s0 := t0, G := G', X := XI'.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N + R.retLen) t0) = ra' := by
  subst hR
  obtain ⟨-, -, -, -, hk⟩ := emitFunc_ok hemit
  subst hk
  obtain ⟨ckc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  have hF := he.hF
  have hF' := he'.hF
  subst hF hF'
  exact RL.twoRunC (R := actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp)) (t0 := t0)
    (G' := G') (XI := XI) (XI' := XI')
    (fun _ => ⟨⟨ckc, ins, a0, hat, entryOk_of_le hle⟩, halloc, hemit, hlayout, hlm,
      by show 4 * fb.words.size ≤ 2 ^ 64; have := he.abi.fits; omega, he.stack, ⟨body, hpsF⟩,
      he.abi.program, he.gfree⟩)
    (fun _ => ⟨⟨ckc, ins, a0, hat, entryOk_of_le hle⟩, halloc, hemit, hlayout, hlm,
      by show 4 * fb.words.size ≤ 2 ^ 64; have := he'.abi.fits; omega, he'.stack, ⟨body, hpsF⟩,
      he'.abi.program, he'.gfree⟩)
    hat ρ₀ (fun _ => Inv_mono hle Inv_entryState) he.abi he'.abi he.body he'.body OkG OkG'
    (fun n => (he.calls n).mono fun _ h => ⟨onCallPR_of he.proph he.regp h.1, h.2⟩)
    (fun h n => (he.tries h n).mono fun _ h => ⟨onCallPR_of he.proph he.regp h.1, h.2⟩) he.tls
    (fun n => (he'.calls n).mono fun _ h => ⟨onCallPR_of he'.proph he'.regp h.1, h.2⟩)
    (fun h n => (he'.tries h n).mono fun _ h => ⟨onCallPR_of he'.proph he'.regp h.1, h.2⟩) he'.tls
    hcov KJ LB OkS OkS' hG hG' Lk hLpc hstart hstep hend (hK ckc ins a0 hat) hpro hp hpi0 hpix hy

end Backend.Proof
