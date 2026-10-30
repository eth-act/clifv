import FV.E2E.BackendTwoRunLW
import FV.E2E.BackendTwoRunNPre
import FV.E2E.RegLevelTwoRunNP

/-!
# The machine lock with the contracts of the first `N` calls, the call hook told the first run's
call state (SEM1 #537, #713, #729)

`backend_twoRunLWNp`'s call premise `hcall` gets a state `u` of the first run only as `InSeg`
(reachable from *some* state related to the configuration), with an arbitrary call index `n`. At
the link a program callee's lock needs `u` to be the first run's call state of count `n` (#729).
**`backend_twoRunLWNpP`**: `backend_twoRunLWNp` whose `hcall` also receives `RL.SegFrom` of the
first run (`u` is `i` steps after a segment start `OnCall … n`, the segment's machine calls the
step's): same proof, on `RL.twoRunPRTNP`/`RL.twoRunPRTP`. The full case also concludes `RL.Good`
of both runs at every index before the return (prologue and epilogue from `GoodXNY`, the body
from the joint trace): with it `PostTrace` of both runs up to the return.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

set_option maxHeartbeats 8000000 in
/-- **`backend_twoRunLWNp` with the first run's segment start handed to `hcall`** (module doc). -/
theorem backend_twoRunLWNpP (hc : Compiled f k vc vcp rf af fa fb)
    {XI : ExtSemI} {K : Nat} {F : BitVec 64 → Prop}
    {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop} (ρ₀ : Nat → CV)
    (hsw : SameWorld (fun b => F b ∨ D b) w₀ w₀')
    {us : List (Reg × Reg)} {outs : List CV} {w : (Arm.ArmState × Arm.ArmState) × Nat}
    {b kk : Nat} {ρ : Nat → CV} {w₁ : (Arm.ArmState × Arm.ArmState) × Nat} {vb : VBlock}
    {ops : Array Operand} {outs' : List CV}
    (hs : Star (VStep vcp
      (pairDI (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI))
      (.run ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩) (.run ⟨b, kk, ρ, w₁⟩))
    (hvb : vcp.blocks[b]? = some vb) (hk : vb.insts[kk]? = some (.rets us))
    (hops : (MInst.rets us).operands = .ok ops) (hvals : outs = vuses ops ρ)
    (hsem : pairDI (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI (.rets us)
      outs w₁ = some (outs', w, .ret))
    {lm : Std.HashMap Lbl Nat} (hlm : labelOffsets fa.lines = .ok lm) {body : List Line}
    {psF : PState} (hpsF : blocksLinesE ⟨fa.k, af.slotBase⟩ af af.blocks.toList {} = .ok (body, psF))
    {H : ArmHooks} {G G' : BitVec 64 → Prop}
    {base ra ra' : BitVec 64} {Kp Kp' : Nat} {cc cc' : BitVec 64} {P P' : Nat → BitVec 64 → BitVec 8}
    {Rr Rr' : Nat → Arm.ArmState} {s t0 : Arm.ArmState} {N : Nat}
    (he : ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp cc P Rr s w₀ N)
    (he' : ActEntryPRN vcp rf af fa fb K F G' XI H base ra' Kp' cc' P' Rr' t0 w₀' N)
    {R : RL} (hR : R = actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp))
    (hcov : FormsCovered R.ctx R.vc)
    (hx30 : fa.x30Free lm = true)
    (hcall : ∀ n n' c c' i u u', ({ R with X := (XI.upTo N).at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with X := (XI.upTo N).at n } : RL).SegFrom (fun u =>
        OnCall ({ R with X := (XI.upTo N).at 0 } : RL).step R.fa R.base R.s0 n u ∧
          spOf u = R.spB) c i u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      ({ R with X := (XI.upTo N).at n } : RL).GoodX u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).GoodX u' →
      StEqOutX (R.Zc c c') u u' → (∀ a, MConf.WDiff c c' a → F a ∨ D a) →
      ∀ x d, ({ R with X := (XI.upTo N).at n } : RL).AtLine u x → LineDest x d →
      StEqOutX (R.Zc c c') (H.call d u) (H.call d u'))
    (htls : ∀ n n' c c' i u u', ({ R with X := (XI.upTo N).at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      ({ R with X := (XI.upTo N).at n } : RL).GoodX u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).GoodX u' →
      StEqOutX (R.Zc c c') u u' → (∀ a, MConf.WDiff c c' a → F a ∨ D a) →
      (∃ a b c, ({ R with X := (XI.upTo N).at n } : RL).AtLine u (.ldrTlsDescLo12 a b c)) →
      ∀ m r, StEqOutX (R.Zc c c') (H.tls m r u) (H.tls m r u'))
    (hag : EntryAgree (frameDrop af + K) s t0)
    (hx29 : Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) t0) :
    (w₁.2 ≤ N → ∃ T e e',
      (∀ i < T, ∃ c c', StEqOutX (R.Zc c c')
        (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize).length + i) R.s0)
        (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize).length + i) t0)) ∧
      JR R ({ R with s0 := t0, G := G' } : RL) (KJL R (XI.upTo N) t0 G' F)
        (fun d d' u u' => StEqOutX (R.Zc d d') u u' ∧ MConf.WIn (fun b => F b ∨ D b) d d' ∧
          MDiffIn F (fun b => F b ∨ D b) u u')
        (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize).length + T) R.s0) e
        (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize).length + T) t0) e' ∧
      Arm.r .PC (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize).length + T + R.retLen) R.s0) = ra ∧
      Arm.r .PC (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize).length + T + R.retLen) t0) = ra' ∧
      R.RetsAt e ∧ R.RetsAt e' ∧
      ∀ i < (prologueLines R.af.saves R.af.frameSize).length + T + R.retLen,
        R.Good (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step i R.s0) ∧
        ({ R with s0 := t0, G := G' } : RL).Good
          (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step i t0)) ∧
    (N < w₁.2 → ∃ T b k a its m w a' its' m' w',
      (∀ i < T, ∃ c c', StEqOutX (R.Zc c c')
        (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize).length + i) R.s0)
        (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize).length + i) t0)) ∧
      JR R ({ R with s0 := t0, G := G' } : RL) (KJL R (XI.upTo N) t0 G' F)
        (fun d d' u u' => StEqOutX (R.Zc d d') u u' ∧ MConf.WIn (fun b => F b ∨ D b) d d' ∧
          MDiffIn F (fun b => F b ∨ D b) u u')
        (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize).length + T) R.s0) (.run ⟨b, .op k a :: its, m, w⟩)
        (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize).length + T) t0) (.run ⟨b, .op k a' :: its', m', w'⟩) ∧
      countIn (RL.CallSt R) ({ R with X := (XI.upTo N).at 0 } : RL).step R.s0
        ((prologueLines R.af.saves R.af.frameSize).length + T) = N ∧
      countIn (RL.CallSt R) ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step t0
        ((prologueLines R.af.saves R.af.frameSize).length + T) = N ∧
      ∃ vb i, vcp.blocks[b]? = some vb ∧ vb.insts[k]? = some i ∧ i.isCallI = true) := by
  have heU := he.upTo
  have heU' := he'.upTo
  have hRF : R.F = F := by subst hR; exact he.hF
  have hRF' : ({ R with s0 := t0, G := G' } : RL).F = F := by subst hR; exact he'.hF
  have hRgv : R.gv = GotV vcp := by subst hR; rfl
  have hRctx : R.ctx = ⟨fa.k, af.slotBase⟩ := by subst hR; rfl
  have hfit : 4 * fb.words.size ≤ 2 ^ 64 := by have := he.abi.fits; omega
  have hlay : fa.layout = .ok fb := hc.layout
  have hFY : ∀ a, F a → F a ∨ D a := fun _ h => .inl h
  have hproS : StEqOutX
      (R.Zc (MConf.init R.rf (locVal R.fr (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
          (prologueLines R.af.saves R.af.frameSize).length R.s0)) w₀)
        (MConf.init R.rf (locVal R.fr (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } :
          RL).step (prologueLines R.af.saves R.af.frameSize).length t0)) w₀'))
      (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step (prologueLines R.af.saves R.af.frameSize).length R.s0)
      (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize).length t0) := by
    subst hR
    have hF := he.hF
    subst hF
    obtain ⟨-, -, -, -, hk⟩ := emitFunc_ok hc.emit
    subst hk
    obtain ⟨ckc, ins, hck⟩ := checked_of_checkAlloc hc.check
    obtain ⟨a0, hat, hle⟩ := hck.at
    have hW0 : ({ actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp) with
        X := (XI.upTo N).at 0 } : RL).Wf :=
      ⟨⟨ckc, ins, a0, hat, entryOk_of_le hle⟩, hc.alloc, hc.emit, hc.layout, hlm,
        by show 4 * fb.words.size ≤ 2 ^ 64; have := he.abi.fits; omega, he.stack, ⟨body, hpsF⟩,
        he.abi.program, he.gfree⟩
    exact (stEqOutX_prologueZ hW0 he.abi hx30 (fun k h8 h16 => RL.lrWord_Zc hW0 _ _ h8 h16)
      (stEqOutX_entryZ hW0 he.abi he'.abi he.body he'.body (fun _ h => h) hsw hag hx29
        (fun _ h => by exact h)).symm).symm
  have hwi0 : ∀ (m₀ m₀' : Loc → CV), MConf.WIn (fun b => F b ∨ D b)
      (MConf.init R.rf m₀ w₀) (MConf.init R.rf m₀' w₀') := by
    intro m₀ m₀' a hne
    exact Classical.byContradiction fun h => hne (hsw.2.1 a h)
  have hpro : StEqOutX
      (R.Zc (MConf.init R.rf (locVal R.fr (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
          (prologueLines R.af.saves R.af.frameSize).length R.s0)) w₀)
        (MConf.init R.rf (locVal R.fr (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } :
          RL).step (prologueLines R.af.saves R.af.frameSize).length t0)) w₀'))
      (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step (prologueLines R.af.saves R.af.frameSize).length R.s0)
      (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize).length t0) ∧
      MConf.WIn (fun b => F b ∨ D b)
        (MConf.init R.rf (locVal R.fr (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
          (prologueLines R.af.saves R.af.frameSize).length R.s0)) w₀)
        (MConf.init R.rf (locVal R.fr (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } :
          RL).step (prologueLines R.af.saves R.af.frameSize).length t0)) w₀') ∧
      MDiffIn F (fun b => F b ∨ D b)
        (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step (prologueLines R.af.saves R.af.frameSize).length R.s0)
        (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
          (prologueLines R.af.saves R.af.frameSize).length t0) :=
    ⟨hproS, hwi0 _ _, mDiffIn_of_lock hRF ⟨_, rfl⟩ ⟨_, rfl⟩ hproS (hwi0 _ _)⟩
  have hstepL : ∀ n n' c c' i u u', KJL R (XI.upTo N) t0 G' F c c' →
      ({ R with X := (XI.upTo N).at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with X := (XI.upTo N).at n } : RL).SegFrom (fun u =>
        OnCall ({ R with X := (XI.upTo N).at 0 } : RL).step R.fa R.base R.s0 n u ∧
          spOf u = R.spB) c i u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      (({ R with X := (XI.upTo N).at n } : RL).GoodX u ∧
        ({ R with X := (XI.upTo N).at n } : RL).WReadsIn (OkDiff F c c') u) →
      (({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).GoodX u' ∧
        ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).WReadsIn (OkDiff F c c') u') →
      (StEqOutX (R.Zc c c') u u' ∧ MConf.WIn (fun b => F b ∨ D b) c c' ∧
        MDiffIn F (fun b => F b ∨ D b) u u') →
      (StEqOutX (R.Zc c c') (({ R with X := (XI.upTo N).at 0 } : RL).step u)
          (({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step u') ∧
        MConf.WIn (fun b => F b ∨ D b) c c' ∧
        MDiffIn F (fun b => F b ∨ D b) (({ R with X := (XI.upTo N).at 0 } : RL).step u)
          (({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step u')) :=
    fun n n' c c' i u u' _ hin hsf hin' ⟨hg, hwr⟩ ⟨hg', _⟩ ⟨hl, hwi, _⟩ => by
      have hrc := RL.InSeg.isRun hin
      have hrc' := RL.InSeg.isRun hin'
      have hWD : ∀ a, MConf.WDiff c c' a → F a ∨ D a := wDiff_of_wIn hrc hrc' hwi
      subst hR
      obtain ⟨x, ⟨j, tc, hj, hpc⟩, htl⟩ := hg.line
      have ht : OnLine fa fb lm base u x := ⟨hlay, hlm, hfit, hg.prog, hg.err, ⟨j, tc, hj, hpc⟩⟩
      have hat : ({ actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp) with
          X := (XI.upTo N).at n } : RL).AtLine u x := ⟨j, tc, hj, hpc⟩
      have hx' : x.x30Exempt = true → (∃ m, x = .bl m) ∨ ∃ r', x = .blr r' := fun h =>
        RL.InSeg.exempt hin hat h htl
      have hld : x.ldpFR = false := by
        cases hl2 : x.ldpFR with
        | false => rfl
        | true =>
          exfalso
          have e : x = .ldp .fp .lr (.spPostIndexed 16) := by simpa [Insn.ldpFR] using hl2
          subst e
          rcases hx' (by decide) with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
      have hZ : x.hooked = false → ReadsAvoid
          ((actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp)).Zc c c')
          (stepiEvs u) := by
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
      have hstep1 := stEqOutX_lineZD (X := (XI.upTo N).at 0) (H := H) ht hx30 hx' hl.symm hZ
        (fun d hd => (hcall n n' c c' i u u' hin hsf hin' hg hg' hl hWD x d hat hd).symm)
        (fun m r' hb => (htls n n' c c' i u u' hin hin' hg hg' hl hWD
          (let ⟨a, b, c, e⟩ := hb; ⟨a, b, c, e ▸ hat⟩) m r').symm)
      exact ⟨hstep1.symm, hwi, mDiffIn_of_lock hRF hrc hrc' hstep1.symm hwi⟩
  have hendL : ∀ c c' d d' (i : Nat) u u', KJL R (XI.upTo N) t0 G' F c c' →
      KJL R (XI.upTo N) t0 G' F d d' → MConf.ShapeEq d d' →
      (∃ W : Nat × PState × List Line, QWA R u W.1 W.2.1 W.2.2 d ∧
        QWA ({ R with s0 := t0, G := G' } : RL) u' W.1 W.2.1 W.2.2 d') →
      (StEqOutX (R.Zc c c') u u' ∧ MConf.WIn (fun b => F b ∨ D b) c c' ∧
        MDiffIn F (fun b => F b ∨ D b) u u') →
      (StEqOutX (R.Zc d d') u u' ∧ MConf.WIn (fun b => F b ∨ D b) d d' ∧
        MDiffIn F (fun b => F b ∨ D b) u u') :=
    fun c c' d d' i u u' _ _ _ ⟨W, hq, hq'⟩ ⟨hl, _, hmd⟩ =>
      ⟨stEqOutX_zc_end (hRF'.trans hRF.symm) hq hq' hl, wIn_end hRF hRF' hFY hq hq' hmd, hmd⟩
  have hKL : ∀ (XP : ExtSemI) (ckc : CheckCtx) (ins : Array (Option AState)) (a0 : AState),
      CheckedAt R.vc R.rf ckc ins a0 → ∀ e e' x x',
      Match ckc ins ckeep (fun r => locVal R.fr (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize).length R.s0) (.reg r)) e x →
      Match ckc ins ckeep (fun r => locVal R.fr (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 }
        : RL).step (prologueLines R.af.saves R.af.frameSize).length t0) (.reg r)) e' x' →
      PairOfG pairFst pairSnd (StepOrRet vcp
        (pairDI (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XP)) x x' →
      KJL R (XI.upTo N) t0 G' F (e.mapW Prod.fst) (e'.mapW Prod.fst) :=
    fun XP ckc ins a0 hck e e' x x' hm hm' ⟨pc, hx, hx', hp⟩ => by
      subst hx hx' hR
      exact ⟨fun n d h => mstep_okDiff_fst hck hm hm' hp hRF h,
        fun n d h => mstep_okDiff_snd hck hm hm' hp hRF' h⟩
  have hp₁ : ∀ XP : ExtSemI, ISem.ProjW pairFst
      (pairDI (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XP)
      (csemVIGS R.gv R.F R.ctx XP (fun _ Y => Y = F)) := fun XP => by
    rw [hRF, csemVIGS_eqF, hRgv, hRctx]; exact pairFst_projD _ _ _ _
  have hp₂ : ∀ XP : ExtSemI, ISem.ProjW pairSnd
      (pairDI (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XP)
      (csemVIGS R.gv ({ R with s0 := t0, G := G' } : RL).F R.ctx XP (fun _ Y => Y = F)) :=
    fun XP => by rw [hRF', csemVIGS_eqF, hRgv, hRctx]; exact pairSnd_projD _ _ _ _
  refine ⟨fun hN => ?_, fun hN => ?_⟩
  rotate_left
  · -- the run passes the step from counter `N`: the lock up to that call
    obtain ⟨x, y, hsx, hxy, -, hxN, hyN⟩ := vstar_split_ctr hs (Nat.zero_le _) hN
    have hsxU := vstar_pairDI_upTo (N := N) hsx (Nat.le_of_eq hxN)
    have hpp := pstar_of_projSB (fun _ _ h => VStep.pairDI_upTo h) (hp₁ (XI.upTo N))
      (hp₂ (XI.upTo N)) hsxU ⟨y, hxy⟩
    have hy1 := VStep_mapW (hp₁ XI) hxy
    -- the step out of `x` is a call
    have hcallx : ∃ bx kx ρx wx vbx ix, x = .run ⟨bx, kx, ρx, wx⟩ ∧
        vcp.blocks[bx]? = some vbx ∧ vbx.insts[kx]? = some ix ∧ ix.isCallI = true := by
      cases hxy with
      | @step bx kx ρx wx vbx ix opsx outsx wx' ctlx cx' hvbx hix hopsx hsemx hlenx hnx =>
        refine ⟨bx, kx, ρx, wx, vbx, ix, rfl, hvbx, hix, ?_⟩
        have hcc := vnext_ctr hnx
        obtain ⟨-, hw⟩ := ISem.counted_some hsemx
        have hx2 : wx.2 = N := hxN
        rw [hcc, hw] at hyN
        cases hcI : ix.isCallI with
        | false => rw [hcI] at hyN; simp only [Bool.false_eq_true, ite_false] at hyN; omega
        | true => rfl
    obtain ⟨bx, kx, ρx, wx, vbx, ix, rfl, hvbx, hix, hcI⟩ := hcallx
    have hRvc : R.vc = vcp := by subst hR; rfl
    subst hR
    obtain ⟨T, b2, k2, a, its, m, w2, ρ2, a', its', m', w2', ρ2', nc, nc', h1, h2, h3, h4, h5, h6,
        h7⟩ :=
      RL.twoRunPRTNP hc.check hc.alloc hc.emit hc.layout hlm hpsF heU heU' rfl hcov ρ₀
        (fun _ Y => Y = F) (fun _ Y => Y = F) (KJL _ (XI.upTo N) t0 G' F)
        (fun d d' u u' => StEqOutX (Backend.Proof.RL.Zc _ d d') u u' ∧
          MConf.WIn (fun b => F b ∨ D b) d d' ∧ MDiffIn F (fun b => F b ∨ D b) u u')
        (fun c c' => OkDiff F c c') (fun c c' => OkDiff F c c')
        (fun n c c' d hK h => hK.1 n d h) (fun n c c' d hK h => hK.2 n d h)
        (fun c c' _ u u' => StEqOutX (Backend.Proof.RL.Zc _ c c') u u' ∧
          MConf.WIn (fun b => F b ∨ D b) c c' ∧ MDiffIn F (fun b => F b ∨ D b) u u')
        (fun _ _ _ _ _ h => h.1.1 .PC (by simp)) (fun _ _ _ _ _ h => h)
        hstepL hendL (hKL XI) hpro hpp
        ⟨VConf.init ρ₀ ((w₀, w₀'), 0), rfl, rfl, .inl (star_head_step hsx hxy)⟩
        ⟨.run ⟨bx, kx, ρx, wx⟩, rfl, rfl, .inl ⟨_, hxy⟩⟩ hy1
    simp only [VConf.mapW, pairFst, pairSnd, VConf.run.injEq, VState.mk.injEq, Prod.mk.injEq]
      at h6 h7
    obtain ⟨rfl, rfl, -, -, hnc⟩ := h6
    obtain ⟨-, -, -, -, hnc'⟩ := h7
    simp only [vctr] at hxN
    refine ⟨T, bx, kx, a, its, m, w2, a', its', m', w2', fun i hi => ?_, h3, ?_, ?_,
      vbx, ix, hvbx, hix, hcI⟩
    · obtain ⟨⟨c, c', _, h⟩, -, -⟩ := h2 i hi
      exact ⟨c, c', h.1⟩
    · rw [h4, ← hnc, hxN]
    · rw [h5, ← hnc', hxN]
  · -- the run makes at most `N` calls: it is a run of `XI.upTo N` to the return
    have hsU := vstar_pairDI_upTo (N := N) hs (by simpa [vctr] using hN)
    replace hsem : pairDI (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩
        (XI.upTo N) (.rets us) outs w₁ = some (outs', w, .ret) := by
      simp only [pairDI, ISem.counted] at hsem ⊢
      rw [pairSemD_upTo_eq _ _ _ XI (Or.inr rfl)]
      exact hsem
    have hck : ctlCheck vcp rf = true := (lowerRFunc_ok hc.alloc).2.2
    obtain ⟨ns, rfl⟩ := ctlCheck_rets hck hvb hk
    rw [operands_retsC] at hops
    cases hops
    have hlast : VStep vcp
        (pairDI (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ (XI.upTo N))
        (.run ⟨b, kk, ρ, w₁⟩) (.ret outs w) := by
      obtain ⟨hsP, -⟩ := ISem.counted_some hsem
      obtain ⟨-, hs1⟩ := pairSemD_sub hsP
      obtain ⟨hs1, -⟩ := pairSem_inv hs1
      have hsem' := hs1
      simp only [csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
      obtain ⟨rfl, -, -⟩ := hsem'
      rw [hvals] at hsem ⊢
      refine VStep.step hvb hk (operands_retsC ns) hsem ?_ (VNext.ret rfl)
      rw [List.toList_toArray, filter_isDef_retOpsC]; rfl
    subst hR
    have hy : PStep _ _ _ (PairOfG pairFst pairSnd (StepOrRet vcp _)) _ _ :=
      (⟨VStep_mapW (hp₁ (XI.upTo N)) hlast, VStep_mapW (hp₂ (XI.upTo N)) hlast,
        VConf.sameAt_mapW pairFst pairSnd (.ret outs w), .ret outs w, rfl, rfl,
        .inr ⟨outs, w, rfl⟩⟩ :
        PStep vcp _ _ (PairOfG pairFst pairSnd (StepOrRet vcp
          (pairDI (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ (XI.upTo N))))
          ((VConf.run ⟨b, kk, ρ, w₁⟩).mapW pairFst, (VConf.run ⟨b, kk, ρ, w₁⟩).mapW pairSnd)
          ((VConf.ret outs w).mapW pairFst, (VConf.ret outs w).mapW pairSnd))
    have hpp := pstar_of_projS (hp₁ (XI.upTo N)) (hp₂ (XI.upTo N)) hsU ⟨_, hlast⟩
    obtain ⟨T, e, e', hp0, h2, h3, hep, h5, h6, h7⟩ :=
      RL.twoRunPRTP hc.check hc.alloc hc.emit hc.layout hlm hpsF heU heU' rfl hcov ρ₀
        (fun _ Y => Y = F) (fun _ Y => Y = F) (KJL _ (XI.upTo N) t0 G' F)
        (fun d d' u u' => StEqOutX (Backend.Proof.RL.Zc _ d d') u u' ∧
          MConf.WIn (fun b => F b ∨ D b) d d' ∧ MDiffIn F (fun b => F b ∨ D b) u u')
        (fun c c' => OkDiff F c c') (fun c c' => OkDiff F c c')
        (fun n c c' d hK h => hK.1 n d h) (fun n c c' d hK h => hK.2 n d h)
        (fun c c' _ u u' => StEqOutX (Backend.Proof.RL.Zc _ c c') u u' ∧
          MConf.WIn (fun b => F b ∨ D b) c c' ∧ MDiffIn F (fun b => F b ∨ D b) u u')
        (fun _ _ _ _ _ h => h.1.1 .PC (by simp)) (fun _ _ _ _ _ h => h)
        hstepL hendL (hKL (XI.upTo N)) hpro hpp
        ⟨VConf.init ρ₀ ((w₀, w₀'), 0), rfl, rfl, .inl (star_head_step hsU hlast)⟩
        ⟨.run ⟨b, kk, ρ, w₁⟩, rfl, rfl, .inl ⟨_, hlast⟩⟩ hy
    refine ⟨T, e, e', fun i hi => let ⟨⟨c, c', _, h⟩, _, _⟩ := h2 i hi; ⟨c, c', h.1⟩, h3, h5, h6,
      h7.1, h7.2, fun i hi => ?_⟩
    generalize (prologueLines (actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G
      (GotV vcp)).af.saves (actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G
      (GotV vcp)).af.frameSize).length = PL at hi hp0 h2 hep ⊢
    generalize (actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp)).retLen = RLn
      at hi hep
    rcases Nat.lt_or_ge i PL with h1 | h1
    · exact ⟨(hp0 i h1).1.1.1.good, (hp0 i h1).2.1.1.good⟩
    rcases Nat.lt_or_ge i (PL + T) with h1' | h1'
    · obtain ⟨j, rfl⟩ : ∃ j, i = PL + j := ⟨i - PL, by omega⟩
      exact (h2 j (by omega)).2
    · obtain ⟨j, rfl⟩ : ∃ j, i = PL + T + j := ⟨i - (PL + T), by omega⟩
      exact ⟨(hep j (by omega)).1.1.1.good, (hep j (by omega)).2.1.1.good⟩

end

end E2E
