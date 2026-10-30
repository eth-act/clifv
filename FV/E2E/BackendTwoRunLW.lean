import FV.E2E.BackendTwoRunLR

/-!
# The machine lock with the world-difference invariant and the call destination
(SEM1 #537, `docs/plans/uninit.md` §5.9, machine lock, item (2))

`backend_twoRunLER`'s call premise `hcall` receives a pair of locked states at a `bl`/`blr` line
and has to keep the lock for **every** hook destination `d`, and knows nothing about the worlds
of the two configurations. Neither is enough for the two kinds of callee:

* a base callee keeps the lock by `HookNIX` only when the lock set is inside the exterior `F`
  (`stEqOutX_call_of_hookNIX` needs `WDiff c c' ⊆ F`);
* a program callee is entered only at the destination the line names.

Here the lock carries the invariant that the two VCode worlds differ only on `F ∪ D` (the entry
worlds' difference set, `MConf.WIn`), together with its machine form (`MDiffIn`: outside `F` the
two machine states differ only on `F ∪ D`). It is kept along a segment by the lock itself (a byte
outside `F` where the states differ is in `Zc c c'`, hence where the configurations' worlds
differ) and carried to the next configuration through `StRel` (outside `F` the machine is the
VCode world). `hcall` then receives `WDiff c c' ⊆ F ∪ D` and the line's destination (`LineDest`).

* `MConf.WIn`, `MDiffIn`, `LineDest`, `RL.InSeg.isRun`, `wDiff_of_wIn`, `mDiffIn_of_lock`,
  `wIn_end`, `stEqOutX_line_callD`, `stEqOutX_lineZD`;
* **`backend_twoRunLW`** (`backend_twoRunLEF` with the stronger lock and call premises),
  **`backend_twoRunLERW`** (with `RetAgreeX` at the return, as `backend_twoRunLER`);
* `stEqOutX_call_of_hookNIX_D`: the base-call case when `D ⊆ F`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **The worlds of two run configurations differ only on `Y`** (true at other configurations). -/
def _root_.Backend.MConf.WIn (Y : BitVec 64 → Prop) :
    MConf CV Arm.ArmState → MConf CV Arm.ArmState → Prop
  | .run ms, .run ms' => ∀ a, ms.w.mem a ≠ ms'.w.mem a → Y a
  | _, _ => True

/-- **Outside `F`, two machine states differ only on `Y`.** -/
def MDiffIn (F Y : BitVec 64 → Prop) (u u' : Arm.ArmState) : Prop :=
  ∀ a, ¬ F a → u.mem a ≠ u'.mem a → Y a

/-- **The hook destination of a call line**: `bl n` calls `some n`, `blr` calls `none`
(`ArmStepX`). -/
def LineDest (x : Insn) (d : Option String) : Prop :=
  (∃ n, x = .bl n ∧ d = some n) ∨ ∃ r, x = .blr r ∧ d = none

/-- A segment starts at a run configuration (it realises an `MStep`). -/
theorem RL.InSeg.isRun {R : RL} {Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop}
    {c : MConf CV Arm.ArmState} {i : Nat} {u : Arm.ArmState} (h : R.InSeg Ok c i u) :
    ∃ ms, c = .run ms := by
  obtain ⟨s, j, ps1, T, d, n, -, hm, -⟩ := h
  cases c with
  | run ms => exact ⟨ms, rfl⟩
  | ret => cases hm
  | halt => cases hm

/-- `WIn` at two run configurations bounds their difference set. -/
theorem wDiff_of_wIn {Y : BitVec 64 → Prop} {c c' : MConf CV Arm.ArmState}
    (hc : ∃ ms, c = .run ms) (hc' : ∃ ms, c' = .run ms) (h : MConf.WIn Y c c') :
    ∀ a, MConf.WDiff c c' a → Y a := by
  obtain ⟨ms, rfl⟩ := hc
  obtain ⟨ms', rfl⟩ := hc'
  exact h

/-- **The lock and `WIn` give the machine form**: outside `F`, a byte where the locked states
differ is in `Zc c c'`, so where the (run) configurations' worlds differ. -/
theorem mDiffIn_of_lock {R : RL} {F Y : BitVec 64 → Prop} (hRF : R.F = F)
    {c c' : MConf CV Arm.ArmState} (hc : ∃ ms, c = .run ms) (hc' : ∃ ms, c' = .run ms)
    {u u' : Arm.ArmState} (hl : StEqOutX (R.Zc c c') u u') (hw : MConf.WIn Y c c') :
    MDiffIn F Y u u' := by
  intro a hF hne
  have hz : R.Zc c c' a := Classical.byContradiction fun hz => hne (hl.2.2 a hz)
  obtain ⟨-, -, -, hFD⟩ := hz
  rcases hFD with h | h
  · exact absurd (hRF ▸ h) hF
  · exact wDiff_of_wIn hc hc' hw a h

/-- **`WIn` at the end of a segment** from the machine form (`StRel`: outside `F` the machine
is the VCode world). -/
theorem wIn_end {R R' : RL} {F Y : BitVec 64 → Prop} (hRF : R.F = F) (hRF' : R'.F = F)
    (hFY : ∀ a, F a → Y a) {d d' : MConf CV Arm.ArmState} {u u' : Arm.ArmState}
    {W : Nat × PState × List Line} (hq : QWA R u W.1 W.2.1 W.2.2 d)
    (hq' : QWA R' u' W.1 W.2.1 W.2.2 d') (hm : MDiffIn F Y u u') : MConf.WIn Y d d' := by
  obtain ⟨⟨b, its, m, w⟩⟩ | _ | _ := d
  · obtain ⟨⟨b', its', m', w'⟩⟩ | _ | _ := d'
    · intro a hne
      by_cases hF : F a
      · exact hFY a hF
      · have e1 := (QWA.stRel hq).choose_spec.world.2.1 a (hRF ▸ hF)
        have e2 := (QWA.stRel hq').choose_spec.world.2.1 a (hRF' ▸ hF)
        exact hm a hF fun h => hne (by rw [← e1, ← e2]; exact h)
    · trivial
    · trivial
  · trivial
  · trivial

/-- `stEqOutX_line_call` with the hook premise at the line's destination only. -/
theorem stEqOutX_line_callD {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {fb : FnBin}
    {lm : Std.HashMap Lbl Nat} {base : BitVec 64} {Z Z' : BitVec 64 → Prop} {s t : Arm.ArmState}
    {x : Insn} (ht : OnLine fa fb lm base t x) (hb : (∃ n, x = .bl n) ∨ ∃ r', x = .blr r')
    (h : StEqOutX Z s t) (hcall : ∀ d, LineDest x d → StEqOutX Z' (H.call d s) (H.call d t)) :
    StEqOutX Z' (ArmStepX X H fa s) (ArmStepX X H fa t) := by
  have hpb : progBase s = progBase t := by simp only [progBase, h.2.1]
  have hpc' : Arm.r .PC s = Arm.r .PC t := h.1 .PC (by simp)
  have hi := ht.insnAt_eq
  rcases hb with ⟨n, rfl⟩ | ⟨r', rfl⟩
  · simp only [ArmStepX, hpb, hpc', hi]
    exact hcall _ (.inl ⟨n, rfl, rfl⟩)
  · simp only [ArmStepX, hpb, hpc', hi]
    exact hcall _ (.inr ⟨r', rfl, rfl⟩)

/-- `stEqOutX_lineZ` with the hook premise at the line's destination only. -/
theorem stEqOutX_lineZD {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {fb : FnBin}
    {lm : Std.HashMap Lbl Nat} {base : BitVec 64} {Z : BitVec 64 → Prop} {s t : Arm.ArmState}
    {x : Insn} (ht : OnLine fa fb lm base t x) (hc : fa.x30Free lm = true)
    (hx : x.x30Exempt = true → (∃ n, x = .bl n) ∨ ∃ r', x = .blr r')
    (h : StEqOutX Z s t) (hZ : x.hooked = false → ReadsAvoid Z (stepiEvs t))
    (hcall : ∀ d, LineDest x d → StEqOutX Z (H.call d s) (H.call d t))
    (htls : ∀ n r', (∃ a b c, x = .ldrTlsDescLo12 a b c) →
      StEqOutX Z (H.tls n r' s) (H.tls n r' t)) :
    StEqOutX Z (ArmStepX X H fa s) (ArmStepX X H fa t) := by
  cases hE : x.x30Exempt with
  | true => exact stEqOutX_line_callD ht (hx hE) h hcall
  | false =>
    have hb : ¬ ((∃ n, x = .bl n) ∨ ∃ r', x = .blr r') := by
      rintro (⟨n, rfl⟩ | ⟨r', rfl⟩) <;> simp [Insn.x30Exempt] at hE
    exact stEqOutX_lineZ ht hc (fun h' => absurd h' (by rw [hE]; decide)) h hZ
      (fun hb' => absurd hb' hb) htls

/-- **A base call keeps the lock when the entry difference set is inside the exterior**
(`HookNIX`, #704): `WDiff c c' ⊆ F ∪ D` with `F ∪ D` inside the activation's exterior. -/
theorem stEqOutX_call_of_hookNIX_D {R : RL} {Hb : ArmHooks} {BD : Option String → Prop}
    {F D : BitVec 64 → Prop} (hN : HookNIX Hb BD R.F) (hD : ∀ a, F a ∨ D a → R.F a)
    {c c' : MConf CV Arm.ArmState} (hW : ∀ a, MConf.WDiff c c' a → F a ∨ D a)
    {d : Option String} (hd : BD d) {u u' : Arm.ArmState}
    (h : StEqOutX (R.Zc c c') u u') : StEqOutX (R.Zc c c') (Hb.call d u) (Hb.call d u') :=
  stEqOutX_call_of_hookNIX hN (fun a ha => hD a (hW a ha)) hd h

/-- The TLS case of `stEqOutX_call_of_hookNIX_D`. -/
theorem stEqOutX_tls_of_hookNIX_D {R : RL} {Hb : ArmHooks} {BD : Option String → Prop}
    {F D : BitVec 64 → Prop} (hN : HookNIX Hb BD R.F) (hD : ∀ a, F a ∨ D a → R.F a)
    {c c' : MConf CV Arm.ArmState} (hW : ∀ a, MConf.WDiff c c' a → F a ∨ D a)
    (n : String) (r : Reg) {u u' : Arm.ArmState}
    (h : StEqOutX (R.Zc c c') u u') : StEqOutX (R.Zc c c') (Hb.tls n r u) (Hb.tls n r u') :=
  stEqOutX_tls_of_hookNIX hN (fun a ha => hD a (hW a ha)) n r h

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

set_option maxHeartbeats 4000000 in
/-- **The machine lock with the world-difference invariant** (module doc): `backend_twoRunLEF`
with the lock `StEqOutX (Zc c c') ∧ WIn (F ∪ D) c c' ∧ MDiffIn F (F ∪ D)`; the call and TLS
premises receive `WDiff c c' ⊆ F ∪ D`, and the call premise only the line's destination. -/
theorem backend_twoRunLW (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
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
    (hcall : ∀ n n' c c' i u u', ({ R with X := XI.at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with s0 := t0, G := G', X := XI.at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      ({ R with X := XI.at n } : RL).GoodX u →
      ({ R with s0 := t0, G := G', X := XI.at n' } : RL).GoodX u' →
      StEqOutX (R.Zc c c') u u' → (∀ a, MConf.WDiff c c' a → F a ∨ D a) →
      ∀ x d, ({ R with X := XI.at n } : RL).AtLine u x → LineDest x d →
      StEqOutX (R.Zc c c') (H.call d u) (H.call d u'))
    (htls : ∀ n n' c c' i u u', ({ R with X := XI.at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with s0 := t0, G := G', X := XI.at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      ({ R with X := XI.at n } : RL).GoodX u →
      ({ R with s0 := t0, G := G', X := XI.at n' } : RL).GoodX u' →
      StEqOutX (R.Zc c c') u u' → (∀ a, MConf.WDiff c c' a → F a ∨ D a) →
      (∃ a b c, ({ R with X := XI.at n } : RL).AtLine u (.ldrTlsDescLo12 a b c)) →
      ∀ m r, StEqOutX (R.Zc c c') (H.tls m r u) (H.tls m r u'))
    (hag : EntryAgree (frameDrop af + K) s t0)
    (hx29 : Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) t0) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
    ∃ N e e',
      (∀ i < N, ∃ c c', StEqOutX (R.Zc c c')
        (iterN ({ R with X := XI.at 0 } : RL).step ((prologueLines R.af.saves R.af.frameSize).length + i) R.s0)
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize).length + i) t0)) ∧
      JR R ({ R with s0 := t0, G := G' } : RL) (KJL R XI t0 G' F)
        (fun d d' u u' => StEqOutX (R.Zc d d') u u' ∧ MConf.WIn (fun b => F b ∨ D b) d d' ∧
          MDiffIn F (fun b => F b ∨ D b) u u')
        (iterN ({ R with X := XI.at 0 } : RL).step ((prologueLines R.af.saves R.af.frameSize).length + N) R.s0) e
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize).length + N) t0) e' ∧
      Arm.r .PC (iterN ({ R with X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize).length + N + R.retLen) R.s0) = ra ∧
      Arm.r .PC (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize).length + N + R.retLen) t0) = ra' ∧
      R.RetsAt e ∧ R.RetsAt e' := by
  intro vals cm hrun
  have hRF : R.F = F := by subst hR; exact he.hF
  have hRF' : ({ R with s0 := t0, G := G' } : RL).F = F := by subst hR; exact he'.hF
  have hfit : 4 * fb.words.size ≤ 2 ^ 64 := by have := he.abi.fits; omega
  have hlay : fa.layout = .ok fb := hc.layout
  have hFY : ∀ a, F a → F a ∨ D a := fun _ h => .inl h
  have hproS : StEqOutX
      (R.Zc (MConf.init R.rf (locVal R.fr (iterN ({ R with X := XI.at 0 } : RL).step
          (prologueLines R.af.saves R.af.frameSize).length R.s0)) w₀)
        (MConf.init R.rf (locVal R.fr (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          (prologueLines R.af.saves R.af.frameSize).length t0)) w₀'))
      (iterN ({ R with X := XI.at 0 } : RL).step (prologueLines R.af.saves R.af.frameSize).length R.s0)
      (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize).length t0) := by
    subst hR
    have hF := he.hF
    subst hF
    obtain ⟨-, -, -, -, hk⟩ := emitFunc_ok hc.emit
    subst hk
    obtain ⟨ckc, ins, hck⟩ := checked_of_checkAlloc hc.check
    obtain ⟨a0, hat, hle⟩ := hck.at
    have hW0 : ({ actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp) with X := XI.at 0 } :
        RL).Wf :=
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
  have key := backend_twoRunPRIYT hsub hc hone htc hX hNI hTls hsym hslot ρ₀ hce hrel hrel' hargs
    hsw hreg hstk htr fuel hlm hpsF he he' hR hcov (KJL R XI t0 G' F)
    (fun d d' u u' => StEqOutX (R.Zc d d') u u' ∧ MConf.WIn (fun b => F b ∨ D b) d d' ∧
      MDiffIn F (fun b => F b ∨ D b) u u')
    (fun c c' => OkDiff F c c')
    (fun c c' => OkDiff F c c') (fun n c c' d hK h => hK.1 n d h) (fun n c c' d hK h => hK.2 n d h)
    (fun c c' _ u u' => StEqOutX (R.Zc c c') u u' ∧ MConf.WIn (fun b => F b ∨ D b) c c' ∧
      MDiffIn F (fun b => F b ∨ D b) u u')
    (fun _ _ _ _ _ h => h.1.1 .PC (by simp))
    (fun _ _ _ _ _ h => h)
    (fun n n' c c' i u u' _ hin hin' ⟨hg, hwr⟩ ⟨hg', _⟩ ⟨hl, hwi, _⟩ => by
      have hrc := RL.InSeg.isRun hin
      have hrc' := RL.InSeg.isRun hin'
      have hWD : ∀ a, MConf.WDiff c c' a → F a ∨ D a := wDiff_of_wIn hrc hrc' hwi
      subst hR
      obtain ⟨x, ⟨j, tc, hj, hpc⟩, htl⟩ := hg.line
      have ht : OnLine fa fb lm base u x := ⟨hlay, hlm, hfit, hg.prog, hg.err, ⟨j, tc, hj, hpc⟩⟩
      have hat : ({ actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp) with X := XI.at n } :
          RL).AtLine u x := ⟨j, tc, hj, hpc⟩
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
          ((actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp)).Zc c c') (stepiEvs u) := by
        intro hk
        apply readsAvoid_stepiEvs
        intro a ha ev hev hdir k hk'
        obtain ⟨a', ha', hd⟩ := decodeAt_ofLine ht.layout ht.lm ht.fit ht.prog hj hpc
        rw [hd, Option.some.injEq] at ha
        subst ha
        have hcov := (ExecBytes.instEvs_cover hev).1 hdir
        obtain ⟨Y, -, hYO, hrd⟩ := hwr
        have hr := hrd j x tc hj hpc hk a'
          (by refine (congrArg (x.toArmInst ·) ?_).trans ha'; exact RL.envL_of_lm ht.lm j)
          (ev.addr, ev.n) hcov k hk'
        rw [hld] at hr
        refine RL.notZc_of_readInY hr fun b hb => ?_
        rcases hYO with hall | ⟨_, -, hYD⟩
        · exact hall b
        · exact hYD b hb
      have hstep1 := stEqOutX_lineZD (X := XI.at 0) (H := H) ht hx30 hx' hl.symm hZ
        (fun d hd => (hcall n n' c c' i u u' hin hin' hg hg' hl hWD x d hat hd).symm)
        (fun m r' hb => (htls n n' c c' i u u' hin hin' hg hg' hl hWD
          (let ⟨a, b, c, e⟩ := hb; ⟨a, b, c, e ▸ hat⟩) m r').symm)
      exact ⟨hstep1.symm, hwi, mDiffIn_of_lock hRF hrc hrc' hstep1.symm hwi⟩)
    (fun c c' d d' i u u' _ _ _ ⟨W, hq, hq'⟩ ⟨hl, _, hmd⟩ =>
      ⟨stEqOutX_zc_end (hRF'.trans hRF.symm) hq hq' hl, wIn_end hRF hRF' hFY hq hq' hmd, hmd⟩)
    (fun ckc ins a0 hck e e' x x' hm hm' ⟨pc, hx, hx', hp⟩ => by
      subst hx hx' hR
      exact ⟨fun n d h => mstep_okDiff_fst hck hm hm' hp hRF h,
        fun n d h => mstep_okDiff_snd hck hm hm' hp hRF' h⟩)
    ⟨hproS, hwi0 _ _, mDiffIn_of_lock hRF ⟨_, rfl⟩ ⟨_, rfl⟩ hproS (hwi0 _ _)⟩ vals cm hrun
  obtain ⟨N, e, e', -, h2, h3, -, h5, h6, h7⟩ := key
  exact ⟨N, e, e', fun i hi => let ⟨c, c', _, h⟩ := h2 i hi; ⟨c, c', h.1⟩, h3, h5, h6, h7⟩

set_option maxHeartbeats 4000000 in
/-- **`backend_twoRunLER` with the world-difference invariant and the call destination**: the
lock along the body, both returns at their return addresses, `RetAgreeX` at the return, and the
two returned states equal on the memory outside `F ∪ D`; the call and TLS premises as in
`backend_twoRunLW`. -/
theorem backend_twoRunLERW (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
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
    (hcall : ∀ n n' c c' i u u', ({ R with X := XI.at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with s0 := t0, G := G', X := XI.at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      ({ R with X := XI.at n } : RL).GoodX u →
      ({ R with s0 := t0, G := G', X := XI.at n' } : RL).GoodX u' →
      StEqOutX (R.Zc c c') u u' → (∀ a, MConf.WDiff c c' a → F a ∨ D a) →
      ∀ x d, ({ R with X := XI.at n } : RL).AtLine u x → LineDest x d →
      StEqOutX (R.Zc c c') (H.call d u) (H.call d u'))
    (htls : ∀ n n' c c' i u u', ({ R with X := XI.at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with s0 := t0, G := G', X := XI.at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      ({ R with X := XI.at n } : RL).GoodX u →
      ({ R with s0 := t0, G := G', X := XI.at n' } : RL).GoodX u' →
      StEqOutX (R.Zc c c') u u' → (∀ a, MConf.WDiff c c' a → F a ∨ D a) →
      (∃ a b c, ({ R with X := XI.at n } : RL).AtLine u (.ldrTlsDescLo12 a b c)) →
      ∀ m r, StEqOutX (R.Zc c c') (H.tls m r u) (H.tls m r u'))
    (hag : EntryAgree (frameDrop af + K) s t0)
    (hx29 : Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) t0) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
    ∃ N,
      (∀ i < N, ∃ c c', StEqOutX (R.Zc c c')
        (iterN ({ R with X := XI.at 0 } : RL).step ((prologueLines R.af.saves R.af.frameSize).length + i) R.s0)
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize).length + i) t0)) ∧
      Arm.r .PC (iterN ({ R with X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize).length + N + R.retLen) R.s0) = ra ∧
      Arm.r .PC (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize).length + N + R.retLen) t0) = ra' ∧
      RetAgreeX (frameDrop af + K) (spv s)
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize).length + N + R.retLen) t0)
        (iterN ({ R with X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize).length + N + R.retLen) R.s0) ∧
      (∀ a, ¬ F a → ¬ D a →
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize).length + N + R.retLen) t0).mem a =
        (iterN ({ R with X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize).length + N + R.retLen) R.s0).mem a) ∧
      ∀ i < (prologueLines R.af.saves R.af.frameSize).length + N + R.retLen, ∃ Z : BitVec 64 → Prop,
        StEqOutX Z (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step i t0)
          (iterN ({ R with X := XI.at 0 } : RL).step i R.s0) := by
  intro vals cm hrun
  obtain ⟨N, e, e', hlk, ⟨⟨W, hqA, -⟩, -, -, hLB⟩, hpc, hpc', hre, hre'⟩ :=
    backend_twoRunLW hsub hc hone htc hX hNI hTls hsym hslot ρ₀ hce hrel hrel' hargs hsw hreg hstk
      htr fuel hlm hpsF he he' hR hcov hx30 hcall htls hag hx29 vals cm hrun
  refine ⟨N, hlk, hpc, hpc', ?_⟩
  have hs : ∀ (g : Arm.ArmState → Arm.ArmState) (x : Arm.ArmState) (j : Nat),
      iterN g ((prologueLines R.af.saves R.af.frameSize).length + N + j) x =
        iterN g j (iterN g ((prologueLines R.af.saves R.af.frameSize).length + N) x) :=
    fun g x j => iterN_add ..
  subst hR
  have hF := he.hF
  subst hF
  obtain ⟨-, -, -, -, hk⟩ := emitFunc_ok hc.emit
  subst hk
  obtain ⟨ckc, ins, hck⟩ := checked_of_checkAlloc hc.check
  obtain ⟨a0, hat, hle⟩ := hck.at
  have hW0 : ({ actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp) with X := XI.at 0 } :
      RL).Wf :=
    ⟨⟨ckc, ins, a0, hat, entryOk_of_le hle⟩, hc.alloc, hc.emit, hc.layout, hlm,
      by show 4 * fb.words.size ≤ 2 ^ 64; have := he.abi.fits; omega, he.stack, ⟨body, hpsF⟩,
      he.abi.program, he.gfree⟩
  have hr1 : ∃ ms, e = .run ms := by
    obtain ⟨_, _, _, _, _, _, _, _, rfl, -⟩ := hre; exact ⟨_, rfl⟩
  have hr2 : ∃ ms, e' = .run ms := by
    obtain ⟨_, _, _, _, _, _, _, _, rfl, -⟩ := hre'; exact ⟨_, rfl⟩
  obtain ⟨hra, -, hm, hepi⟩ := RL.retLock_rets hW0 he.abi hx30 (QWA.qaX hqA hW0 he.abi) hre
    hLB.1.symm
  refine ⟨by rw [hs, hs]; exact hra, fun a hFa hDa => ?_, fun i hi => ?_⟩
  · rw [hs, hs]
    refine hm a ?_
    rintro ⟨-, -, -, hz⟩
    rcases hz with h | h
    · exact hFa h
    · rcases wDiff_of_wIn hr1 hr2 hLB.2.1 a h with h' | h'
      · exact hFa h'
      · exact hDa h'
  · have hPe : (prologueLines (actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp)).af.saves
        (actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp)).af.frameSize).length
        = (prologueLines af.saves af.frameSize).length := rfl
    have hRe : (actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp)).retLen =
        ({ actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp) with X := XI.at 0 } : RL).retLen :=
      rfl
    rw [hPe] at hi hs
    rcases Nat.lt_or_ge i (prologueLines af.saves af.frameSize).length with h1 | h1
    · exact ⟨_, stEqOutX_prologueZ_le hW0 he.abi hx30
        (fun k h8 h16 => RL.lrWord_Zc hW0 _ _ h8 h16)
        (stEqOutX_entryZ hW0 he.abi he'.abi he.body he'.body (fun _ h => h) hsw hag hx29
          (c := .run ⟨0, [], fun _ => ρ₀ 0, w₀⟩) (c' := .run ⟨0, [], fun _ => ρ₀ 0, w₀'⟩)
          (fun _ h => h)).symm i (Nat.le_of_lt h1)⟩
    · rcases Nat.lt_or_ge i ((prologueLines af.saves af.frameSize).length + N) with h2 | h2
      · obtain ⟨j, rfl⟩ : ∃ j, i = (prologueLines af.saves af.frameSize).length + j :=
          ⟨i - (prologueLines af.saves af.frameSize).length, by omega⟩
        obtain ⟨c, c', hcc⟩ := hlk j (by omega)
        exact ⟨_, hcc.symm⟩
      · obtain ⟨j, rfl⟩ : ∃ j, i = (prologueLines af.saves af.frameSize).length + N + j :=
          ⟨i - ((prologueLines af.saves af.frameSize).length + N), by omega⟩
        rw [hs, hs]
        exact ⟨_, hepi j (by rw [hRe] at hi; omega)⟩

end

end E2E
