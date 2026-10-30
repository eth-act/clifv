import FV.Concurrency.CallSegRun

/-!
# The invariants of a live activation along its CLIF run (#473, `SegOkG`)

* `crun_preserve`: a state property up to bytes kept by every `CStep` between reachable lifted
  states holds at the end of a `CRun` (and the lifted end is reachable);
* `allocInvD_cstep`, `linv_cstep`: `AllocInvD` of an open activation (at a depth at most the
  lifted state's) and `LInv` of the lifted state, through a `CStep` of the unlifted one;
* **`seg_inv`**: along an activation's own CLIF run from `s` (below its callers `ext`): every
  memory event is in `s`'s valid ranges or the activation's dead stack (`CallSegRun.segInv_crun`),
  and at a running end state `s'` with no callers the lifted `LInv`, every open activation's
  `AllocInvD`, the slot-placement oracle and the valid ranges (within `s`'s or the dead stack) are
  kept.
-/

namespace Concurrency.CallSegLive

open Clif ClifThread ClifCStepTerm ClifLift CallSegOkG CallSegRun CallValid Prog

variable {env : Env} {p : Program}

/-- `LInv` of a state up to its bytes. -/
theorem linv_congr {S S' : State} (h : withBytes S (fun _ => none) = withBytes S' (fun _ => none))
    (hI : LInv p S) : LInv p S' := by
  have e1 : S.frame = S'.frame := congrArg (·.frame) h
  have e2 : S.callers = S'.callers := congrArg (·.callers) h
  exact ⟨e1 ▸ hI.1, fun c hc => hI.2 c (e2 ▸ hc)⟩

/-- `AllocInvD` of a state up to its bytes. -/
theorem allocInvD_congr {S S' : State}
    (h : withBytes S (fun _ => none) = withBytes S' (fun _ => none)) {cm : Mem} {n : Nat}
    (hI : AllocInvD cm n S) : AllocInvD cm n S' := by
  have e1 : S.frame = S'.frame := congrArg (·.frame) h
  have e2 : S.callers = S'.callers := congrArg (·.callers) h
  have e3 : S.mem.allocs = S'.mem.allocs := congrArg (·.mem.allocs) h
  intro x hx
  rw [← e3] at hx
  have : slotBasesAbove n S' = slotBasesAbove n S := by
    simp only [slotBasesAbove, e1, e2]
  rw [this]
  exact hI x hx

theorem withBytes_pushC {ext : List (Frame × List ValueId)} {S S' : State}
    (h : withBytes S (fun _ => none) = withBytes S' (fun _ => none)) :
    withBytes (pushC ext S) (fun _ => none) = withBytes (pushC ext S') (fun _ => none) := by
  have e1 : S.frame = S'.frame := congrArg (·.frame) h
  have e2 : S.callers = S'.callers := congrArg (·.callers) h
  have e3 : ({ S.mem with bytes := fun _ => none } : Mem) = { S'.mem with bytes := fun _ => none } :=
    congrArg (·.mem) h
  simp only [withBytes, pushC, e1, e2, e3]

/-- **A property kept along a `CRun`** (module doc). -/
theorem crun_preserve {c0 : TState} {ext : List (Frame × List ValueId)} {Q : State → Prop}
    (hstep : ∀ S evs S1, RReach env p c0 (.run (pushC ext S)) → CStep env p (.run S) evs (.run S1) →
      Q S → Q S1) :
    ∀ {S S' : State} {trS : List (List (Ev SKind BVal))}, CRun env p (.run S) trS (.run S') →
      RReach env p c0 (.run (pushC ext S)) → Q S → Q S' ∧ RReach env p c0 (.run (pushC ext S'))
  | _, _, _, .nil, hR, hQ => ⟨hQ, hR⟩
  | S, S', _, .cons (t' := t1) hs r, hR, hQ => by
    cases t1 with
    | ret v => cases r with
      | cons h' _ => exact absurd h' (by intro h; exact h)
    | run S1 =>
      exact crun_preserve hstep r (hR.step (cstep_pushC hs)) (hstep _ _ _ hR hs hQ)

/-- `LInv` of the lifted state through a `CStep`. -/
theorem linv_cstep (hP : ∀ g ∈ p.funcs, LinkFree g) {ext : List (Frame × List ValueId)}
    {S S1 : State} {evs : List (Ev SKind BVal)} (hs : CStep env p (.run S) evs (.run S1))
    (hI : LInv p (pushC ext S)) : LInv p (pushC ext S1) := by
  obtain ⟨B, S2, hst, he⟩ := cstep_next (cstep_pushC (ext := ext) hs)
  have hI' : LInv p (withBytes (pushC ext S) B) := hI
  exact linv_congr he (Clif.step_next_linv hP hI' hst).1

/-- `AllocInvD` of an open activation through a `CStep` of the lifted state. -/
theorem allocInvD_cstep (hP : ∀ g ∈ p.funcs, LinkFree g) (hk : EnvKeepsAllocs env)
    {ext : List (Frame × List ValueId)} {S S1 : State} {evs : List (Ev SKind BVal)}
    (hs : CStep env p (.run S) evs (.run S1)) (hI : LInv p (pushC ext S)) {cm : Mem} {n : Nat}
    (hn : n ≤ ext.length) (hA : AllocInvD cm n (pushC ext S)) : AllocInvD cm n (pushC ext S1) := by
  obtain ⟨B, S2, hst, he⟩ := cstep_next (cstep_pushC (ext := ext) hs)
  have hI' : LInv p (withBytes (pushC ext S) B) := hI
  have hA' : AllocInvD cm n (withBytes (pushC ext S) B) := hA
  have hc2 : S2.callers = (pushC ext S1).callers := congrArg (·.callers) he
  refine allocInvD_congr he (allocInvD_step hP hk hI' hA' hst ?_ ?_)
  · show n ≤ (S.callers ++ ext).length; simp; omega
  · rw [hc2]; show n ≤ (S1.callers ++ ext).length; simp; omega

/-! ## A live activation -/

open Arm ArmThread Backend Backend.Proof Backend.Proof.Driver E2E ArmAllocThread LinkedMachine
  LinkedMachine.Link CallComposeT CallSegCall ThreadRefine PrivCohT

section live
variable (L : Link) (env : Clif.Env) (p : Clif.Program) (Bnd : Nat → Prop) (c0 : TState)
  (Loc : Nat → Nat → Prop) (fr : String → Option (Nat × (SlotId → Nat))) (Mx Dcap : Nat)
  (syms : String → Option Nat)

/-- **The invariants of a live activation** at its own CLIF state `s` (below its callers) with
mask `U` and dirty set `D` (module doc). -/
structure Live (g : Act) (U D : Nat → Prop) (s : Clif.State) : Prop where
  stat : StatOk L env p g
  syms : g.Γ.syms = syms
  code : CodeIn L (g.RL L)
  bnd : ∀ a, PrivA (g.RL L) a → Bnd a
  dirty : ∀ a, D a → PrivA (g.RL L) a ∨ U a ∨ (¬ ∃ n, Loc a n) ∨ g.N a
  reach : RReach env p c0 (.run (pushC g.ext s))
  call : s.callers = []
  ret : g.ext ≠ [] → (∃ cnm, (cnm, g.caller) ∈ L.fns) ∧ g.caller.InRange g.ra ∧
    ∀ k < g.F.fb.words.size, g.ra ≠ g.F.base + BitVec.ofNat 64 (4 * k)
  linv : LInv p (pushC g.ext s)
  place : s.mem.place = some ⟨(g.RL L).spB :: g.sps, fr, none⟩
  nv : ∀ a k, 0 < k → s.mem.valid a k = true → ¬ g.N a
  ndead : ∀ a, g.N a → ¬ ((g.RL L).spB.toNat ≤ a + g.K ∧ a < (g.RL L).spB.toNat)
  opens : ∀ om ∈ g.opens, om.2 < g.ext.length ∧ AllocInvD om.1 om.2 (pushC g.ext s)
  budget : (Dcap - g.ext.length) * Mx ≤ g.K
  func : s.frame.func = g.f

end live

/-- **An activation's segment** (module doc): a chain segment from a live state is a realized
prefix ending as `seg_end` ends, the activation live at its pause. -/
theorem seg_live {env : Clif.Env} {p : Clif.Program} {L : Link} {Bnd : Nat → Prop} {c0 : TState}
    {Loc : Nat → Nat → Prop}
    {fr : String → Option (Nat × (SlotId → Nat))} {Mx Dcap : Nat} {syms : String → Option Nat}
    (hP : PartsOk env p c0 Loc) (hdisj : PartDisj Loc)
    (hLF : ∀ f : Clif.Function, f ∈ Clif.Program.funcs p → Clif.LinkFree f)
    (hk : Clif.EnvKeepsAllocs env)
    (hkp : Clif.EnvKeepsPlace env)
    (hpo : PlaceOk p fr Mx) (hdep : ∀ S, RReach env p c0 (.run S) → S.callers.length < Dcap)
    {g : Act} {U D : Nat → Prop} {s : Clif.State}
    (hLv : Live L env p Bnd c0 Loc fr Mx Dcap syms g U D s) {x : ArmState × Mon}
    (hch : ChainP L env p g (g.r0 L) x s) {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm L.M (OkB Bnd) x ls t') :
    ∃ k' d', RealT env p Bnd ls k' (encT U (.run (pushC g.ext s)), D) d' ∧
      (k' = ls.length ∨ EndT env p Dcap (ls.take k') d' ∨
        ∃ s' M DE, (CallPz L g (g.r0 L) x (ls.take k') s' ∨
            RetPz L env p g (g.r0 L) x (ls.take k') s') ∧
          d' = (encT M (.run (pushC g.ext s')), DE) ∧ (∀ a, M a → U a) ∧
          Live L env p Bnd c0 Loc fr Mx Dcap syms g M DE s') := by
  obtain ⟨k, trS, t, ψ, hk', hx, hrun, href, hend⟩ := hch ls t' (prun_okPriv hLv.bnd hr)
  have hwf := hLv.stat.wf
  obtain ⟨hB1, hB2⟩ := FrameDisj.spB_toNat hwf
  have hKs : g.K ≤ (g.RL L).spB.toNat := by simp only [Act.RL, act_af, act_K] at hB1 hB2 ⊢; omega
  have hpl := hLv.place
  have hsI : SegInv p fr Mx (g.RL L).spB g.sps g.K s.mem s :=
    segInv_start ⟨hLv.linv.1, fun c hc => hLv.linv.2 c (by simp [pushC, hLv.call] at hc ⊢)⟩
      hLv.call hpl
  obtain ⟨hacc, -⟩ := seg_parts hP hLv.reach hrun
  have hev := segInv_crun hLF hk hkp hpo hKs hdep hLv.budget hrun hLv.reach hsI
  have hN : ∀ q y, evAt trS q = some y → y.dir = .R → ¬ g.N y.loc := by
    intro q y hy hR hN
    have hn : 0 < y.n := (hacc q y hy).2 hR
    obtain ⟨evs, hm, hye⟩ := mem_of_evAt hy
    rcases hev evs hm y hye (by rw [hR]; decide) with hv | ⟨h1, h2⟩
    · exact hLv.nv _ _ hn hv hN
    · exact hLv.ndead _ hN ⟨h1, by omega⟩
  obtain ⟨k2, d2, hR2, hE2⟩ := seg_end (Bnd := Bnd) (Dcap := Dcap) hLv.bnd hP hdisj hr hk' g.ext
    hLv.reach hrun hx href (N := g.N) hLv.dirty hN
    (Pz := fun s' => CallPz L g (g.r0 L) x (ls.take k) s' ∨ RetPz L env p g (g.r0 L) x (ls.take k) s')
    (hend.imp_right (Or.imp_right fun ⟨s', h1, h2⟩ => ⟨s', h1, h2⟩))
  rcases hE2 with h | h | ⟨rfl, s', M, DE, hz, rfl, rfl, hMU, hDE, hreach'⟩
  · exact ⟨k2, d2, hR2, .inl h⟩
  · exact ⟨k2, d2, hR2, .inr (.inl h)⟩
  -- the invariants at the pause
  have hcall' : s'.callers = [] := by
    rcases hz with ⟨_, _, _, _, _, _, _, _, hm2, _, _⟩ | ⟨_, _, _, hret⟩
    · exact hm2.1
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, vals, cm, _, _, _, _, _, hdone, _⟩ := hret
      exact callers_nil_of_done hdone
  obtain ⟨⟨hli, hop, hsI', hbot⟩, -⟩ := crun_preserve (c0 := c0) (ext := g.ext)
    (Q := fun S => LInv p (pushC g.ext S) ∧
      (∀ om ∈ g.opens, om.2 < g.ext.length ∧ AllocInvD om.1 om.2 (pushC g.ext S)) ∧
      SegInv p fr Mx (g.RL L).spB g.sps g.K s.mem S ∧ Clif.State.bottom S = g.f)
    (fun S evs S1 hRS hs ⟨h1, h2, h3, h4⟩ => by
      refine ⟨linv_cstep hLF hs h1, fun om hom => ⟨(h2 om hom).1,
        allocInvD_cstep hLF hk hs h1 (Nat.le_of_lt (h2 om hom).1) (h2 om hom).2⟩, ?_, ?_⟩
      · have hR1 : RReach env p c0 (.run (pushC g.ext S1)) := hRS.step (cstep_pushC hs)
        obtain ⟨B, S2, hst, he⟩ := cstep_next hs
        have hc2 : S2.callers = S1.callers := congrArg (·.callers) he
        have hd1 : S2.callers.length * Mx ≤ g.K := by
          have := hdep _ hR1
          simp only [pushC, List.length_append] at this
          rw [hc2]
          calc S1.callers.length * Mx ≤ (Dcap - g.ext.length) * Mx :=
                Nat.mul_le_mul_right _ (by omega)
            _ ≤ g.K := hLv.budget
        exact segInv_congr he (segInv_step hLF hk hkp hpo hKs (segInv_withBytes.mpr h3) hst hd1)
      · obtain ⟨B, S2, hst, he⟩ := cstep_next hs
        have hc2 : S2.callers = S1.callers := congrArg (·.callers) he
        have hf2 : S2.frame = S1.frame := congrArg (·.frame) he
        have hI : LInv p (withBytes S B) := h3.linv
        have hb := (Clif.step_next_linv hLF hI hst).2
        have e : Clif.State.bottom S1 = Clif.State.bottom S2 := by
          simp only [Clif.State.bottom, hc2, hf2]
        rw [e, hb]; exact h4)
    hrun hLv.reach ⟨hLv.linv, hLv.opens, hsI, by simp [Clif.State.bottom, hLv.call, hLv.func]⟩
  obtain ⟨l, hpl', hlen, -⟩ := hsI'.place
  rw [hcall'] at hlen
  obtain rfl : l = [] := List.eq_nil_of_length_eq_zero hlen
  refine ⟨_, _, hR2, .inr (.inr ⟨s', M, DE, hz, rfl, hMU, ⟨hLv.stat, hLv.syms, hLv.code, hLv.bnd,
    hDE, hreach', hcall', hLv.ret, hli, hpl', fun a k hk hv hN => ?_, hLv.ndead, hop,
    hLv.budget, by simpa [Clif.State.bottom, hcall'] using hbot⟩⟩)⟩
  simp only [Mem.valid, List.any_eq_true] at hv
  obtain ⟨y, hy, hcy⟩ := hv
  rcases hsI'.allocs y hy with h1 | ⟨h1, h2⟩
  · exact hLv.nv a k hk (h1 a k hcy) hN
  · simp only [Alloc.contains, Bool.and_eq_true, decide_eq_true_eq] at hcy
    exact hLv.ndead a hN ⟨by omega, by omega⟩

end Concurrency.CallSegLive
