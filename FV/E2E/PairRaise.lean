import FV.Backend.Proof.LowerSimUW
import FV.E2E.DeadCleanupPair
import FV.E2E.DeadCleanupUnwindIsel

/-!
# The raising code on pairs of worlds (S10f, #233)

The non-interference half of the per-function theorem with unwinding runs the generic driver
with unwinding (`sim_runXW`, `FV/Backend/Proof/LowerSimUW.lean`) on pairs of worlds
(`pairSem`, memory relation `MRP`, `FV/E2E/PairDriver.lean`). Its raising steps need the
contracts `RaiseCalls`/`RaiseTries` for the paired semantics; this file derives them from M4's
rule theorems run, on each world, on a **guarded probe**:

* `probeG sem XR C Gd`: `probe` (`LowerSimURaise.lean`) whose calls also require the guard `Gd`
  of the call site; with `Gd := RaiseGuard …` the probe's run records, at the raising call, the
  pinned CLIF call (extern `n`, signature `s`, values `vals`, memory `cm`), the arguments where
  the call's kind puts them and the world related to `cm` — what the callees' non-interference
  on raises (`XRNI`) needs. Its non-call instructions run a guarded semantics `semG` (reads
  guarded by `Rd`): `stmt_raiseG`, `try_raiseG` (the per-world `stmt_raise`/`try_raise` with
  the code before the raising call a run of `semG`).
* `XRNI`: the callees' non-interference on raises (`XNI`'s counterpart for `XRaise`): two worlds
  that agree outside `Z ⊇ F`, with the call's pinned facts, raising give worlds that agree
  outside `Z`. `CallLgR`: the calls it is required at (the CLIF extern unwinds).
* `pairRaise XR`: the raises on pairs of worlds (both raise the same object).
* `raiseHypW_pair`: the paired `RaiseHypW`, for any guarded semantics family `semG` whose
  non-call steps go in lockstep and are steps of the semantics with unwinding `semU`; its
  instances `raiseHypW_pair_csemU` (legacy pipeline) and `raiseHypW_pair_valueSemU`
  (dead-cleanup pipeline).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-! ## The callees' non-interference on raises -/

/-- A raising call (`XRNI`'s premise `Lg`): the call's kind as `CallLg` has it, and the CLIF
extern `n` unwinds on `vals` from `cm` in `env`. -/
def CallLgR (env : Clif.XEnv) (exts : List Clif.ExtFunc) (sigs : List Clif.Signature) (n : String)
    (sig : Clif.Signature) (vals : List Clif.Val) (cm : Clif.Mem) : Prop :=
  ((∃ e ∈ exts, e.name = n ∧ e.sig = sig) ∨
      sig ∈ sigs ∧ vals.map (·.ty) = Clif.AbiParam.tys sig.params) ∧
    ∃ g e m, env.extern n = some g ∧ g vals cm = .unwound e m

/-- **Non-interference of the callees' raises** at the calls `Lg` admits (`XNI`'s counterpart):
two worlds that agree outside `Z ⊇ F`, both related to `cm` with stack pointer `sp0`, with the
arguments as the call's kind puts them, give, when the callee raises on both, worlds that agree
outside `Z`. -/
def XRNI (F : BitVec 64 → Prop) (syms : String → Option Nat) (exts : List Clif.ExtFunc)
    (sigs : List Clif.Signature) (sp0 : BitVec 64)
    (Lg : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (X : ExtSem) (XR : XRaise) :
    Prop :=
  ∀ (n : String) (sig : Clif.Signature) (vals : List Clif.Val) (cm : Clif.Mem) (args : List CV)
    (d : Option String) (uses : List CV) (Z : BitVec 64 → Prop) (w w' : Arm.ArmState)
    (o : BitVec 64) (x : Arm.ArmState) (o' : BitVec 64) (x' : Arm.ArmState),
    Lg n sig vals cm →
    (d = some n ∧ uses = args ∨ d = none ∧ ∃ u, uses = u :: args ∧ lo64 u = X.sym n 0) →
    (∀ a, F a → Z a) → SameWorld Z w w' → MemRel F syms cm w → MemRel F syms cm w' →
    spv w = sp0 → spv w' = sp0 →
    ((∃ e ∈ exts, e.name = n ∧ e.sig = sig) ∧ ArgsAt sig vals args w ∧ ArgsAt sig vals args w' ∨
      sig ∈ sigs ∧ ArgsAt sig vals args w ∧ ArgsAt sig vals args w') →
    XR.raise d uses w = some (o, x) → XR.raise d uses w' = some (o', x') → SameWorld Z x x'

/-! ## Raises on pairs of worlds -/

open Classical in
/-- **The raises on pairs of worlds**: the callee raises on both worlds, the same object. -/
noncomputable def pairRaise (XR : XRaise) : RaiseFn W2 := fun d us p =>
  match XR.raise d us p.1, XR.raise d us p.2 with
  | some (o1, x1), some (o2, x2) => if o1 = o2 then some (o1, (x1, x2)) else none
  | _, _ => none

theorem pairRaise_eq {XR : XRaise} {d : Option String} {us : List CV} {p : W2} {o : BitVec 64}
    {x1 x2 : Arm.ArmState} (h1 : XR.raise d us p.1 = some (o, x1))
    (h2 : XR.raise d us p.2 = some (o, x2)) : pairRaise XR d us p = some (o, (x1, x2)) := by
  simp [pairRaise, h1, h2]

theorem pairRaise_inv {XR : XRaise} {d : Option String} {us : List CV} {p : W2} {o : BitVec 64}
    {q : W2} (h : pairRaise XR d us p = some (o, q)) :
    XR.raise d us p.1 = some (o, q.1) ∧ XR.raise d us p.2 = some (o, q.2) := by
  unfold pairRaise at h
  split at h
  · rename_i o1 x1 o2 x2 h1 h2
    split at h
    · rename_i he
      subst he
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨h1, h2⟩
    · cases h
  · cases h

/-- A paired exceptional end projects to an exceptional end of each world, with the same
object. -/
theorem vUnwFrom_pair {vc : VCode} {sem : Sem} {XR : XRaise} {vs : VState CV W2} {obj : BitVec 64}
    {w : W2} (h : VUnwFromW vc (pairSem sem) (pairRaise XR) vs obj w) :
    VUnwFrom vc sem XR ⟨vs.b, vs.k, vs.ρ, vs.w.1⟩ obj w.1 ∧
      VUnwFrom vc sem XR ⟨vs.b, vs.k, vs.ρ, vs.w.2⟩ obj w.2 := by
  obtain ⟨b, k, ρ, w₁, vb, info, ops, outs, hs, hvb, hk, hops, hr, hsem, hlen⟩ := h
  obtain ⟨h1, h2⟩ := pairSem_inv hsem
  obtain ⟨r1, r2⟩ := pairRaise_inv hr
  exact ⟨⟨b, k, ρ, w₁.1, vb, info, ops, outs, star_pair Prod.fst (.inl rfl) hs, hvb, hk, hops, r1,
      h1, hlen⟩,
    ⟨b, k, ρ, w₁.2, vb, info, ops, outs, star_pair Prod.snd (.inr rfl) hs, hvb, hk, hops, r2, h2,
      hlen⟩⟩

/-! ## The guarded probe -/

/-- **The guard of a raising call site**: the pinned CLIF call (extern `n`, signature `s`, values
`vals`, memory `cm`) with its arguments as the call's kind puts them (a declared extern of
`exts` with the ABI's arguments; an indirect call of signature in `sigs` with the arguments where
its ABI puts them, S5, of the parameter types), the world related to `cm` with stack pointer
`sp0`, and the call's destination and uses (`CallG` for one pinned call, with the indirect
call's types). -/
def RaiseGuard (F : BitVec 64 → Prop) (syms : String → Option Nat) (X : ExtSem)
    (exts : List Clif.ExtFunc) (sigs : List Clif.Signature) (sp0 : BitVec 64) (n : String)
    (s : Clif.Signature) (vals : List Clif.Val) (cm : Clif.Mem) (dest : CallDest) (uses : List CV)
    (w : Arm.ArmState) : Prop :=
  ∃ args, (MemRel F syms cm w ∧ spv w = sp0) ∧
    ((∃ e ∈ exts, e.name = n ∧ e.sig = s) ∧ ArgsAt s vals args w ∨
      s ∈ sigs ∧ ArgsAt s vals args w ∧
        vals.map (·.ty) = Clif.AbiParam.tys s.params) ∧
    (dest = .sym n ∧ uses = args ∨ (∃ r, dest = .reg r) ∧ ∃ u, uses = u :: args ∧ lo64 u = X.sym n 0)

open Classical in
/-- **The guarded probe** (proof device): `probe sem XR C` whose calls also require the guard
`Gd` of the call site. -/
noncomputable def probeG (sem : Sem) (XR : XRaise) (C : BitVec 64 → Arm.ArmState → Prop)
    (Gd : CallDest → List CV → Arm.ArmState → Prop) : Sem := fun i uses w =>
  match i with
  | .call ci => if Gd ci.dest uses w then probe sem XR C i uses w else none
  | .tryCall ci _ => if Gd ci.dest uses w then probe sem XR C i uses w else none
  | _ => sem i uses w

section
variable {sem : Sem} {XR : XRaise} {C : BitVec 64 → Arm.ArmState → Prop}
  {Gd : CallDest → List CV → Arm.ArmState → Prop}

theorem probeG_other {i : MInst} (hc : ∀ ci, i ≠ .call ci) (ht : ∀ ci ti, i ≠ .tryCall ci ti) :
    probeG sem XR C Gd i = sem i := by
  funext uses w
  cases i with
  | call ci => exact absurd rfl (hc ci)
  | tryCall ci ti => exact absurd rfl (ht ci ti)
  | _ => rfl

theorem probeG_call_some {ci : CallInfo} {uses : List CV} {w w' : Arm.ArmState} {outs : List CV}
    {ctl : Ctl} (h : probeG sem XR C Gd (.call ci) uses w = some (outs, w', ctl)) :
    Gd ci.dest uses w ∧ ∃ obj, XR.raise (callDest ci) uses w = some (obj, w') ∧ C obj w' ∧
      outs = ci.defs.map (fun _ => ofX 0) ∧ ctl = .next := by
  simp only [probeG] at h
  split at h
  · exact ⟨‹_›, probe_call_some h⟩
  · cases h

theorem probeG_tryCall_some {ci : CallInfo} {ti : TryInfo} {uses : List CV} {w w' : Arm.ArmState}
    {outs : List CV} {ctl : Ctl}
    (h : probeG sem XR C Gd (.tryCall ci ti) uses w = some (outs, w', ctl)) :
    Gd ci.dest uses w ∧ ∃ obj, XR.raise (callDest ci) uses w = some (obj, w') ∧ C obj w' ∧
      outs = ci.defs.map (fun _ => ofX 0) ∧ ctl = .goto ti.handlers.length := by
  simp only [probeG] at h
  split at h
  · exact ⟨‹_›, probe_tryCall_some h⟩
  · cases h

theorem probeG_call_of {ci : CallInfo} {uses : List CV} {w w' : Arm.ArmState} {obj : BitVec 64}
    (hg : Gd ci.dest uses w) (hr : XR.raise (callDest ci) uses w = some (obj, w')) (hC : C obj w') :
    probeG sem XR C Gd (.call ci) uses w = some (ci.defs.map (fun _ => ofX 0), w', .next) := by
  simp only [probeG, hg, ite_true]
  exact probe_call_of hr hC

theorem probeG_tryCall_of {ci : CallInfo} {ti : TryInfo} {uses : List CV} {w w' : Arm.ArmState}
    {obj : BitVec 64} (hg : Gd ci.dest uses w) (hr : XR.raise (callDest ci) uses w = some (obj, w'))
    (hC : C obj w') :
    probeG sem XR C Gd (.tryCall ci ti) uses w =
      some (ci.defs.map (fun _ => ofX 0), w', .goto ti.handlers.length) := by
  simp only [probeG, hg, ite_true]
  exact probe_tryCall_of hr hC

theorem refines_probeG {F : BitVec 64 → Prop} (h : Refines F sem) :
    Refines F (probeG sem XR C Gd) := by
  intro i us w outs w' ctl hs
  have hc : ∀ ci, i ≠ .call ci := by rintro ci rfl; simp [ispec] at hs
  have ht : ∀ ci ti, i ≠ .tryCall ci ti := by rintro ci ti rfl; simp [ispec] at hs
  rw [probeG_other hc ht]
  exact h i us w outs w' hs

theorem memRefinesR_probeG {Rd F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (h : MemRefinesR Rd F sb syms sem) : MemRefinesR Rd F sb syms (probeG sem XR C Gd) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- **A guarded probe run that falls through a code containing a call** passes through a call
whose callee raises: the code before it (no call, no `tryCall`) is a run of `sem`, the call's
site satisfies the guard. -/
theorem probeG_fall_split :
    ∀ {ms : List MInst} {ρ : Nat → CV} {w : Arm.ArmState} {ρ' : Nat → CV} {w'' : Arm.ArmState},
    seqRun (probeG sem XR C Gd) ms ρ w = some (.fall ρ' w'') → (∃ ci, MInst.call ci ∈ ms) →
    ∃ k ci ops ρ₁ w₁ obj w', ms[k]? = some (.call ci) ∧
      (∀ m ∈ ms.take k, (∀ c, m ≠ .call c) ∧ ∀ c t, m ≠ .tryCall c t) ∧
      seqRun sem (ms.take k) ρ w = some (.fall ρ₁ w₁) ∧ (MInst.call ci).operands = .ok ops ∧
      XR.raise (callDest ci) (vuses ops ρ₁) w₁ = some (obj, w') ∧ C obj w' ∧
      Gd ci.dest (vuses ops ρ₁) w₁ := by
  intro ms
  induction ms with
  | nil => intro _ _ _ _ _ ⟨ci, h⟩; cases h
  | cons i ms ih =>
    intro ρ w ρ' w'' h hc
    obtain ⟨ops, outs, w₁, hops, hs, hl, hrest⟩ := seqRun_cons_fall h
    by_cases hic : ∃ ci, i = .call ci
    · obtain ⟨ci, rfl⟩ := hic
      obtain ⟨hg, obj, hr, hC, -, -⟩ := probeG_call_some hs
      exact ⟨0, ci, ops, ρ, w, obj, w₁, rfl, by simp, rfl, hops, hr, hC, hg⟩
    · have hc' : ∀ ci, i ≠ .call ci := fun ci e => hic ⟨ci, e⟩
      have ht : ∀ ci ti, i ≠ .tryCall ci ti := by
        rintro ci ti rfl
        obtain ⟨_, _, _, _, _, h⟩ := probeG_tryCall_some hs
        cases h
      rw [probeG_other hc' ht] at hs
      have hc2 : ∃ ci, MInst.call ci ∈ ms := by
        obtain ⟨ci, hci⟩ := hc
        rcases List.mem_cons.mp hci with e | e
        · exact absurd e.symm (hc' ci)
        · exact ⟨ci, e⟩
      obtain ⟨k, ci, ops', ρ₁, w₁', obj, w', h1, h2, h3, h4⟩ := ih hrest hc2
      refine ⟨k + 1, ci, ops', ρ₁, w₁', obj, w', h1, ?_, ?_, h4⟩
      · intro m hm
        rw [List.take_succ_cons] at hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact ⟨hc', ht⟩
        · exact h2 m hm
      · rw [List.take_succ_cons, seqRun_cons_next hops hs hl, h3]; rfl

/-- **A guarded probe run that stops at the last instruction** of a code whose other
instructions are no calls: they are no `tryCall`s either, and `sem` runs them as the probe
does. -/
theorem probeG_pre_stop :
    ∀ {pre : List MInst} {x : MInst} {ρ : Nat → CV} {w : Arm.ArmState} {k : Nat} {i : MInst}
      {ops : Array Operand} {ρ₁ : Nat → CV} {w₁ : Arm.ArmState} {outs : List CV}
      {w₂ : Arm.ArmState} {ctl : Ctl},
    (∀ m ∈ pre, ∀ ci, m ≠ .call ci) →
    seqRun (probeG sem XR C Gd) (pre ++ [x]) ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ ctl) →
    k = pre.length →
    (∀ m ∈ pre, ∀ c t, m ≠ .tryCall c t) ∧
    seqRun sem pre ρ w = some (.fall ρ₁ w₁) ∧ i = x ∧ x.operands = .ok ops ∧
      probeG sem XR C Gd x (vuses ops ρ₁) w₁ = some (outs, w₂, ctl) := by
  intro pre
  induction pre with
  | nil =>
    intro x ρ w k i ops ρ₁ w₁ outs w₂ ctl _ h hk
    rcases seqRun_cons_stop h with ⟨-, rfl, hops, rfl, rfl, hs, -, -⟩ |
      ⟨k', _, _, _, hk', -⟩
    · exact ⟨by simp, rfl, rfl, hops, hs⟩
    · simp at hk; omega
  | cons m pre ih =>
    intro x ρ w k i ops ρ₁ w₁ outs w₂ ctl hpre h hk
    rcases seqRun_cons_stop h with ⟨rfl, -, -, -, -, -, -, -⟩ |
      ⟨k', ops₀, outs₀, w₃, rfl, hops₀, hs₀, hl₀, hrest⟩
    · simp at hk
    · have hc : ∀ ci, m ≠ .call ci := hpre m (by simp)
      have ht : ∀ ci ti, m ≠ .tryCall ci ti := by
        rintro ci ti rfl
        obtain ⟨_, _, _, _, _, h⟩ := probeG_tryCall_some hs₀
        cases h
      rw [probeG_other hc ht] at hs₀
      obtain ⟨h0, h1, h2⟩ := ih (fun m' hm' => hpre m' (by simp [hm'])) hrest
        (by simp at hk; omega)
      refine ⟨fun m' hm' => ?_, by rw [seqRun_cons_next hops₀ hs₀ hl₀, h1]; rfl, h2⟩
      rcases List.mem_cons.mp hm' with rfl | hm'
      · exact ht
      · exact h0 m' hm'

end

/-! ## The guarded probe's contracts -/

section
variable {F : BitVec 64 → Prop} {X : ExtSem} {XR : XRaise} {env : Clif.XEnv}
  {MR : MemRelT} {slots : List (Clif.SlotId × Nat)} {sem : Sem} {syms : String → Option Nat}
  {sp0 : BitVec 64}

/-- **The guarded probe satisfies the pinned callee contract** at a call of `n` on `vals` from
`cm` whose CLIF extern unwinds. -/
theorem callsRefineP_probeG {exts : List Clif.ExtFunc} {sigs : List Clif.Signature}
    (hgot : ∀ (rd : Reg) (n : String) (w : Arm.ArmState), ∃ w',
      sem (.loadExtNameGot rd n) [] w = some ([ofX (X.sym n 0)], w', .next) ∧ SameWorldNF F w' w)
    (hXR : XRaiseOk env exts MR X XR) (hMRm : ∀ sl cm w, MR sl cm w → MemRel F syms cm w)
    (hMRc : ∀ sl cm w, MR sl cm w → spv w = sp0)
    {n : String} {s : Clif.Signature} {vals : List Clif.Val} {cm : Clif.Mem}
    {g : List Clif.Val → Clif.Mem → Clif.XOutcome} {e : Clif.Exn} {m : Clif.Mem}
    (hg : env.extern n = some g) (hu : g vals cm = .unwound e m) :
    CallsRefineP (pinPc n s vals cm) F (overEnv env.toEnv n vals cm (zeroVals s.returns) m) exts
      (pinMR MR slots)
      (probeG sem XR (raiseC MR slots e m) (RaiseGuard F syms X exts sigs sp0 n s vals cm)) := by
  refine ⟨fun n => X.sym n 0, fun rd n w => by
    obtain ⟨w', h1, h2⟩ := hgot rd n w
    exact ⟨w', by rw [probeG_other (fun _ h => by cases h) (fun _ _ h => by cases h)]; exact h1,
      h2⟩, ?_, ?_⟩
  · intro ext hin g' sl cm0 w dest us ds uses args vals' rvals cm' hg' hd hds hargs hmr hpc hret hrl
    obtain ⟨hn, hs, rfl, rfl⟩ := hpc
    obtain ⟨-, rfl, hcm⟩ := overEnv_at hg' hret
    subst hn hs cm'
    obtain ⟨obj, w', hr, hex, hm⟩ := hXR ext hin g sl cm0 w (callDest ⟨dest, us, ds⟩) uses args
      vals' e m hg (by rcases hd with ⟨rfl, rfl⟩ | ⟨r, rfl, hcol, rfl⟩ <;> simp [callDest, *])
      hargs hmr.2 hu
    have hG : RaiseGuard F syms X exts sigs sp0 ext.name ext.sig vals' cm0 dest uses w := by
      refine ⟨args, ⟨hMRm _ _ _ hmr.2, hMRc _ _ _ hmr.2⟩, .inl ⟨⟨ext, hin, rfl, rfl⟩, hargs⟩, ?_⟩
      rcases hd with ⟨rfl, rfl⟩ | ⟨r, rfl, -, rfl⟩
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr ⟨⟨r, rfl⟩, _, rfl, lo64_ofX64 _⟩
    exact ⟨_, w', probeG_call_of (ci := ⟨dest, us, ds⟩) hG hr ⟨hex, hmr.1 ▸ hm⟩, by simp,
      prefixHold_zero (by rw [hds]; exact returns_le_sigRets _), hmr.1, hm⟩
  · intro ext hin g' sl cm0 w dest us ds ti uses args vals' rvals cm' hg' hd hds hti hargs hmr hpc
      hret hrl
    obtain ⟨hn, hs, rfl, rfl⟩ := hpc
    obtain ⟨-, rfl, hcm⟩ := overEnv_at hg' hret
    subst hn hs cm'
    obtain ⟨obj, w', hr, hex, hm⟩ := hXR ext hin g sl cm0 w (callDest ⟨dest, us, ds⟩) uses args
      vals' e m hg (by rcases hd with ⟨rfl, rfl⟩ | ⟨r, rfl, hcol, rfl⟩ <;> simp [callDest, *])
      hargs hmr.2 hu
    have hG : RaiseGuard F syms X exts sigs sp0 ext.name ext.sig vals' cm0 dest uses w := by
      refine ⟨args, ⟨hMRm _ _ _ hmr.2, hMRc _ _ _ hmr.2⟩, .inl ⟨⟨ext, hin, rfl, rfl⟩, hargs⟩, ?_⟩
      rcases hd with ⟨rfl, rfl⟩ | ⟨r, rfl, -, rfl⟩
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr ⟨⟨r, rfl⟩, _, rfl, lo64_ofX64 _⟩
    exact ⟨_, w', probeG_tryCall_of (ci := ⟨dest, us, ds⟩) hG hr ⟨hex, hmr.1 ▸ hm⟩, by simp,
      prefixHold_zero (Nat.le_trans (returns_le_sigRets _) hds), hmr.1, hm⟩

/-- **The guarded probe satisfies the pinned indirect-call contract** at a call of `n` on `vals`
from `cm` whose CLIF extern unwinds. -/
theorem indCallsRefineP_probeG {exts : List Clif.ExtFunc} {sigs : List Clif.Signature}
    (hXRi : XRaiseIndOk env sigs MR X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hMRs : ∀ sl cm w, MR sl cm w → cm.symbols = syms)
    (hMRm : ∀ sl cm w, MR sl cm w → MemRel F syms cm w)
    (hMRc : ∀ sl cm w, MR sl cm w → spv w = sp0)
    {n : String} {s : Clif.Signature} {vals : List Clif.Val} {cm : Clif.Mem}
    {g : List Clif.Val → Clif.Mem → Clif.XOutcome} {e : Clif.Exn} {m : Clif.Mem}
    (hg : env.extern n = some g) (hu : g vals cm = .unwound e m) :
    IndCallsRefineP (pinPc n s vals cm) (overEnv env.toEnv n vals cm (zeroVals s.returns) m) sigs
      (pinMR MR slots)
      (probeG sem XR (raiseC MR slots e m) (RaiseGuard F syms X exts sigs sp0 n s vals cm)) := by
  refine ⟨?_, ?_⟩
  · intro sig hin n' g' sl cm0 w a r us ds u args vals' rvals cm' hg' hsg ha hu' hds hargs hmr
      hpc hret hrl hty
    obtain ⟨hn, hs, rfl, rfl⟩ := hpc
    obtain ⟨-, rfl, hcm⟩ := overEnv_at hg' hret
    subst hn hs cm'
    have hX : lo64 u = X.sym n' 0 := by
      rw [hu', hsym n' a (by rw [← hMRs sl _ w hmr.2]; exact ha)]
    obtain ⟨obj, w', hr, hex, hm⟩ := hXRi sig hin n' g sl cm0 w u args vals' e m hg hsg hX hargs
      hmr.2 hu hty
    have hG : RaiseGuard F syms X exts sigs sp0 n' sig vals' cm0 (.reg r) (u :: args) w :=
      ⟨args, ⟨hMRm _ _ _ hmr.2, hMRc _ _ _ hmr.2⟩, .inr ⟨hin, hargs, hty⟩,
        .inr ⟨⟨r, rfl⟩, u, rfl, hX⟩⟩
    exact ⟨_, w', probeG_call_of (ci := ⟨.reg r, us, ds⟩) hG hr ⟨hex, hmr.1 ▸ hm⟩, by simp,
      prefixHold_zero (by rw [hds]; exact returns_le_sigRets _), hmr.1, hm⟩
  · intro sig hin n' g' sl cm0 w a r us ds ti u args vals' rvals cm' hg' hsg ha hu' hds hti hargs
      hmr hpc hret hrl hty
    obtain ⟨hn, hs, rfl, rfl⟩ := hpc
    obtain ⟨-, rfl, hcm⟩ := overEnv_at hg' hret
    subst hn hs cm'
    have hX : lo64 u = X.sym n' 0 := by
      rw [hu', hsym n' a (by rw [← hMRs sl _ w hmr.2]; exact ha)]
    obtain ⟨obj, w', hr, hex, hm⟩ := hXRi sig hin n' g sl cm0 w u args vals' e m hg hsg hX hargs
      hmr.2 hu hty
    have hG : RaiseGuard F syms X exts sigs sp0 n' sig vals' cm0 (.reg r) (u :: args) w :=
      ⟨args, ⟨hMRm _ _ _ hmr.2, hMRc _ _ _ hmr.2⟩, .inr ⟨hin, hargs, hty⟩,
        .inr ⟨⟨r, rfl⟩, u, rfl, hX⟩⟩
    exact ⟨_, w', probeG_tryCall_of (ci := ⟨.reg r, us, ds⟩) hG hr ⟨hex, hmr.1 ▸ hm⟩, by simp,
      prefixHold_zero (Nat.le_trans (returns_le_sigRets _) hds), hmr.1, hm⟩

end

/-! ## The raising code on one world, through the guarded probe -/

section
variable {F : BitVec 64 → Prop} {X : ExtSem} {XR : XRaise} {semG : Sem} {Rd : BitVec 64 → Prop}
  {env : Clif.XEnv} {p : Clif.Program} {f : Clif.Function} {MR : MemRelT} {sb : Nat}
  {syms : String → Option Nat} {out : Nat} {sp0 : BitVec 64}

/-- **The code of a raising `call`/`call_indirect` statement on one world, guarded**
(`stmt_raise` with the reads before the raising call guarded by `Rd`): the code runs, under the
guarded semantics `semG`, up to its first call (no call, no `tryCall` before it), whose callee
raises an object related to `e`, the world after the unwinder related to `m`, at a call site
satisfying `RaiseGuard` for the pinned CLIF call (`n`, `s`, `vals`, `cm`; from
`instRaise_spec`). -/
theorem stmt_raiseG (hRG : Refines F semG) (hMG : MemRefinesR Rd F sb syms semG)
    (hgot : ∀ (rd : Reg) (n : String) (w : Arm.ArmState), ∃ w',
      semG (.loadExtNameGot rd n) [] w = some ([ofX (X.sym n 0)], w', .next) ∧ SameWorldNF F w' w)
    (hMR : MRStable F MR) (hout : OutArgsOk F out MR) (hMRo : MemRelOk F sb syms f MR)
    (hstk : CallsStack f out) (hIstk : IndStack (indSigs f) out)
    (hXR : XRaiseOk env (f.externs.map (·.2)) MR X XR) (hXRi : XRaiseIndOk env (indSigs f) MR X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hMRs : ∀ sl cm w, MR sl cm w → cm.symbols = syms)
    (hMRm : ∀ sl cm w, MR sl cm w → MemRel F syms cm w)
    (hMRc : ∀ sl cm w, MR sl cm w → spv w = sp0)
    {ctx : Ctx} (hctx : CtxInv f ctx) (hE : Compile.functionE f = true)
    {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hin : ∃ B ∈ f.blocks, ∃ stm ∈ B.body, stm.inst = inst)
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hsig : IndSigOk f (indSigs f) inst) {st : LState} {rss : List (List Reg)} {st' : LState}
    {tr : List Isle.RuleId} (hemp : st.emitted = #[]) (hvb : ValsBelow ctx st)
    (hrun : runTerm ctx "lower" [.inst ii] st = .ok (some (.regsVec rss), st', tr))
    (hcall : ∃ ci, MInst.call ci ∈ st'.emitted.toList)
    {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (hf : fr.func = ctx.func) (hvh : ValsHeld fr ρ) (hdc : DFGCons ctx fr) (hmr : MR fr.slots cm w)
    (hII : InitIn Rd cm) {e : Clif.Exn} {m : Clif.Mem} {n : String} {s : Clif.Signature}
    {vals : List Clif.Val} {g : List Clif.Val → Clif.Mem → Clif.XOutcome}
    (hg : env.extern n = some g) (hu : g vals cm = .unwound e m)
    (hO : instOutcome (overEnv env.toEnv n vals cm (zeroVals s.returns) m) p fr cm inst =
      .ok (zeroVals s.returns, m))
    (hpin : CallPin (pinPc n s vals cm) (overEnv env.toEnv n vals cm (zeroVals s.returns) m) inst
      fr cm) :
    UsesOk st fr st'.emitted.toList ∧ ∃ k ci ops ρ₁ w₁ obj w',
      st'.emitted.toList[k]? = some (.call ci) ∧
      (∀ x ∈ st'.emitted.toList.take k, (∀ c, x ≠ .call c) ∧ ∀ c t, x ≠ .tryCall c t) ∧
      seqRun semG (st'.emitted.toList.take k) ρ w = some (.fall ρ₁ w₁) ∧
      (MInst.call ci).operands = .ok ops ∧
      XR.raise (callDest ci) (vuses ops ρ₁) w₁ = some (obj, w') ∧
      RaiseGuard F syms X (f.externs.map (·.2)) (indSigs f) sp0 n s vals cm ci.dest
        (vuses ops ρ₁) w₁ ∧
      ExnRel e obj ∧ MR fr.slots m w' := by
  obtain ⟨B, hB, stm, hstm, rfl⟩ := hin
  obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOkP_runTerm lowerRulesCorrect_program
    excludedUnmatchable callRulesCorrectP indRulesCorrectP memRulesCorrectR_program
    (Rd := Rd) (Pc := pinPc n s vals cm) (cp := p)
    (refines_probeG (XR := XR) (C := raiseC MR fr.slots e m)
      (Gd := RaiseGuard F syms X (f.externs.map (·.2)) (indSigs f) sp0 n s vals cm) hRG)
    (mrStable_pin hMR fr.slots)
    (callsRefineP_probeG (slots := fr.slots) (sigs := indSigs f) hgot hXR hMRm hMRc hg hu)
    (indCallsRefineP_probeG (sem := semG) (exts := f.externs.map (·.2)) (slots := fr.slots) hXRi
      hsym hMRs hMRm hMRc hg hu)
    (memRefinesR_probeG hMG) hctx (outArgsOk_pin hout fr.slots)
    (externsIn_self f) hE (memRelOk_pin hMRo fr.slots) hi hc hsig hIstk
    (fun fn args e' hc' he => hstk B hB stm hstm fn args e' hc' he) hvb hrun
  have hms : ms = st'.emitted.toList := by
    rw [hemp, Array.empty_append] at hem; rw [hem, List.toList_toArray]
  subst hms
  have hrun' := hok.run fr cm ρ w hf hvh hdc ⟨rfl, hmr⟩ hII hpin
  rw [hO] at hrun'
  obtain ⟨hU, ρ', w'', hsr, -, -⟩ := hrun'
  obtain ⟨k, ci, ops, ρ₁, w₁, obj, w', h1, h2, h3, h4, h5, ⟨h6, h7⟩, h8⟩ :=
    probeG_fall_split hsr hcall
  exact ⟨hU, k, ci, ops, ρ₁, w₁, obj, w', h1, h2, h3, h4, h5, h8, h6, h7⟩

/-- **The code of a raising `try_call`/`try_call_indirect` on one world, guarded**
(`try_raise` with the reads before the raising call guarded by `Rd`): the code before the call
is a run of the guarded semantics `semG` (no `tryCall` in it), whose callee raises an object
related to `e` (the world related to `m`) at a call site satisfying `RaiseGuard`. -/
theorem try_raiseG (hRG : Refines F semG) (hMG : MemRefinesR Rd F sb syms semG)
    (hgot : ∀ (rd : Reg) (n : String) (w : Arm.ArmState), ∃ w',
      semG (.loadExtNameGot rd n) [] w = some ([ofX (X.sym n 0)], w', .next) ∧ SameWorldNF F w' w)
    (hMR : MRStable F MR) (hout : OutArgsOk F out MR) (hIstk : IndStack (indSigs f) out)
    (hXR : XRaiseOk env (f.externs.map (·.2)) MR X XR) (hXRi : XRaiseIndOk env (indSigs f) MR X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hMRs : ∀ sl cm w, MR sl cm w → cm.symbols = syms)
    (hMRm : ∀ sl cm w, MR sl cm w → MemRel F syms cm w)
    (hMRc : ∀ sl cm w, MR sl cm w → spv w = sp0)
    {ctx : Ctx} (hctx : CtxInv f ctx) {ti : Nat} {et : Clif.ExnTable} {data : V}
    {sig : Clif.Signature} {items : List (Option Nat)} {targets : List Label} {info : TryInfo}
    {trs : List Reg × List Reg} {lo st1 : LState} {outv : V} {st' : LState}
    {tr : List Isle.RuleId} {ci : Clif.Inst}
    (hT : (∃ fn args, ci = .call fn args ∧ tryCallData f (.tryCall fn args et) = .ok data ∧
        ∀ e, f.extern? fn = some e → SigStackOk e.sig out) ∨
      (∃ callee args, ci = .callIndirect et.sig callee args ∧
        tryCallData f (.tryCallIndirect callee args et) = .ok data ∧ sig ∈ indSigs f))
    (he : exnTableOpnd f et = .ok (sig, items))
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    (hinfo : tryInfoOf sig items targets = some info) (hregs : tryRegsOf sig lo = some (trs, st1))
    (hvb : ValsBelow ctx lo)
    (hrun : runTerm (tryCtx ctx ti data trs) "lower_branch" [.inst ti, .labels targets]
      { st1 with emitted := #[] } = .ok (some outv, st', tr))
    {pre : List MInst} {c : CallInfo} (hms : st'.emitted.toList = pre ++ [.call c])
    (hpre : ∀ x ∈ pre, ∀ ci, x ≠ .call ci)
    {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (hf : fr.func = ctx.func) (hvh : ValsHeld fr ρ) (hdc : DFGCons (tryCtx ctx ti data trs) fr)
    (hmr : MR fr.slots cm w) (hII : InitIn Rd cm) {e : Clif.Exn} {m : Clif.Mem} {n : String}
    {s : Clif.Signature} {vals : List Clif.Val} {g : List Clif.Val → Clif.Mem → Clif.XOutcome}
    (hg : env.extern n = some g) (hu : g vals cm = .unwound e m)
    (hO : instOutcome (overEnv env.toEnv n vals cm (zeroVals s.returns) m) p fr cm ci =
      .ok (zeroVals s.returns, m))
    (hpin : CallPin (pinPc n s vals cm) (overEnv env.toEnv n vals cm (zeroVals s.returns) m) ci
      fr cm) :
    UsesOk { st1 with emitted := #[] } fr st'.emitted.toList ∧ ∃ ops ρ₁ w₁ obj w',
      (∀ x ∈ pre, ∀ c t, x ≠ .tryCall c t) ∧ seqRun semG pre ρ w = some (.fall ρ₁ w₁) ∧
      (MInst.tryCall c info).operands = .ok ops ∧
      XR.raise (callDest c) (vuses ops ρ₁) w₁ = some (obj, w') ∧
      RaiseGuard F syms X (f.externs.map (·.2)) (indSigs f) sp0 n s vals cm c.dest
        (vuses ops ρ₁) w₁ ∧
      ExnRel e obj ∧ MR fr.slots m w' := by
  have hctx' := ctxInv_tryRegs (ctxInv_termCtx hctx hph data) trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  have hR' := refines_probeG (XR := XR) (C := raiseC MR fr.slots e m)
    (Gd := RaiseGuard F syms X (f.externs.map (·.2)) (indSigs f) sp0 n s vals cm) hRG
  have hcr := callsRefineP_probeG (slots := fr.slots) (s := s) (sigs := indSigs f) hgot hXR hMRm
    hMRc hg hu
  have hicr := indCallsRefineP_probeG (sem := semG) (exts := f.externs.map (·.2))
    (slots := fr.slots) (s := s) hXRi hsym hMRs hMRm hMRc hg hu
  obtain ⟨ms, hem, hlow⟩ : ∃ ms, st'.emitted = ({ st1 with emitted := #[] } : LState).emitted ++
      ms.toArray ∧ LowerTryOkP Rd (pinPc n s vals cm)
        (probeG semG XR (raiseC MR fr.slots e m)
          (RaiseGuard F syms X (f.externs.map (·.2)) (indSigs f) sp0 n s vals cm))
        (pinMR MR fr.slots) (overEnv env.toEnv n vals cm (zeroVals s.returns) m) p
        (tryCtx ctx ti data trs) ci info { st1 with emitted := #[] } st' ms := by
    rcases hT with ⟨fn, args, rfl, hd, hra⟩ | ⟨callee, args, rfl, hd, hsg⟩
    · exact tryOkP_runTerm tryRulesCorrectP tryUnmatchable hR' (mrStable_pin hMR fr.slots)
        (memRefinesR_probeG hMG) (outArgsOk_pin hout fr.slots) hcr hctx' (externsIn_self f) hra
        hd he hi hinfo hregs' hvb' (Nat.le_refl _) hrun
    · exact tryIndOkP_runTerm tryIndRulesCorrectP tryIndUnmatchable hR'
        (mrStable_pin hMR fr.slots) (memRefinesR_probeG hMG) (outArgsOk_pin hout fr.slots) hIstk
        hicr hctx' hd he hsg hi hinfo hregs' hvb' (Nat.le_refl _) hrun
  have hms' : ms = st'.emitted.toList := by
    simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
  subst hms'
  have hrun' := hlow.run fr cm ρ w hf hvh hdc ⟨rfl, hmr⟩ hII hpin
  rw [hO] at hrun'
  obtain ⟨hU, k, i, ops, ρ₁, w₁, outs, w₂, hsr, hk, -, -⟩ := hrun'
  rw [hms, tryFix_append] at hsr
  rw [hms] at hk
  have hk' : k = pre.length := by
    simp only [List.length_append, List.length_singleton] at hk; omega
  obtain ⟨hnt, hpre_run, rfl, hops, hprobe⟩ := probeG_pre_stop hpre hsr hk'
  obtain ⟨hG, obj, hra, ⟨hex, hm⟩, -, -⟩ := probeG_tryCall_some hprobe
  exact ⟨hU, ops, ρ₁, w₁, obj, w₂, hnt, hpre_run, hops, hra, hG, hex, hm⟩

end

/-! ## Pairing the raising code -/

theorem exnRel_unique {e : Clif.Exn} {o o' : BitVec 64} (h : ExnRel e o) (h' : ExnRel e o') :
    o = o' := by
  have := h.1.symm.trans h'.1
  injection this with h1 _
  injection h1

theorem callDest_eq (ci : CallInfo) : callDest ci = destName ci.dest := by
  obtain ⟨d, us, ds⟩ := ci
  cases d <;> rfl

/-- **The callees' non-interference at two guarded raising call sites** (`XRNI`, the guards'
facts on both worlds). -/
theorem raiseGuard_ni {F : BitVec 64 → Prop} {syms : String → Option Nat} {X : ExtSem}
    {XR : XRaise} {env : Clif.XEnv} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature}
    {sp0 : BitVec 64} (hNI : XRNI F syms exts sigs sp0 (CallLgR env exts sigs) X XR)
    {n : String} {s : Clif.Signature} {vals : List Clif.Val} {cm : Clif.Mem}
    {g : List Clif.Val → Clif.Mem → Clif.XOutcome} {e : Clif.Exn} {m : Clif.Mem}
    (hg : env.extern n = some g) (hu : g vals cm = .unwound e m)
    {Z : BitVec 64 → Prop} (hFZ : ∀ a, F a → Z a) {dest : CallDest} {uses : List CV}
    {w w' : Arm.ArmState} (hsw : SameWorld Z w w')
    (h1 : RaiseGuard F syms X exts sigs sp0 n s vals cm dest uses w)
    (h2 : RaiseGuard F syms X exts sigs sp0 n s vals cm dest uses w')
    {o o' : BitVec 64} {x x' : Arm.ArmState} (hr1 : XR.raise (destName dest) uses w = some (o, x))
    (hr2 : XR.raise (destName dest) uses w' = some (o', x')) : SameWorld Z x x' := by
  obtain ⟨a1, ⟨hm1, hsp1⟩, hk1, hd1⟩ := h1
  obtain ⟨a2, ⟨hm2, hsp2⟩, hk2, hd2⟩ := h2
  have hargs : a1 = a2 := by
    rcases hd1 with ⟨rfl, rfl⟩ | ⟨⟨r, rfl⟩, u, rfl, -⟩ <;>
      rcases hd2 with ⟨he, rfl⟩ | ⟨⟨r', he⟩, u', hu', -⟩
    · rfl
    · cases he
    · cases he
    · exact (List.cons.inj hu').2
  subst hargs
  have hd : destName dest = some n ∧ uses = a1 ∨
      destName dest = none ∧ ∃ u, uses = u :: a1 ∧ lo64 u = X.sym n 0 := by
    rcases hd1 with ⟨rfl, rfl⟩ | ⟨⟨r, rfl⟩, hu⟩
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨rfl, hu⟩
  have hLg : CallLgR env exts sigs n s vals cm := by
    refine ⟨?_, g, e, m, hg, hu⟩
    rcases hk1 with ⟨hk, -⟩ | ⟨hs, -, hty⟩
    · exact .inl hk
    · exact .inr ⟨hs, hty⟩
  have hA : (∃ e ∈ exts, e.name = n ∧ e.sig = s) ∧ ArgsAt s vals a1 w ∧ ArgsAt s vals a1 w' ∨
      s ∈ sigs ∧ ArgsAt s vals a1 w ∧ ArgsAt s vals a1 w' := by
    rcases hk1 with ⟨hk, ha1⟩ | ⟨hs, ha1, -⟩
    · rcases hk2 with ⟨-, ha2⟩ | ⟨-, ha2, -⟩
      · exact .inl ⟨hk, ha1, ha2⟩
      · exact .inl ⟨hk, ha1, ha2⟩
    · rcases hk2 with ⟨-, ha2⟩ | ⟨-, ha2, -⟩
      · exact .inr ⟨hs, ha1, ha2⟩
      · exact .inr ⟨hs, ha1, ha2⟩
  exact hNI n s vals cm a1 (destName dest) uses Z w w' o x o' x' hLg hd hFZ hsw hm1 hm2 hsp1 hsp2
    hA hr1 hr2

/-- The first call of a code is at one index. -/
theorem firstCall_unique {ms : List MInst} {k k' : Nat} {c c' : CallInfo}
    (h : ms[k]? = some (.call c)) (hn : ∀ x ∈ ms.take k, (∀ c, x ≠ .call c) ∧ ∀ c t, x ≠ .tryCall c t)
    (h' : ms[k']? = some (.call c'))
    (hn' : ∀ x ∈ ms.take k', (∀ c, x ≠ .call c) ∧ ∀ c t, x ≠ .tryCall c t) : k = k' := by
  rcases Nat.lt_trichotomy k k' with hlt | heq | hlt
  · have hm : MInst.call c ∈ ms.take k' := by
      apply List.mem_of_getElem? (i := k)
      rw [List.getElem?_take_of_lt hlt]; exact h
    exact absurd rfl ((hn' _ hm).1 c)
  · exact heq
  · have hm : MInst.call c' ∈ ms.take k := by
      apply List.mem_of_getElem? (i := k')
      rw [List.getElem?_take_of_lt hlt]; exact h'
    exact absurd rfl ((hn _ hm).1 c')

/-- A code whose instruction `k` is `x` splits at `k`. -/
theorem split_at {ms : List MInst} {k : Nat} {x : MInst} (h : ms[k]? = some x) :
    ms = ms.take k ++ x :: ms.drop (k + 1) ∧ (ms.take k).length = k := by
  obtain ⟨hk, hx⟩ := List.getElem?_eq_some_iff.mp h
  refine ⟨?_, by simp; omega⟩
  calc ms = ms.take k ++ ms.drop k := (List.take_append_drop k ms).symm
    _ = _ := by rw [List.drop_eq_getElem_cons hk, hx]

section
variable {p : Clif.Program} {f : Clif.Function} {env : Clif.XEnv} {F : BitVec 64 → Prop}
  {syms : String → Option Nat} {sb ib : Nat} {c : BitVec 64} {D : BitVec 64 → Prop}
  {X : ExtSem} {XR : XRaise} {out : Nat}

/-- **The raising code on pairs of worlds** (`RaiseHypW` for `pairSem semU`, the raises
`pairRaise XR` and the memory relation `MRP`): for a family of guarded semantics `semG Rd` with
the rule contracts (`Refines`, `MemRefinesR Rd`, the GOT load), whose steps with the reads
guarded by `¬ Zof F D cm` go in lockstep on worlds that agree outside `Zof F D cm` (`hlock`) and
are steps of the semantics with unwinding `semU` (`hsubG`), which ends the activation at a
raising call and enters the landing pad at a raising `tryCall` (`RaiseSem`), under the callees'
non-interference on raises (`XRNI`). -/
theorem raiseHypW_pair (semG : (BitVec 64 → Prop) → Sem) (semU : Sem)
    (hRG : ∀ Rd, Refines F (semG Rd)) (hMG : ∀ Rd, MemRefinesR Rd F sb syms (semG Rd))
    (hgot : ∀ Rd (rd : Reg) (n : String) (w : Arm.ArmState), ∃ w',
      semG Rd (.loadExtNameGot rd n) [] w = some ([ofX (X.sym n 0)], w', .next) ∧
        SameWorldNF F w' w)
    (hlock : ∀ (cm : Clif.Mem) (i : MInst) (us : List CV) (w w' : Arm.ArmState) (o : List CV)
      (w₁ : Arm.ArmState) (ct : Ctl) (o' : List CV) (w₁' : Arm.ArmState) (ct' : Ctl),
      SameWorld (Zof F D cm) w w' →
      semG (fun b => ¬ Zof F D cm b) i us w = some (o, w₁, ct) →
      semG (fun b => ¬ Zof F D cm b) i us w' = some (o', w₁', ct') →
      o = o' ∧ ct = ct' ∧ SameWorld (Zof F D cm) w₁ w₁')
    (hsubG : ∀ Rd i us w r, semG Rd i us w = some r → semU i us w = some r)
    (hRS : RaiseSem F X XR semU)
    (hstk : CallsStack f out) (htstk : TryStack f out) (hIstk : IndStack (indSigs f) out)
    (hout : OutArgsOk F out (RelW ⟨F, syms, sb, ib⟩ f c))
    (hXR : XRaiseOk env (f.externs.map (·.2)) (RelW ⟨F, syms, sb, ib⟩ f c) X XR)
    (hXRi : XRaiseIndOk env (indSigs f) (RelW ⟨F, syms, sb, ib⟩ f c) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hNI : XRNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLgR env (f.externs.map (·.2)) (indSigs f)) X XR) :
    RaiseHypW f (pairSem semU) (pairRaise XR) (MRP ⟨F, syms, sb, ib⟩ f c D) env p out := by
  let Γ : Rel := ⟨F, syms, sb, ib⟩
  have hMR : MRStable F (RelW Γ f c) := mrStable_relW Γ f c
  have hMRo : MemRelOk F sb syms f (RelW Γ f c) := memRelOk_relW Γ f c
  have hMRs : ∀ sl cm w, RelW Γ f c sl cm w → cm.symbols = syms := hMRo.symbols
  have hMRm : ∀ sl cm w, RelW Γ f c sl cm w → MemRel F syms cm w := fun _ _ _ h => h.1.1
  have hMRc : ∀ sl cm w, RelW Γ f c sl cm w → spv w = c := fun _ _ _ h => h.2.1
  have hFZ : ∀ cm, ∀ a, F a → Zof F D cm a := fun _ _ h => .inl h
  refine ⟨?_, ?_, htstk⟩
  · intro ctx ii info inst st rss st' tr hctx hE hin hi hc hsig hemp hvb hrun hcall fr cm ρ q hf
      hvh hdc hmr e m hr
    obtain ⟨hm1, hm2, hsw⟩ := hmr
    obtain ⟨n, s, vals, g, hg, hu, hO, hpin⟩ := instRaise_spec hr
    have hII : InitIn (fun b => ¬ Zof F D cm b) cm := initIn_zof (Γ := Γ) hm1 D
    obtain ⟨hU, k, ci, ops, ρa, wa, obj, wa', hk1, hn1, hs1, hops, hr1, hG1, hex1, hm1'⟩ :=
      stmt_raiseG (hRG _) (hMG _) (hgot _) hMR hout hMRo hstk hIstk hXR hXRi hsym hMRs hMRm hMRc
        hctx
        hE hin hi hc hsig hemp hvb hrun hcall hf hvh hdc hm1 hII hg hu hO hpin
    obtain ⟨-, k2, ci2, ops2, ρb, wb, obj2, wb', hk2, hn2, hs2, hops2, hr2, hG2, hex2, hm2'⟩ :=
      stmt_raiseG (hRG _) (hMG _) (hgot _) hMR hout hMRo hstk hIstk hXR hXRi hsym hMRs hMRm hMRc
        hctx
        hE hin hi hc hsig hemp hvb hrun hcall hf hvh hdc hm2 hII hg hu hO hpin
    obtain rfl := firstCall_unique hk1 hn1 hk2 hn2
    rw [hk1] at hk2
    cases hk2
    rw [hops] at hops2
    cases hops2
    obtain rfl := exnRel_unique hex1 hex2
    obtain ⟨ep, hp, hp1, hp2, hpr⟩ := seqRun_pair (sem := semU) (hsubG _)
      (R := SameWorld (Zof F D cm)) _ (fun i _ => hlock cm i) ρ q.1 q.2 _ _ hsw hs1 hs2
    cases ep with
    | stop => simp [SeqEnd.mapW] at hp1
    | fall ρ' qq =>
      simp only [SeqEnd.mapW, SeqEnd.fall.injEq] at hp1 hp2
      obtain ⟨hρ1, h1⟩ := hp1
      obtain ⟨hρ2, h2⟩ := hp2
      have hq : qq = (wa, wb) := Prod.ext h1 h2
      rw [hq, hρ1] at hp
      rw [hq] at hpr
      rw [← hρ2, hρ1] at hr2 hG2
      have hsw' : SameWorld (Zof F D cm) wa' wb' := by
        rw [callDest_eq] at hr1 hr2
        exact raiseGuard_ni hNI hg hu (hFZ cm) hpr hG1 hG2 hr1 hr2
      have hl : ((defCons (.call ci)).map fun _ => ofX 0).length =
          (ops.toList.filter Operand.isDef).length := by simp [defCons, hops]
      have hstep : pairSem semU (.call ci) (vuses ops ρa) (wa, wb) =
          some ((defCons (.call ci)).map fun _ => ofX 0, (wa', wb'), .halt) :=
        pairSem_eq (hRS.call ci _ wa obj wa' hr1) (hRS.call ci _ wb obj wb' hr2)
      obtain ⟨hsplit, hlen⟩ := split_at hk1
      have hrun2 := seqRun_append_fall_stop (pairSem semU) hp
        (seqRun_cons_halt (ms := st'.emitted.toList.drop (k + 1)) hops hstep hl
          (by intro h; cases h))
      rw [← hsplit, hlen, Nat.zero_add] at hrun2
      exact ⟨hU, k, ci, ops, ρa, (wa, wb), obj, (wa', wb'), hrun2, pairRaise_eq hr1 hr2, hex1,
        ⟨hm1', hm2', sameWorld_zof (hMRm _ _ _ hm1') (hMRm _ _ _ hm2') hsw' (zof_sub cm)⟩, hl⟩
  · intro ctx hctx ti et data sig items targets info trs lo st1 outv st' tr ci hT he hph hinfo hregs
      hvb hrun pre cc hms hpre hok fr cm ρ q hf hvh hdc hmr e m hr
    obtain ⟨hm1, hm2, hsw⟩ := hmr
    obtain ⟨n, s, vals, g, hg, hu, hO, hpin⟩ := instRaise_spec hr
    have hII : InitIn (fun b => ¬ Zof F D cm b) cm := initIn_zof (Γ := Γ) hm1 D
    obtain ⟨hU, ops, ρa, wa, obj, wa', hnt, hs1, hops, hr1, hG1, hex1, hm1'⟩ :=
      try_raiseG (hRG _) (hMG _) (hgot _) hMR hout hIstk hXR hXRi hsym hMRs hMRm hMRc hctx hT he
        hph
        hinfo hregs hvb hrun hms hpre hf hvh hdc hm1 hII hg hu hO hpin
    obtain ⟨-, ops2, ρb, wb, obj2, wb', -, hs2, hops2, hr2, hG2, hex2, hm2'⟩ :=
      try_raiseG (hRG _) (hMG _) (hgot _) hMR hout hIstk hXR hXRi hsym hMRs hMRm hMRc hctx hT he
        hph
        hinfo hregs hvb hrun hms hpre hf hvh hdc hm2 hII hg hu hO hpin
    rw [hops] at hops2
    cases hops2
    obtain rfl := exnRel_unique hex1 hex2
    obtain ⟨ep, hp, hp1, hp2, hpr⟩ := seqRun_pair (sem := semU) (hsubG _)
      (R := SameWorld (Zof F D cm)) _ (fun i _ => hlock cm i) ρ q.1 q.2 _ _ hsw hs1 hs2
    cases ep with
    | stop => simp [SeqEnd.mapW] at hp1
    | fall ρ' qq =>
      simp only [SeqEnd.mapW, SeqEnd.fall.injEq] at hp1 hp2
      obtain ⟨hρ1, h1⟩ := hp1
      obtain ⟨hρ2, h2⟩ := hp2
      have hq : qq = (wa, wb) := Prod.ext h1 h2
      rw [hq, hρ1] at hp
      rw [hq] at hpr
      rw [← hρ2, hρ1] at hr2 hG2
      have hsw' : SameWorld (Zof F D cm) wa' wb' := by
        rw [callDest_eq] at hr1 hr2
        exact raiseGuard_ni hNI hg hu (hFZ cm) hpr hG1 hG2 hr1 hr2
      have hops' : (MInst.call cc).operands = .ok ops := by
        rw [← operands_tryCall_call cc info]; exact hops
      have hl : (payloadOuts (.call cc) obj).length = (ops.toList.filter Operand.isDef).length := by
        simp [payloadOuts, defCons, hops']
      have hstep : pairSem semU (.tryCall cc info) (vuses ops ρa) (wa, wb) =
          some (payloadOuts (.call cc) obj, (wa', wb'), .goto 0) :=
        pairSem_eq (hRS.tryCall cc info _ wa obj wa' hr1 hok)
          (hRS.tryCall cc info _ wb obj wb' hr2 hok)
      have hrun2 := seqRun_append_fall_stop (pairSem semU) hp
        (seqRun_cons_halt (ms := []) hops hstep hl (by intro h; cases h))
      rw [Nat.zero_add] at hrun2
      exact ⟨hU, ops, ρa, (wa, wb), obj, (wa', wb'), hrun2, pairRaise_eq hr1 hr2, hex1,
        ⟨hm1', hm2', sameWorld_zof (hMRm _ _ _ hm1') (hMRm _ _ _ hm2') hsw' (zof_sub cm)⟩⟩

end

/-! ## The two pipelines -/

section
variable {p : Clif.Program} {f : Clif.Function} {env : Clif.XEnv} {F : BitVec 64 → Prop}
  {syms : String → Option Nat} {sb ib : Nat} {c : BitVec 64} {D : BitVec 64 → Prop}
  {X : ExtSem} {XR : XRaise} {out : Nat}

theorem csemG_got (fctx : FnCtx) (Rd : BitVec 64 → Prop) (rd : Reg) (n : String) (w : Arm.ArmState) :
    ∃ w', csemG F fctx X Rd syms [] [] 0 (fun _ _ _ _ => False) (.loadExtNameGot rd n) [] w =
      some ([ofX (X.sym n 0)], w', .next) ∧ SameWorldNF F w' w := by
  have hg : GuardR F Rd fctx.slotBase (.loadExtNameGot rd n) [] w := by
    unfold GuardR; split <;> simp_all
  have hc : GuardC F syms X [] [] 0 (fun _ _ _ _ => False) (.loadExtNameGot rd n) [] w := trivial
  rw [csemG_of hg hc]
  exact ⟨w, rfl, fun _ _ _ => rfl, fun _ _ => rfl, rfl⟩

/-- **The raising code on pairs of worlds, legacy pipeline** (`csemU`; the guarded semantics
`csemG` with no call admitted). -/
theorem raiseHypW_pair_csemU (fctx : FnCtx) (hsb : fctx.slotBase = sb) (hTls : XTls F X)
    (hex : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    (hstk : CallsStack f out) (htstk : TryStack f out) (hIstk : IndStack (indSigs f) out)
    (hout : OutArgsOk F out (RelW ⟨F, syms, sb, ib⟩ f c))
    (hXR : XRaiseOk env (f.externs.map (·.2)) (RelW ⟨F, syms, sb, ib⟩ f c) X XR)
    (hXRi : XRaiseIndOk env (indSigs f) (RelW ⟨F, syms, sb, ib⟩ f c) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hNI : XRNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLgR env (f.externs.map (·.2)) (indSigs f)) X XR) :
    RaiseHypW f (pairSem (csemU F fctx X XR)) (pairRaise XR) (MRP ⟨F, syms, sb, ib⟩ f c D) env p
      out :=
  raiseHypW_pair (fun Rd => csemG F fctx X Rd syms [] [] 0 (fun _ _ _ _ => False))
    (csemU F fctx X XR) (fun _ => refines_csemG) (fun _ => memRefinesR_csemG hsb hsym)
    (csemG_got fctx)
    (fun cm i us w w' o w₁ ct o' w₁' ct' hw h h' =>
      guardedStep0 (D := D) (syms := syms) hTls fctx cm [i] [] [] i (List.mem_singleton_self i) us
        w w' o w₁ ct o' w₁' ct' hw h h')
    (fun _ _ _ _ _ h => csemU_of_csem hex (csemG_sub h).2.2) (raiseSem_csemU F fctx X XR) hstk
    htstk hIstk hout hXR hXRi hsym hNI

/-- **The raising code on pairs of worlds, dead-cleanup pipeline** (`valueSemU`; the guarded
semantics `valueSemG` with no call admitted). -/
theorem raiseHypW_pair_valueSemU (fctx : FnCtx) (hsb : fctx.slotBase = sb) (hTls : XTls F X)
    (hex : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    (hstk : CallsStack f out) (htstk : TryStack f out) (hIstk : IndStack (indSigs f) out)
    (hout : OutArgsOk F out (RelW ⟨F, syms, sb, ib⟩ f c))
    (hXR : XRaiseOk env (f.externs.map (·.2)) (RelW ⟨F, syms, sb, ib⟩ f c) X XR)
    (hXRi : XRaiseIndOk env (indSigs f) (RelW ⟨F, syms, sb, ib⟩ f c) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hNI : XRNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLgR env (f.externs.map (·.2)) (indSigs f)) X XR) :
    RaiseHypW f (pairSem (valueSemU F fctx X XR)) (pairRaise XR) (MRP ⟨F, syms, sb, ib⟩ f c D) env
      p out :=
  raiseHypW_pair (fun Rd => valueSemG F fctx X Rd syms [] [] 0 (fun _ _ _ _ => False))
    (valueSemU F fctx X XR) (fun _ => refines_valueSemG) (fun _ => memRefinesR_valueSemG hsb hsym)
    (fun Rd rd n w => by
      simp only [valueSemG, specForm, pureForm, cmpForm, Bool.false_or, Bool.false_eq_true, ite_false]
      exact csemG_got fctx Rd rd n w)
    (fun cm i us w w' o w₁ ct o' w₁' ct' hw h h' =>
      guardedStep0_value (D := D) (syms := syms) hTls fctx cm [i] [] [] i
        (List.mem_singleton_self i) us w w' o w₁ ct o' w₁' ct' hw h h')
    (fun _ _ _ _ _ h => valueSemU_of_valueSem hex (valueSemG_sub h))
    (raiseSem_valueSemU F fctx X XR) hstk htstk hIstk hout hXR hXRi hsym hNI

end

end E2E
