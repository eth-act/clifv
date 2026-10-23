import FV.Concurrency.CallSegOkG

/-! SCRATCH (WIP, contains `sorry`; imported by nothing). -/

namespace Concurrency.CallSegOkG

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck ThreadRefine IselCall IselCallRet ArmAllocThread E2E
  ClifCStepTerm IselThread CallRetsEnd CallRetsN CallSegAbi LinkedMachine LinkedMachine.Link
  CallComposeT ClifLift

section thread
variable (L : Link) (env : Clif.Env) (p : Clif.Program) (Bnd : Nat → Prop) (c0 : TState)
  (Loc : Nat → Nat → Prop)

/-- **The invariants of a live activation** at its own CLIF state `s` (below its callers) with
mask `U` and dirty set `D`. -/
structure Live (g : Act) (U D : Nat → Prop) (s : Clif.State) : Prop where
  stat : StatOk L env p g
  bnd : ∀ a, PrivA (g.RL L) a → Bnd a
  dirty : ∀ a, D a → PrivA (g.RL L) a ∨ U a ∨ ¬ ∃ n, Loc a n
  reach : RReach env p c0 (.run (pushC g.ext s))
  call : s.callers = []
  ret : g.ext ≠ [] → (∃ cnm, (cnm, g.caller) ∈ L.fns) ∧ g.caller.InRange g.ra ∧
    ∀ k < g.F.fb.words.size, g.ra ≠ g.F.base + BitVec.ofNat 64 (4 * k)

/-- **The segment invariant** (`SegOkG`'s `Inv`): the activation's chain property from `x` with
its own CLIF state `s`, lifted below its callers and carrying the mask, and its invariants. -/
def Inv (g : Act) (_u : ArmState × Mon) (_c : TState × (Nat → Prop)) (x : ArmState × Mon) (d : TState × (Nat → Prop)) :
    Prop :=
  ∃ s U, d.1 = encT U (.run (pushC g.ext s)) ∧ Live L env p Bnd c0 Loc g U d.2 s ∧
    ChainP L env p g (g.r0 L) x s

/-- **An activation entered** at its ABI entry. -/
def Ent (g : Act) (u : ArmState × Mon) (c : TState × (Nat → Prop)) : Prop :=
  u.1 = g.s0 ∧ Inv L env p Bnd c0 Loc g u c u c

/-- **An activation returned** (`SegOkG`'s `Ret`): the bottom activation at its done `return`;
a callee after its `ret`, back in its caller's code with the CLIF return into the caller's
frame realized. -/
def Ret (g : Act) (_u : ArmState × Mon) (_c : TState × (Nat → Prop)) (v : ArmState × Mon) (d : TState × (Nat → Prop)) :
    Prop :=
  (g.ext = [] ∧ ∃ sR U, RetEnd (g.RL L) g.ra env p (RelW g.Γ g.f g.c) g.slots (g.r0 L) v.1 sR ∧
    AtRetS sR ∧ d.1 = encT U (.run sR)) ∨
  ∃ caller results cs, g.ext = (caller, results) :: cs ∧
    ∃ x sR n vals cm regs U, RetEnd (g.RL L) g.ra env p (RelW g.Γ g.f g.c) g.slots (g.r0 L) x sR ∧
      AtRetS sR ∧ sR.callers = [] ∧
      RetC (g.RL L) g.ra (g.r0 L) (iterN (g.RL L).step n x) ∧
      v.1 = set_program (iterN (g.RL L).step n x) (g.caller.fb.program g.caller.base) ∧
      Clif.step env p sR = .done vals cm ∧ caller.regs.setMany results vals = some regs ∧
      d.1 = encT U (.run ⟨{ caller with regs := regs }, cs, cm⟩) ∧
      (∀ a, d.2 a → PrivA (g.RL L) a ∨ U a ∨ ¬ ∃ n, Loc a n) ∧ RReach env p c0 d.1

end thread

/-- **`SegOkG` for every activation of a link of compiled functions** (WIP). -/
theorem segOkG {L : Link} {env : Clif.Env} {p : Clif.Program} {Bnd : Nat → Prop} {c0 : TState}
    {Loc : Nat → Nat → Prop} (hP : PartsOk env p c0 Loc) (hdisj : PartDisj Loc)
    {syms : String → Option Nat}
    (hlink : ∀ n f, p.func? n = some f → ∃ F, (n, F) ∈ L.fns ∧ FnOk L env p syms n F f)
    (g : Act) :
    SegOkG (RealT env p Bnd) L.M (OkB Bnd) (Ent L env p Bnd c0 Loc) (Ret L env p c0 Loc)
      (EndT env p) (Inv L env p Bnd c0 Loc g) g := by
  intro u c x d hI ls t' hr
  obtain ⟨s, U, hd1, hLv, hch⟩ := hI
  obtain ⟨d1, D⟩ := d
  simp only at hd1
  subst hd1
  obtain ⟨k, trS, t, ψ, hk, hx, hrun, href, hend⟩ := hch ls t' (prun_okPriv hLv.bnd hr)
  obtain ⟨k', d', hR, hE⟩ := seg_end (Bnd := Bnd) hLv.bnd hP hdisj hr hk g.ext hLv.reach hrun hx
    href hLv.dirty (Pz := fun s' => CallPz L g (g.r0 L) x (ls.take k) s' ∨
      RetPz L env p g (g.r0 L) x (ls.take k) s')
    (hend.imp_right (Or.imp_right fun ⟨s', h1, h2⟩ => ⟨s', h1, h2⟩))
  rcases hE with h | h | ⟨rfl, s', M, DE, hz, rfl, rfl, hMU, hDE, hreach'⟩
  · exact ⟨k', d', hR, .inl h⟩
  · exact ⟨k', d', hR, .inr (.inl h)⟩
  rcases hz with hcall | ⟨tE, hpre, hat, hret⟩
  · -- the call pause
    obtain ⟨tE, vV', vP', cM', hpre, hRQ, hPz, hat, hm2, hm3, hm4⟩ := hcall
    obtain ⟨v0, hv0, hrest⟩ := CallCompose.take_prun hr k'
    obtain rfl : v0 = tE := PRun.det (prun_okPriv hLv.bnd hv0) hpre
    by_cases hlen : ls.length ≤ k'
    · exact ⟨k', _, hR, .inl (by omega)⟩
    obtain ⟨l, rest, hdrop⟩ : ∃ l rest, ls.drop k' = l :: rest := by
      cases h : ls.drop k' with
      | nil => simp at h; omega
      | cons l rest => exact ⟨l, rest, rfl⟩
    have hm2' := hm2
    obtain ⟨stm, rest', fn, args, hbody, hcl⟩ := hat
    have hb' : s'.frame.body = { results := stm.results, inst := .call fn args } :: rest' := by
      rw [hbody, ← hcl]
    have hRe : RReach env p c0 (encT M (.run (pushC g.ext s'))) :=
      hreach'.strip (strip_encT M _).symm
    cases hstep : Clif.step env p (pushC g.ext s') with
    | stuck msg =>
      exact ⟨k', _, hR, .inr (.inl (.inl ⟨g.ext, s',
        by exact strip_encT M (.run (pushC g.ext s')), .inr (.inr (.inl ⟨msg, hstep⟩))⟩))⟩
    | trapped c' =>
      exact ⟨k', _, hR, .inr (.inl (.inl ⟨g.ext, s',
        by exact strip_encT M (.run (pushC g.ext s')), .inr (.inr (.inr ⟨c', hstep⟩))⟩))⟩
    | done v m =>
      exfalso
      rw [Clif.step_call env p _ rest' stm.results fn args (by simpa [pushC] using hb')] at hstep
      exact ClifLift.stepCall_ne_done env p _ _ _ _ _ v m hstep
    | next s1 =>
      obtain ⟨hcalls, hfunc, -, -⟩ := hm2
      obtain ⟨e, vals, callee, he, hvals, htys, hpf, -, -⟩ :=
        call_next hb' (hfunc ▸ hLv.stat.envx) hstep
      have hemem : (fn, e) ∈ g.f.externs := mem_of_lookup (hfunc ▸ he)
      obtain ⟨FB, hFBm, hFBs, hFB16, hFn⟩ := hlink e.name callee hpf
      have hsig : callee.sig = e.sig := hLv.stat.sigs _ hemem callee hpf
      sorry
  · -- the return pause
    obtain ⟨v0, hv0, hrest⟩ := CallCompose.take_prun hr k'
    obtain rfl : v0 = tE := PRun.det (prun_okPriv hLv.bnd hv0) hpre
    have hRe : RReach env p c0 (encT M (.run (pushC g.ext s'))) :=
      hreach'.strip (strip_encT M _).symm
    by_cases hroot : g.ext = []
    · exact ⟨k', (encT M (.run (pushC g.ext s')), DE), hR, .inr (.inr (.inl ⟨v0, hv0,
        .inl ⟨hroot, s', M, hret, hat, by simp [hroot, pushC]⟩⟩))⟩
    obtain ⟨caller, results, cs, hext⟩ : ∃ caller results cs, g.ext = (caller, results) :: cs := by
      cases h : g.ext with
      | nil => exact absurd h hroot
      | cons a cs => exact ⟨a.1, a.2, cs, rfl⟩
    obtain ⟨⟨cnm, hcA⟩, hrA, hra⟩ := hLv.ret hroot
    have hcall' : s'.callers = [] := by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, vals, cm, -, -, -, -, -, hdone, -⟩ := hret
      exact callers_nil_of_done hdone
    obtain ⟨k2, d2, hR2, hE2⟩ := ret_seg (Bnd := Bnd) hLv.stat hLv.bnd hcA hrA hra hext hret hat
      hcall' M DE (prun_okPriv hLv.bnd hrest)
    have hR12 : RealT env p Bnd ls (k' + k2) _ d2 := RealizedT.trans hR hR2
    rcases hE2 with h2 | ⟨vals, cm, hdone, hn, rfl, rfl⟩ | ⟨vals, cm, regs, v, hdone, hreg, hRC, hv, hv1, rfl⟩
    · refine ⟨k' + k2, d2, hR12, .inl ?_⟩
      rw [h2]; simp; omega
    · refine ⟨k' + 0, _, hR12, .inr (.inl (.inl ⟨g.ext, s',
        by exact strip_encT M (.run (pushC g.ext s')), .inr (.inr ?_)⟩))⟩
      rw [hext]; exact .inl (step_pushC_stuck hdone hn)
    · obtain ⟨v', hv', -⟩ := CallCompose.take_prun hrest k2
      obtain rfl : v' = v := PRun.det (prun_okPriv hLv.bnd hv') hv
      refine ⟨k' + k2, _, hR12, .inr (.inr (.inl ⟨v', ?_, .inr ⟨caller, results, cs, hext, v0.1, s',
        k2, vals, cm, regs, M, hret, hat, hcall', hRC, hv1, hdone, hreg, rfl, fun a h => ?_, ?_⟩⟩))⟩
      · rw [List.take_add]; exact hv0.append hv'
      · rcases h with h | h
        · rcases hDE a h with h | h | h
          · exact .inl h
          · exact .inr (.inl h)
          · exact .inr (.inr h)
        · exact .inl h
      · exact hRe.stepS (by rw [hext]; exact CallRetT.cstepS_ret_pop hcall' hat hdone hreg M)

end Concurrency.CallSegOkG
