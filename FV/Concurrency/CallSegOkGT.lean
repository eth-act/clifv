import FV.Concurrency.CallSegPc
import FV.Concurrency.CallSegCall

/-!
# `SegOkG` for every activation of a link of compiled functions (#473, steps 3 and 4)

* `Inv`/`Ent`/`Ret`: the segment invariant of an activation (its chain property from its own
  CLIF state below its callers, and `CallSegLive.Live`), its entry, and its return (the bottom
  activation at its done `return`; a callee after its `ret`, back in its caller's code with the
  CLIF return into the caller's frame realized, the returned state's `LInv`, the open
  activations' `AllocInvD`, the slot-placement oracle popped and the dirty set bounded);
* **`segOkG`**: `CallComposeT.SegOkG` for every activation: the chain segment up to its pause
  (`CallSegLive.seg_live`); at a call pause the `bl` and the CLIF call enter the callee
  (`callee_chainP`, its `Live` with budget `K - (frameSize + 16)` from `budget_call`), and the
  callee's return resumes the caller (`resume_ret`, `chainP_resume`); at a return pause the
  epilogue and `ret` (`ret_seg`);
* **`funRealT_link`**: `link_composeT` with every activation compiled: every precise run from an
  activation's entry is realized on a prefix up to the whole run, an `EndT` end, or the
  activation's return.

The static premises of the link (`LinkOk`): every program function compiled (`FnOk`) with its
oracle frame and its frame within `Mx` bytes, every call instruction followed by a word
(`CallsInside`), no direct self-call, the callees' `rets` registers `CallDefsRet` of every
caller.
-/

namespace Concurrency.CallSegOkGT

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck ThreadRefine IselCall IselCallRet ArmAllocThread E2E
  ClifCStepTerm IselThread CallRetsEnd CallRetsN CallSegAbi LinkedMachine LinkedMachine.Link
  CallComposeT ClifLift CallSegOkG CallSegLive CallSegPc CallSegEnt CallSegCall CallEntryRel
  CallEnterClif CallValid CallSegRun CallResumeChecks FrameDisj CallStepT ClifThreadI

section thread
variable (L : Link) (env : Clif.Env) (p : Clif.Program) (Bnd : Nat → Prop) (c0 : TState)
  (Loc : Nat → Nat → Prop) (fr : String → Option (Nat × (Clif.SlotId → Nat))) (Mx Dcap : Nat)
  (syms : String → Option Nat)

/-- **The segment invariant** (module doc). -/
def Inv (g : Act) (_u : ArmState × Mon) (_c : TState × (Nat → Prop)) (x : ArmState × Mon)
    (d : TState × (Nat → Prop)) : Prop :=
  ∃ s U, d.1 = encT U (.run (pushC g.ext s)) ∧ Live L env p Bnd c0 Loc fr Mx Dcap syms g U d.2 s ∧
    ChainP L env p g (g.r0 L) x s ∧ p.func? g.nm = some g.f

/-- **An activation entered** at its ABI entry. -/
def Ent (g : Act) (u : ArmState × Mon) (c : TState × (Nat → Prop)) : Prop :=
  u.1 = g.s0 ∧ Inv L env p Bnd c0 Loc fr Mx Dcap syms g u c u c

/-- **An activation returned** (module doc). -/
def Ret (g : Act) (_u : ArmState × Mon) (_c : TState × (Nat → Prop)) (v : ArmState × Mon)
    (d : TState × (Nat → Prop)) : Prop :=
  (g.ext = [] ∧ ∃ sR U, RetEnd (g.RL L) g.ra env p (RelW g.Γ g.f g.c) g.slots (g.r0 L) v.1 sR ∧
    AtRetS sR ∧ d.1 = encT U (.run sR)) ∨
  ∃ caller results cs, g.ext = (caller, results) :: cs ∧
    ∃ x sR n vals cm regs U, RetEnd (g.RL L) g.ra env p (RelW g.Γ g.f g.c) g.slots (g.r0 L) x sR ∧
      AtRetS sR ∧ sR.callers = [] ∧ sR.frame.func = g.f ∧
      RetC (g.RL L) g.ra (g.r0 L) (iterN (g.RL L).step n x) ∧
      v.1 = set_program (iterN (g.RL L).step n x) (g.caller.fb.program g.caller.base) ∧
      Clif.step env p sR = .done vals cm ∧ caller.regs.setMany results vals = some regs ∧
      d.1 = encT U (.run ⟨{ caller with regs := regs }, cs, cm⟩) ∧
      (∀ a, d.2 a → PrivA (g.RL L) a ∨ U a ∨ (¬ ∃ n, Loc a n) ∨ g.N a) ∧
      RReach env p c0 (.run ⟨{ caller with regs := regs }, cs, cm⟩) ∧
      Clif.LInv p ⟨{ caller with regs := regs }, cs, cm⟩ ∧
      (∀ om ∈ g.opens, AllocInvD om.1 om.2 ⟨{ caller with regs := regs }, cs, cm⟩) ∧
      cm.place = some ⟨g.sps, fr, none⟩

end thread

/-- **The static premises of a link of compiled functions** (module doc). -/
structure LinkOk (L : Link) (env : Clif.Env) (p : Clif.Program) (syms : String → Option Nat)
    (fr : String → Option (Nat × (Clif.SlotId → Nat))) (Mx : Nat) : Prop where
  fn : ∀ n f, p.func? n = some f → ∃ F, (n, F) ∈ L.fns ∧ FnOk L env p syms n F f ∧
    fr n = some (frameDrop F.af, slotOffs F.af f) ∧ F.af.frameSize + 16 ≤ Mx
  inside : ∀ n F, (n, F) ∈ L.fns → CallsInside F
  noSelf : ∀ n f, p.func? n = some f → ∀ e ∈ f.externs, e.2.name ≠ n
  defsRet : ∀ nA FA nB FB, (nA, FA) ∈ L.fns → (nB, FB) ∈ L.fns →
    ∀ (b : Nat) (vb : VBlock) (us : List (Reg × Reg)), FB.vc.blocks[b]? = some vb →
      (∃ k : Nat, vb.insts[k]? = some (MInst.rets us)) → CallDefsRet FA.vc (us.map (·.2))

theorem pushC_nil (s : Clif.State) (hs : s.callers = []) (ext : List (Clif.Frame × List Clif.ValueId)) :
    (pushC ext s).callers = ext := by simp [pushC, hs]

/-- **`SegOkG` for every activation of a link of compiled functions** (module doc). -/
theorem segOkG {L : Link} {env : Clif.Env} {p : Clif.Program} {Bnd : Nat → Prop} {c0 : TState}
    {Loc : Nat → Nat → Prop} {fr : String → Option (Nat × (Clif.SlotId → Nat))} {Mx Dcap : Nat}
    {syms : String → Option Nat}
    (hP : PartsOk env p c0 Loc) (hdisj : PartDisj Loc)
    (hLF : ∀ f : Clif.Function, f ∈ Clif.Program.funcs p → Clif.LinkFree f)
    (hk : Clif.EnvKeepsAllocs env) (hkp : Clif.EnvKeepsPlace env)
    (hpo : PlaceOk p fr Mx) (hdep : ∀ S, RReach env p c0 (.run S) → S.callers.length < Dcap)
    (hL : LinkOk L env p syms fr Mx) (g : Act) :
    SegOkG (RealT env p Bnd) L.M (OkB Bnd) (Ent L env p Bnd c0 Loc fr Mx Dcap syms)
      (Ret L env p c0 Loc fr) (EndT env p Dcap) (Inv L env p Bnd c0 Loc fr Mx Dcap syms g) g := by
  intro u c x d hI ls t' hr
  obtain ⟨s, U, hd1, hLv, hch, hnm⟩ := hI
  obtain ⟨d1, D⟩ := d
  simp only at hd1
  subst hd1
  obtain ⟨k', d', hR, hE⟩ := seg_live hP hdisj hLF hk hkp hpo hdep hLv hch hr
  rcases hE with h | h | ⟨s', M, DE, hz, rfl, hMU, hLv'⟩
  · exact ⟨k', d', hR, .inl h⟩
  · exact ⟨k', d', hR, .inr (.inl h)⟩
  have hRe : RReach env p c0 (encT M (.run (pushC g.ext s'))) :=
    hLv'.reach.strip (strip_encT M _).symm
  rcases hz with hcall | ⟨tE, hpre, hat, hret⟩
  · -- the call pause
    obtain ⟨tE, vV', vP', cM', hpre, hRQ, hPz, hat, hm2, hm3, hm4⟩ := hcall
    obtain ⟨v0, hv0, hrest⟩ := CallCompose.take_prun hr k'
    obtain rfl : tE = v0 := (PRun.det (prun_okPriv hLv.bnd hv0) hpre).symm
    have hS := hLv'.stat
    have hcall' : s'.callers = [] := hLv'.call
    by_cases hDc : Dcap ≤ g.ext.length
    · exact ⟨k', _, hR, .inr (.inl (.inl ⟨g.ext, s', by exact strip_encT M (.run (pushC g.ext s')),
        .inr (.inr (.inr (.inr ⟨hat, hDc⟩)))⟩))⟩
    by_cases hlen : ls.length ≤ k'
    · exact ⟨k', _, hR, .inl (by have := hR.1; omega)⟩
    obtain ⟨l, rest, hdrop⟩ : ∃ l rest, ls.drop k' = l :: rest := by
      cases h : ls.drop k' with
      | nil => simp at h; omega
      | cons l rest => exact ⟨l, rest, rfl⟩
    obtain ⟨stm, rest', fn, args, hbody, hcl⟩ := id hat
    have hb' : s'.frame.body = { results := stm.results, inst := .call fn args } :: rest' := by
      rw [hbody, ← hcl]
    have hpb : (pushC g.ext s').frame.body =
        { results := stm.results, inst := .call fn args } :: rest' := hb'
    cases hstep : Clif.step env p (pushC g.ext s') with
    | stuck msg =>
      exact ⟨k', _, hR, .inr (.inl (.inl ⟨g.ext, s',
        by exact strip_encT M (.run (pushC g.ext s')), .inr (.inr (.inl ⟨msg, hstep⟩))⟩))⟩
    | trapped c' =>
      exact ⟨k', _, hR, .inr (.inl (.inl ⟨g.ext, s',
        by exact strip_encT M (.run (pushC g.ext s')), .inr (.inr (.inr (.inl ⟨c', hstep⟩)))⟩))⟩
    | done v m =>
      exfalso
      rw [Clif.step_call env p _ rest' stm.results fn args hpb] at hstep
      exact ClifLift.stepCall_ne_done env p _ _ _ _ _ v m hstep
    | next s1 =>
    obtain ⟨e, vals, callee, he, hvals, htys, hpf, -, -⟩ :=
      call_next hb' (by rw [hLv'.func]; exact hS.envx) hstep
    have hemem : (fn, e) ∈ g.f.externs := mem_of_lookup (hLv'.func ▸ he)
    obtain ⟨FB, hFBm, hFn, hfr, hMx⟩ := hL.fn e.name callee hpf
    have hcn : callee.name = e.name := (Clif.Program.func?_some hpf).2
    have hsig : callee.sig = e.sig := hS.sigs _ hemem callee hpf
    obtain ⟨w, hmr, -, -, hsp⟩ := caller_world hS.noCall hS.H hS.chk hS.H3 hS.checked hRQ.1 hPz hat
      hm2 hm3 hm4
    have hpl0 : s'.mem.place = some ⟨(g.RL L).spB :: g.sps, fr, none⟩ := hLv'.place
    have hi : ∀ pl, (pushC g.ext s').mem.place = some pl → pl.init = none := by
      intro pl h
      rw [show (pushC g.ext s').mem = s'.mem from rfl, hpl0] at h
      cases h; rfl
    obtain ⟨vals', B0, cs, hvals', hB0, hs1, hcs1, hcs2, hcs3, hcs4, hcs5, hcs6, hcs7, hcs8, hcs9⟩ :=
      step_call_entry hpb he hpf hstep
    obtain rfl : vals = vals' := by
      have h := hvals.symm.trans (show s'.frame.getMany args = _ from hvals')
      cases h; rfl
    have hCI := cstepI_call hpb he hpf hstep M hi
    have e1 : (pushC g.ext s').callers = g.ext := pushC_nil s' hcall' g.ext
    rw [e1] at hs1
    subst hs1
    -- the callee's budget
    have hdlt : g.ext.length < Dcap := by omega
    obtain ⟨hNK, hbud⟩ := budget_call hLv'.budget hdlt hMx
    let KB := g.K - (FB.af.frameSize + 16)
    let RB := L.act FB (enter FB tE.1) KB (g.RL L).FK
    let ext' := ({ s'.frame with body := rest' }, stm.results) :: g.ext
    let NB : Nat → Prop := fun a => (g.N a ∨ (PrivA (g.RL L) a ∧ ¬ PrivA RB a)) ∧
      ¬ slotZ callee s'.mem a
    obtain ⟨h, hnm', hF, hs0, hK, hG, hra, hf, hsl, hext', hcaller, hop, hN, hsps, hsyms, hSB,
        hchB, hcinB, hnest, hM, hev, hcls, hfx, hlr⟩ :=
      callee_chainP hS hLv'.syms hLv'.code hRQ.1 hPz hm2 hm3 hm4 hbody hcl he hvals htys hFBm hsig
        hFn (KB := KB) (by omega) (sps := g.sps) (fr := fr) (by rw [hsp]; exact hpl0)
        (by rw [hcn]; exact hfr) hB0 hcs1 hcs2 hcs3 hcs4 hcs5 hcs6 hcs7 hcs8 hcs9 ext' g.F
        ((s'.mem, g.ext.length) :: g.opens) NB ((g.RL L).spB :: g.sps)
    have hRL : h.RL L = RB := by show L.act h.F h.s0 h.K h.G = _; rw [hF, hs0, hK, hG]
    -- the `bl` label
    rw [hdrop] at hrest
    cases hrest with
    | cons hs hp ho hrest2 =>
    obtain ⟨rfl, rfl⟩ := CallSeg.tstep_plain_nil (s := tE.1) (mon := tE.2) hs hp hev hcls
    have hR1 : RealT env p Bnd (ls.drop k') 1 (encT M (.run (pushC g.ext s')), DE)
        (encT (fun a => M a ∨ slotZ callee s'.mem a) (.run (pushC ext' cs)), DE) := by
      show RealizedT env p Bnd (ls.drop k') 1 _ _ DE DE
      rw [hdrop]; exact realizedT_nil rfl (cstepS_of_cstepI hCI) DE
    have hRe1 : RReach env p c0 (.run (pushC ext' cs)) :=
      (hRe.stepS (cstepS_of_cstepI hCI)).strip (strip_encT _ _)
    have hlin1 : Clif.LInv p (pushC ext' cs) := (Clif.step_next_linv hLF hLv'.linv hstep).1
    -- geometry
    have hdB : frameDrop FB.af ≤ FB.af.frameSize + 16 := by unfold frameDrop; split <;> omega
    have hKB : KB = g.K - (FB.af.frameSize + 16) := rfl
    have hB1 : RB.spB.toNat = (g.RL L).spB.toNat - frameDrop FB.af := by
      have := (spB_toNat hSB.wf).1; rw [hRL] at this
      simpa [RB, CallEntryRel.spv_enter, hsp] using this
    have hB2 : frameDrop FB.af + KB ≤ (g.RL L).spB.toNat := by
      have := (spB_toNat hSB.wf).2; rw [hRL] at this
      simpa [RB, CallEntryRel.spv_enter, hsp] using this
    have hspB : (h.RL L).spB = (g.RL L).spB - BitVec.ofNat 64 (frameDrop FB.af) := by
      rw [hRL]; show spv (enter FB tE.1) - _ = _; rw [CallEntryRel.spv_enter, hsp]; rfl
    have hInR : g.F.InRange (Arm.r .PC tE.1 + 4#64) :=
      ra_in hS.wf (hL.inside _ _ hS.mem) (callPc_of_pause hS.noCall hS.H hS.chk hS.H3 hS.checked
        hRQ.1 hPz hat hm2 hm3 hm4)
    have hne : g.nm ≠ e.name := fun h' => hL.noSelf g.nm g.f hnm (fn, e) hemem h'.symm
    have hraOut := ra_out hS.ok hS.mem hFBm hne hInR
    have hprivB : ∀ a, PrivA (h.RL L) a → PrivA (g.RL L) a :=
      CallSegGeo.Nested.privA_sub hSB.wf hnest fun c hc =>
        code_F hS.wf hLv'.code hFBm (by simpa [Act.RL, hs0] using hc)
    have hLvB : Live L env p Bnd c0 Loc fr Mx Dcap syms h (fun a => M a ∨ slotZ callee s'.mem a)
        DE cs := by
      refine ⟨hSB, hsyms, hcinB, fun a ha => hLv'.bnd a (hprivB a ha), fun a ha => ?_, ?_,
        hcs1, fun _ => ⟨⟨g.nm, by rw [hcaller]; exact hS.mem⟩, ?_, ?_⟩, by rw [hext']; exact hlin1,
        ?_, ?_, ?_, ?_, ?_, by rw [hf]; exact hcs2⟩
      · -- dirty
        rw [hN]
        by_cases hz : slotZ callee s'.mem a
        · exact .inr (.inl (.inr hz))
        rcases hLv'.dirty a ha with h1 | h1 | h1 | h1
        · by_cases h2 : PrivA (h.RL L) a
          · exact .inl h2
          · exact .inr (.inr (.inr ⟨.inr ⟨h1, by rw [← hRL]; exact h2⟩, hz⟩))
        · exact .inr (.inl (.inl h1))
        · exact .inr (.inr (.inl h1))
        · exact .inr (.inr (.inr ⟨.inl h1, hz⟩))
      · rw [hext']; exact hRe1
      · rw [hcaller, hra]; exact hInR
      · rw [hra, hF]; exact hraOut
      · -- place
        obtain ⟨-, -, -, -, hpl1⟩ := enterSlots_at hpl0 (by rw [hcn]; exact hfr)
        rw [hcs4]; show (Clif.enterSlots callee s'.mem).2.place = _
        rw [hpl1, hspB, hsps]
      · -- nv
        intro a k hk hv hNa
        rw [hN] at hNa
        obtain ⟨hgN, hz⟩ := hNa
        obtain ⟨-, -, hal, -, -⟩ := enterSlots_at hpl0 (by rw [hcn]; exact hfr)
        rw [hcs4] at hv
        simp only [Clif.Mem.valid, List.any_eq_true] at hv
        obtain ⟨y, hy, hcy⟩ := hv
        rcases hal y hy with hy' | ⟨q, hq, rfl⟩
        · have hv' : s'.mem.valid a k = true := List.any_eq_true.mpr ⟨y, hy', hcy⟩
          rcases hgN with hgN | ⟨hpa, -⟩
          · exact hLv'.nv a k hk hv' hgN
          · have hnF := (hmr.valid a k hv').2 0 hk
            simp only [Nat.add_zero] at hnF
            rw [hS.ΓF] at hnF
            exact hnF hpa
        · apply hz
          simp only [Clif.Alloc.contains, Bool.and_eq_true, decide_eq_true_eq] at hcy
          simp only [slotZ, hpl0, hcn, hfr, List.headD]
          exact ⟨q, hq, by omega, by omega⟩
      · -- ndead
        intro a hNa hd
        rw [hN] at hNa
        obtain ⟨hgN, -⟩ := hNa
        rw [hRL, hK] at hd
        rcases hgN with hgN | ⟨-, hnB⟩
        · apply hLv'.ndead a hgN
          constructor <;> omega
        · apply hnB
          unfold PrivA
          refine .inl (.inr ?_)
          have hlt : a < 2 ^ 64 := by have := RB.spB.isLt; omega
          show (BitVec.ofNat 64 a).toNat < RB.spB.toNat ∧ RB.spB.toNat ≤ (BitVec.ofNat 64 a).toNat + KB
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
          exact ⟨hd.2, hd.1⟩
      · -- opens
        rw [hop, hext']
        intro om hom
        rcases List.mem_cons.mp hom with rfl | hom
        · refine ⟨by simp only [ext', List.length_cons]; omega, ?_⟩
          refine allocInvD_step hLF hk hLv'.linv (allocInvD_self (pushC g.ext s') _) hstep ?_ ?_
          · rw [e1]; exact Nat.le_refl _
          · simp [pushC, hcs1, ext']
        · have h1 := hLv'.opens om hom
          refine ⟨by simp [ext']; omega, allocInvD_step hLF hk hLv'.linv h1.2 hstep ?_ ?_⟩
          · rw [e1]; omega
          · simp [pushC, hcs1, ext']; omega
      · -- budget
        rw [hext', hK]; simpa [ext'] using hbud
    refine ⟨k' + 1, _, RealizedT.trans hR hR1, .inr (.inr (.inr ⟨by omega, (L.M tE.1, tE.2), h, ?_,
      ⟨?_, cs, fun a => M a ∨ slotZ callee s'.mem a, by rw [hext'], hLvB, ?_,
        by rw [hnm', hf]; exact hpf⟩, ?_⟩))⟩
    · rw [List.take_add, hdrop]; exact hv0.append (.cons hs hp ho .nil)
    · show L.M tE.1 = h.s0; rw [hM, hs0]
    · show ChainP L env p h (h.r0 L) (L.M tE.1, tE.2) cs
      rw [hM, ← hs0]; exact hchB tE.2
    · -- the callee's return resumes the caller
      intro z d'' hRet
      rcases hRet with ⟨hne', -⟩ | ⟨caller, results, cs', hext2, xB, sR, n, rvals, cm, regs, U2,
        hretB, hatB, hcallB, hfuncB, hRC, hz1, hdone, hreg, hd1, hdirty, hreach, hlinv, hopens,
        hplace⟩
      · rw [hext'] at hne'; simp [ext'] at hne'
      rw [hext'] at hext2
      simp only [ext', List.cons.injEq, Prod.mk.injEq] at hext2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hext2
      have hrty : rvals.map (·.ty) = Clif.AbiParam.tys e.sig.returns := by
        rw [ret_tys hcallB hatB hdone, hfuncB, hf, hsig]
      have hD : AllocInvD s'.mem g.ext.length
          ⟨{ { s'.frame with body := rest' } with regs := regs }, g.ext, cm⟩ :=
        hopens _ (by rw [hop]; exact List.mem_cons_self ..)
      obtain ⟨vV'', vP'', cM'', h1, h2, h3, h4, h5⟩ := resume_ret (RB := h.RL L) hS.wf hSB.wf rfl
        hS.noCall hS.H hS.chk hS.ar hS.low hS.ind hS.ver hS.nt hS.out0 hS.ΓF hS.slot hS.sym hS.H3
        hS.checked hS.dv hRQ.1 hRQ.2 hPz hat hm2 hm3 hm4 hSB.abi
        (by simp only [Act.RL, act_fb, act_base]; rw [hra, hF]; exact hraOut)
        (by simp only [Act.RL, act_s0]; rw [hs0]; exact hfx)
        (by simp only [Act.RL, act_s0]; rw [hs0]; exact hlr)
        (fun a _ => by simp only [Act.RL, act_s0]; rw [hs0, enter_mem])
        (fun a ha => by simp only [Act.RL, act_G]; rw [hG]; exact ha) (fun _ _ => rfl)
        (hL.defsRet g.nm g.F h.nm h.F hS.mem hSB.mem) hretB hSB.ΓF (by rw [hsyms, hLv'.syms])
        hRC hdone hD rfl rfl hbody hcl he (fun e' he' hn => hS.uniq e' he' _ hemem hn) hvals htys
        hrty hreg
      let sN : Clif.State :=
        { s' with frame := { s'.frame with regs := regs, body := rest' }, mem := cm }
      have hpe : pushC g.ext sN = ⟨{ { s'.frame with body := rest' } with regs := regs }, g.ext, cm⟩ := by
        simp [sN, pushC, hcall']
      refine ⟨sN, U2,
        by rw [hpe]; exact hd1, ⟨hS, hLv'.syms, hLv'.code, hLv'.bnd, fun a ha => ?_,
        by rw [hpe]; exact hreach, hcall', hLv'.ret, by rw [hpe]; exact hlinv,
        by rw [show cm.place = _ from hplace, hsps], fun a k hk hv => hLv'.nv a k hk
          (valid_of_allocInvD hD rfl a k hv), hLv'.ndead, fun om hom => ⟨(hLv'.opens om hom).1,
          by rw [hpe]; exact hopens om (by rw [hop]; exact List.mem_cons_of_mem _ hom)⟩,
        hLv'.budget, hLv'.func⟩, ?_, hnm⟩
      · rcases hdirty a ha with h' | h' | h' | h'
        · exact .inl (hprivB a h')
        · exact .inr (.inl h')
        · exact .inr (.inr (.inl h'))
        · rw [hN] at h'
          rcases h'.1 with h' | ⟨h', -⟩
          · exact .inr (.inr (.inr h'))
          · exact .inl h'
      · have hq : Q (g.RL L) z.1 (.run cM'') := by
          rw [hz1, hcaller]; exact h4
        exact chainP_resume (mon := z.2) hS h1 h2 h3 hq h5
  · -- the return pause
    obtain ⟨v0, hv0, hrest⟩ := CallCompose.take_prun hr k'
    obtain rfl : v0 = tE := PRun.det (prun_okPriv hLv.bnd hv0) hpre
    by_cases hroot : g.ext = []
    · exact ⟨k', (encT M (.run (pushC g.ext s')), DE), hR, .inr (.inr (.inl ⟨v0, hv0,
        .inl ⟨hroot, s', M, hret, hat, by simp [hroot, pushC]⟩⟩))⟩
    obtain ⟨caller, results, cs, hext⟩ : ∃ caller results cs, g.ext = (caller, results) :: cs := by
      cases h : g.ext with
      | nil => exact absurd h hroot
      | cons a cs => exact ⟨a.1, a.2, cs, rfl⟩
    obtain ⟨⟨cnm, hcA⟩, hrA, hra⟩ := hLv.ret hroot
    have hcall' : s'.callers = [] := hLv'.call
    obtain ⟨k2, d2, hR2, hE2⟩ := ret_seg (Bnd := Bnd) hLv.stat.ok hLv.stat.mem hLv.stat.wf
      hLv.stat.abi hLv.bnd hcA hrA hra hext hret hat
      hcall' M DE (prun_okPriv hLv.bnd hrest)
    have hR12 : RealT env p Bnd ls (k' + k2) _ d2 := RealizedT.trans hR hR2
    rcases hE2 with h2 | ⟨vals, cm, hdone, hn, rfl, rfl⟩ |
      ⟨vals, cm, regs, v, hdone, hreg, hRC, hv, hv1, rfl⟩
    · refine ⟨k' + k2, d2, hR12, .inl ?_⟩
      have := hR.1; rw [h2]; simp; omega
    · refine ⟨k' + 0, _, hR12, .inr (.inl (.inl ⟨g.ext, s',
        by exact strip_encT M (.run (pushC g.ext s')), .inr (.inr ?_)⟩))⟩
      rw [hext]; exact .inl (step_pushC_stuck hdone hn)
    · obtain ⟨v', hv', -⟩ := CallCompose.take_prun hrest k2
      obtain rfl : v' = v := PRun.det (prun_okPriv hLv.bnd hv') hv
      have hstepR : Clif.step env p (pushC g.ext s') =
          .next ⟨{ caller with regs := regs }, cs, cm⟩ := by
        rw [hext, step_pushC, hdone]; simp [push, hreg]
      have hli := (Clif.step_next_linv hLF hLv'.linv hstepR).1
      have hlis : Clif.LInv p s' :=
        ⟨hLv'.linv.1, fun c hc => absurd (hcall' ▸ hc) (List.not_mem_nil)⟩
      obtain ⟨-, hcm⟩ := Clif.step_done_mem hLF hlis hdone
      have hpl : cm.place = some ⟨g.sps, fr, none⟩ := by
        rw [hcm]; simp [Clif.Mem.leave, Clif.Mem.free, hLv'.place]
      refine ⟨k' + k2, _, hR12, .inr (.inr (.inl ⟨v', ?_, .inr ⟨caller, results, cs, hext, v0.1, s',
        k2, vals, cm, regs, M, hret, hat, hcall', hLv'.func, hRC, hv1, hdone, hreg, rfl,
        fun a h => ?_, hRe.stepS (by rw [hext]; exact CallRetT.cstepS_ret_pop hcall' hat hdone hreg M)
          |>.strip (strip_encT M _), hli, fun om hom => ?_, hpl⟩⟩))⟩
      · rw [List.take_add]; exact hv0.append hv'
      · rcases h with h | h
        · exact hLv'.dirty a h
        · exact .inl h
      · have h1 := hLv'.opens om hom
        refine allocInvD_step hLF hk hLv'.linv h1.2 hstepR ?_ ?_
        · rw [pushC_nil s' hcall']; omega
        · have := h1.1; rw [hext] at this; simp at this ⊢; omega

/-- **Every activation of a link of compiled functions is realized** (module doc,
`link_composeT` with every activation compiled): every precise run of the link's machine from an
activation's entry is realized on a prefix by the CLIF thread, up to the whole run, an `EndT` end,
or the activation's return. -/
theorem funRealT_link {L : Link} {env : Clif.Env} {p : Clif.Program} {Bnd : Nat → Prop}
    {c0 : TState} {Loc : Nat → Nat → Prop} {fr : String → Option (Nat × (Clif.SlotId → Nat))}
    {Mx Dcap : Nat} {syms : String → Option Nat}
    (hP : PartsOk env p c0 Loc) (hdisj : PartDisj Loc)
    (hLF : ∀ f : Clif.Function, f ∈ Clif.Program.funcs p → Clif.LinkFree f)
    (hk : Clif.EnvKeepsAllocs env) (hkp : Clif.EnvKeepsPlace env)
    (hpo : PlaceOk p fr Mx) (hdep : ∀ S, RReach env p c0 (.run S) → S.callers.length < Dcap)
    (hL : LinkOk L env p syms fr Mx) :
    ∀ g u c, Ent L env p Bnd c0 Loc fr Mx Dcap syms g u c →
      FunRealG (RealT env p Bnd) L.M (OkB Bnd) (Ret L env p c0 Loc fr g) (EndT env p Dcap) u c :=
  link_composeT (Ext := fun _ => False) (fun _ _ _ h => EndT.app h) (fun _ _ _ _ h => h.2)
    (fun g _ => segOkG hP hdisj hLF hk hkp hpo hdep hL g) (fun _ _ _ h => h.elim)

end Concurrency.CallSegOkGT

namespace Concurrency.CallSegOkGT

open Arm ArmThread Prog ClifThread ProgE2E ThreadRefine ArmAllocThread CallComposeT PrivCohT
  CallSegOkG CallSegRun LinkedMachine Rel PrepThread

/-- **The program-level contract for threads of compiled code with calls** (`realizes_linkedT`
with each thread `i` a root activation `g i` of the link `L`, entered at `sA i` with CLIF state
`cs i` and start-dirty set `D0 i`, `funRealT_link`): every SC-per-location execution of the
realized prefixes in which no thread touches another thread's bound or start-dirty locations
(`StackDisjoint`, trusted) is realized by `CStepS` threads from the `cs i`. -/
theorem realizes_linked_calls {n : Nat} {L : Link} {env : Clif.Env} {p : Clif.Program}
    {Bnd : Nat → Nat → Prop} {c0 : Nat → TState} {Loc : Nat → Nat → Nat → Prop}
    {fr : String → Option (Nat × (Clif.SlotId → Nat))} {Mx : Nat} {Dcap : Nat → Nat}
    {syms : String → Option Nat} {g : Nat → Act} {sA : Nat → CallCompose.AT}
    {cs : Nat → TState} {D0 : Nat → Nat → Prop}
    (hP : ∀ i < n, PartsOk env p (c0 i) (Loc i)) (hdisj : ∀ i < n, PartDisj (Loc i))
    (hLF : ∀ f : Clif.Function, f ∈ Clif.Program.funcs p → Clif.LinkFree f)
    (hk : Clif.EnvKeepsAllocs env) (hkp : Clif.EnvKeepsPlace env) (hpo : PlaceOk p fr Mx)
    (hdep : ∀ i < n, ∀ S, RReach env p (c0 i) (.run S) → S.callers.length < Dcap i)
    (hL : LinkOk L env p syms fr Mx)
    (hent : ∀ i < n, Ent L env p (Bnd i) (c0 i) (Loc i) fr Mx (Dcap i) syms (g i) (sA i) (cs i, D0 i))
    {ls : Nat → List Lab} {t' : Nat → CallCompose.AT}
    (hr : ∀ i < n, PRun Policy.arm L.M (OkB (Bnd i)) (sA i) (ls i) (t' i)) :
    ∃ k : Nat → Nat, (∀ i < n, k i ≤ (ls i).length) ∧
      ∀ (PA : Traces ProgE2E.AState AKind BVal) (locsA locsC : List (Nat × Nat)) (MA0 MC0 : Bytes)
        (rfA coA rmwA : Rel PEv), PA.n = n →
        (∀ i < n, PA.tr i = conv (evTr ((ls i).take (k i)))) →
        (PA.exec locsA rfA coA rmwA).Wf →
        Acyclic (union (PA.exec locsA rfA coA rmwA).poLoc (PA.exec locsA rfA coA rmwA).com) →
        InitFirst (PA.exec locsA rfA coA rmwA) →
        (∀ i < n, ∀ a b, rmwA (.thr i a.1 a.2) (.thr i b.1 b.2) ↔
          MonPair (evTr ((ls i).take (k i))) a b) →
        locsC <+: locsA →
        (∀ q (h : q < locsA.length), locsC.length ≤ q → ∃ j < n, D0 j (locsA[q]).1) →
        (∀ q (h : q < locsC.length),
          bytesI.get MA0 (locsC[q]).1 (locsC[q]).2 = bytesI.get MC0 (locsC[q]).1 (locsC[q]).2) →
        StackDisjoint PA (fun j l => D0 j l ∨ Bnd j l) →
        ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = n ∧
          (∀ i < n, PC.st i 0 = cs i) ∧ PC.Runs (CStepS env p) ∧
          Realizes PA locsA MA0 rfA coA rmwA PC locsC MC0 φ (fun _ _ _ => True) :=
  realizes_linkedT (M := fun _ => L.M) (ok := fun i => OkB (Bnd i))
    (fun i hi ls t' hr => by
      obtain ⟨k, c', hR, -⟩ := funRealT_link (hP i hi) (hdisj i hi) hLF hk hkp hpo (hdep i hi) hL
        (g i) (sA i) (cs i, D0 i) (hent i hi) ls t' hr
      exact ⟨k, c'.1, c'.2, hR⟩) hr

end Concurrency.CallSegOkGT
