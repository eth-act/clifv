import FV.Concurrency.CallSegPc
import FV.Concurrency.CallSegCall
import FV.Concurrency.CallSegExt

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

/-- **The static premises of a link of compiled functions** (module doc). (#581: the frame bound
`Mx` now also covers the bytes the function's stack probes write below its frame
(`probeBelow`): a callee's `R.Wf` includes `StackAvail`, which bounds them by its budget.) -/
structure LinkOk (L : Link) (env : Clif.Env) (p : Clif.Program) (syms : String → Option Nat)
    (fr : String → Option (Nat × (Clif.SlotId → Nat))) (Mx : Nat) : Prop where
  fn : ∀ n f, p.func? n = some f → ∃ F, (n, F) ∈ L.fns ∧ FnOk L env p syms n F f ∧
    fr n = some (frameDrop F.af, slotOffs F.af f) ∧ F.af.frameSize + 16 + probeBelow F.af ≤ Mx
  inside : ∀ n F, (n, F) ∈ L.fns → CallsInside F
  noSelf : ∀ n f, p.func? n = some f → ∀ e ∈ f.externs, e.2.name ≠ n
  defsRet : ∀ nA FA nB FB, (nA, FA) ∈ L.fns → (nB, FB) ∈ L.fns →
    ∀ (b : Nat) (vb : VBlock) (us : List (Reg × Reg)), FB.vc.blocks[b]? = some vb →
      (∃ k : Nat, vb.insts[k]? = some (MInst.rets us)) → CallDefsRet FA.vc (us.map (·.2))

theorem pushC_nil (s : Clif.State) (hs : s.callers = []) (ext : List (Clif.Frame × List Clif.ValueId)) :
    (pushC ext s).callers = ext := by simp [pushC, hs]

/-! ## Links with external callees (#649) -/

theorem toNat_sub_ofNat {a : BitVec 64} {d : Nat} (h : d ≤ a.toNat) :
    (a - BitVec.ofNat 64 d).toNat = a.toNat - d := by
  have hd : d < 2 ^ 64 := by have := a.isLt; omega
  rw [BitVec.toNat_sub_of_le (by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]; exact h),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]

/-- The frame, the kept addresses and the dead stack of an activation are outside its world. -/
theorem F_of_FK (R : RL) {a : BitVec 64} (h : R.FK a ∨ StackBelow R.K R.spB a) : R.F a := by
  simp only [RL.F, RL.FK, frameWG, frameW, RL.spB] at h ⊢
  rcases h with (h | h) | h
  · exact .inl (.inl h)
  · exact .inr h
  · exact .inl (.inr h)

/-- **The dead stack of an activation avoids its frame and kept addresses.** -/
theorem dead_not_FK {A : RL} (hA : A.Wf) {a : BitVec 64} (hd : StackBelow A.K A.spB a) :
    ¬ A.FK a := by
  obtain ⟨hreg, hnf⟩ := dead_region hA hd
  rintro (hf | hg)
  · rcases frameF_frame hA hf with hf | hc
    · exact hnf hf
    · exact code_not_region hA hc hreg
  · refine hA.gfree a hg ?_
    unfold Region at hreg; exact hreg

open ArmFoot ArmInstFoot in
/-- **The `bl` of a paused call into a function of the link** (`Link.call_end`'s step, for any
linked callee). -/
theorem call_stepX {L : Link} {env : Clif.Env} {p : Clif.Program} {g : Act}
    (hS : StatOk L env p g) {x : ArmState} {s' : Clif.State} {vV' vP' : VState CV ArmState}
    {cM' : MState CV ArmState} (hq : Q (g.RL L) x (.run cM')) (hP : Pause (g.RL L) (.run cM'))
    (hm2 : Match g.f g.ctx g.R g.gn g.bl g.A (RelW g.Γ g.f g.c) g.slots s' vV')
    (hm3 : PMatch g.vc g.F.vc (csem (g.RL L).F (g.RL L).ctx (g.RL L).X)
      (cEvs (g.RL L).F (g.RL L).ctx) g.Lp g.ss' (.run vV') (.run vP'))
    (hm4 : MatchRun g.cc g.ins ckeep (g.r0 L) cM' vP')
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s'.frame.body = stm :: rest)
    {fn : Clif.FnRef} {args : List Clif.ValueId} (hcl : stm.inst = .call fn args)
    {e : Clif.ExtFunc} (he : s'.frame.func.extern? fn = some e)
    (huniq : ∀ e' ∈ g.f.externs, e'.2.name = e.name → e'.2 = e)
    {vals : List Clif.Val} (hvals : s'.frame.getMany args = .ok vals)
    (htys : vals.map (·.ty) = Clif.AbiParam.tys e.sig.params)
    {F : LFn} (hB : (e.name, F) ∈ L.fns) :
    L.M x = enter F x ∧ stepEvs x = [] ∧ cls x = .plain := by
  obtain ⟨vb, us, ds, ops, hvb, hi, -, -⟩ := CallArgsL2.isel_argsAt hS.H hS.chk hS.res hS.low
    hS.ind hS.ver hS.nt hS.out0 hS.slot hS.sym hm2 hbody hcl he huniq hvals htys
  obtain ⟨b0, k0, ρ0, w0⟩ := vV'
  obtain ⟨b', vb', e', hvb', hi', -, -⟩ :=
    CallResumeAll.pmatch_call_fwd hS.H3 hS.noCall hm3 hvb hi
  cases e'
  obtain ⟨b2, k2, allocs, its, m, w2, vb2, info2, rfl, e2, -, -, -⟩ :=
    CallResumeAll.atCall_of_pause hS.noCall hS.H hS.chk hS.H3 hS.checked hP
      ⟨stm, rest, fn, args, hbody, hcl⟩ hm2 hm3 hm4
  simp only [VState.mk.injEq] at e2
  obtain ⟨rfl, rfl, -, rfl⟩ := e2
  exact step_call hS.ok hS.mem hB hS.wf hq hvb' hi' rfl

/-- **At a call pause the relation is `Q ∧ AInv`**: `RelQ` (`QA`) at a `call` item is not a return
tail (`qa_op`). -/
theorem callPz_q {L : Link} {env : Clif.Env} {p : Clif.Program} {g : Act}
    (hS : StatOk L env p g) {r₀ : Reg → CV} {t : ArmState × Mon} {s' : Clif.State}
    {vV' vP' : VState CV ArmState} {cM' : MState CV ArmState} (hq : RelQ (g.RL L) t (.run cM'))
    (hP : Pause (g.RL L) (.run cM')) (hat : AtCallS s')
    (hm2 : Match g.f g.ctx g.R g.gn g.bl g.A (RelW g.Γ g.f g.c) g.slots s' vV')
    (hm3 : PMatch g.vc g.F.vc (csem (g.RL L).F (g.RL L).ctx (g.RL L).X)
      (cEvs (g.RL L).F (g.RL L).ctx) g.Lp g.ss' (.run vV') (.run vP'))
    (hm4 : MatchRun g.cc g.ins ckeep r₀ cM' vP') :
    Q (g.RL L) t.1 (.run cM') ∧ AInv (g.RL L) (.run cM') := by
  obtain ⟨b, k, allocs, its, m, w, vb, info, rfl, -, hvb, hi, -⟩ :=
    CallResumeAll.atCall_of_pause hS.noCall hS.H hS.chk hS.H3 hS.checked hP hat hm2 hm3 hm4
  exact qa_op hq hvb hi (fun us h => by cases h)

/-- **The activation's body-entry values of the registers the prologue pushes are the ABI
entry's** (`chainP_resume`'s `hr₀` for `Act.r0`; the prologue keeps the callee-saved
registers). -/
theorem r0_saves {L : Link} {env : Clif.Env} {p : Clif.Program} {g : Act}
    (hS : StatOk L env p g) :
    ∀ r ∈ (g.RL L).af.saves, ckeep r (g.r0 L r) = ckeep r (regVal (g.RL L).s0 r) := by
  obtain ⟨-, -, -, hsv, -⟩ := RL.frame_facts hS.wf
  intro r hr
  have hcs := hsv.1 r hr
  simp only [Act.r0, locVal]
  exact congrArg (ckeep r) (regVal_calleeSaved_congr
    (fun f h1 h2 h3 h4 h5 => prologue_fields hS.wf hS.abi f h1 h3 h5 h2) r hcs)

/-- **The activations of a link with externals**: compiled program functions and externals
(`CallSegExt.XAct`). -/
inductive AG where
  | c (g : Act)
  | x (h : CallSegExt.XAct)

/-- The external activations. -/
def AG.IsX : AG → Prop
  | .c _ => False
  | .x _ => True

section threadX
variable (L : Link) (env : Clif.Env) (p : Clif.Program) (Bnd : Nat → Prop) (c0 : TState)
  (Loc : Nat → Nat → Prop) (fr : String → Option (Nat × (Clif.SlotId → Nat))) (Mx Dcap : Nat)
  (syms : String → Option Nat) (Xn : String → Prop) (xr : String → List Reg)

/-- The segment invariant: a compiled activation's `Inv` (an external has none: its contract
gives its function contract). -/
def InvX : AG → CallCompose.AT → TState × (Nat → Prop) → CallCompose.AT →
    TState × (Nat → Prop) → Prop
  | .c g => Inv L env p Bnd c0 Loc fr Mx Dcap syms g
  | .x _ => fun _ _ _ _ => False

/-- The entry: a compiled activation's `Ent`, an external's `XEnt`. -/
def EntX : AG → CallCompose.AT → TState × (Nat → Prop) → Prop
  | .c g => Ent L env p Bnd c0 Loc fr Mx Dcap syms g
  | .x h => CallSegExt.XEnt L env p Bnd c0 Loc fr Mx Dcap syms Xn h

/-- The return: a compiled activation's `Ret`, an external's `XRet`. -/
def RetX : AG → CallCompose.AT → TState × (Nat → Prop) → CallCompose.AT →
    TState × (Nat → Prop) → Prop
  | .c g => Ret L env p c0 Loc fr g
  | .x h => CallSegExt.XRet L env p c0 Loc fr syms xr h

end threadX

/-- **The static premises of a link with externals** `Xn` (return registers `xr`): `LinkOk` for
the program functions other than the externals; every external's code in the link and its CLIF
specification without stack slots; the externals' return registers `CallDefsRet` of every
caller. (#581: the frame bound `Mx` also covers the stack probes below the frame, `LinkOk`.) -/
structure LinkOkX (L : Link) (env : Clif.Env) (p : Clif.Program) (syms : String → Option Nat)
    (fr : String → Option (Nat × (Clif.SlotId → Nat))) (Mx : Nat) (Xn : String → Prop)
    (xr : String → List Reg) : Prop where
  fn : ∀ n f, p.func? n = some f → ¬ Xn n → ∃ F, (n, F) ∈ L.fns ∧ FnOk L env p syms n F f ∧
    fr n = some (frameDrop F.af, slotOffs F.af f) ∧ F.af.frameSize + 16 + probeBelow F.af ≤ Mx
  xfn : ∀ n f, p.func? n = some f → Xn n → (∃ F, (n, F) ∈ L.fns) ∧ f.slots = []
  inside : ∀ n F, (n, F) ∈ L.fns → CallsInside F
  noSelf : ∀ n f, p.func? n = some f → ∀ e ∈ f.externs, e.2.name ≠ n
  defsRet : ∀ nA FA nB FB, (nA, FA) ∈ L.fns → (nB, FB) ∈ L.fns →
    ∀ (b : Nat) (vb : VBlock) (us : List (Reg × Reg)), FB.vc.blocks[b]? = some vb →
      (∃ k : Nat, vb.insts[k]? = some (MInst.rets us)) → CallDefsRet FA.vc (us.map (·.2))
  defsRetX : ∀ nA FA n, (nA, FA) ∈ L.fns → Xn n → CallDefsRet FA.vc (xr n)

/-- A link of compiled functions is a link without externals. -/
theorem LinkOk.toX {L : Link} {env : Clif.Env} {p : Clif.Program} {syms : String → Option Nat}
    {fr : String → Option (Nat × (Clif.SlotId → Nat))} {Mx : Nat}
    (h : LinkOk L env p syms fr Mx) : LinkOkX L env p syms fr Mx (fun _ => False) (fun _ => []) :=
  ⟨fun n f hf _ => h.fn n f hf, fun _ _ _ h => h.elim, h.inside, h.noSelf, h.defsRet,
    fun _ _ _ _ h => h.elim⟩

/-- **`SegOkG` for every compiled activation of a link with externals** (module doc): at a call
pause into an external the `bl` and the CLIF call enter it (`XEnt`), and its return (`XRet`, the
contract's return facts) resumes the caller (`CallArity.resume_allAX`, `chainP_resume`). -/
theorem segOkG_ext {L : Link} {env : Clif.Env} {p : Clif.Program} {Bnd : Nat → Prop}
    {c0 : TState} {Loc : Nat → Nat → Prop} {fr : String → Option (Nat × (Clif.SlotId → Nat))}
    {Mx Dcap : Nat} {syms : String → Option Nat} {Xn : String → Prop} {xr : String → List Reg}
    (hP : PartsOk env p c0 Loc) (hdisj : PartDisj Loc)
    (hLF : ∀ f : Clif.Function, f ∈ Clif.Program.funcs p → Clif.LinkFree f)
    (hk : Clif.EnvKeepsAllocs env) (hkp : Clif.EnvKeepsPlace env)
    (hpo : PlaceOk p fr Mx) (hdep : ∀ S, RReach env p c0 (.run S) → S.callers.length < Dcap)
    (hL : LinkOkX L env p syms fr Mx Xn xr) (g : Act) :
    SegOkG (RealT env p Bnd) L.M (OkB Bnd) (EntX L env p Bnd c0 Loc fr Mx Dcap syms Xn)
      (RetX L env p c0 Loc fr syms xr) (EndT env p Dcap) (Inv L env p Bnd c0 Loc fr Mx Dcap syms g)
      (AG.c g) := by
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
    replace hRQ := callPz_q hS hRQ hPz hat hm2 hm3 hm4
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
    have hcn : callee.name = e.name := (Clif.Program.func?_some hpf).2
    have hsig : callee.sig = e.sig := hS.sigs _ hemem callee hpf
    obtain ⟨w, hmr, hmx, herrx, hsp⟩ := caller_world hS.noCall hS.H hS.chk hS.H3 hS.checked hRQ.1
      hPz hat hm2 hm3 hm4
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
    have huniq : ∀ e' ∈ g.f.externs, e'.2.name = e.name → e'.2 = e :=
      fun e' he' hn => hS.uniq e' he' _ hemem hn
    obtain ⟨FC, hFCm⟩ : ∃ F, (e.name, F) ∈ L.fns := by
      by_cases hXe : Xn e.name
      · exact (hL.xfn e.name callee hpf hXe).1
      · obtain ⟨F, hF, -⟩ := hL.fn e.name callee hpf hXe; exact ⟨F, hF⟩
    obtain ⟨hMC, hev, hcls⟩ :=
      call_stepX hS hRQ.1 hPz hm2 hm3 hm4 hbody hcl he huniq hvals htys hFCm
    let ext' := ({ s'.frame with body := rest' }, stm.results) :: g.ext
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
    by_cases hXe : Xn e.name
    · -- an external callee: entered under its contract
      obtain ⟨-, hslx⟩ := hL.xfn e.name callee hpf hXe
      obtain ⟨d, off, hfrd, hdM, -⟩ := hpo callee (Clif.Program.func?_some hpf).1
      obtain ⟨hdK, hbud⟩ := budget_call hLv'.budget hdlt hdM
      obtain ⟨hB1, hB2⟩ := spB_toNat hS.wf
      have hKs : g.K ≤ (g.RL L).spB.toNat := by
        simp only [Act.RL, act_af, act_K] at hB1 hB2 ⊢; omega
      have hspK : g.K ≤ (spv tE.1).toNat := hsp ▸ hKs
      have hspX : (spv tE.1 - BitVec.ofNat 64 d).toNat = (spv tE.1).toNat - d :=
        toNat_sub_ofNat (by omega)
      have hpl0' : s'.mem.place = some ⟨spv tE.1 :: g.sps, fr, none⟩ := by rw [hsp]; exact hpl0
      obtain ⟨-, -, hal, -, hpl1⟩ := enterSlots_at hpl0' hfrd
      let hx : CallSegExt.XAct := ⟨g, tE.1, e.name, FC, callee, vals, d,
        { s'.frame with body := rest' }, stm.results, s'.mem⟩
      have hxe : hx.ext = ext' := rfl
      have hxo : hx.opens = (s'.mem, g.ext.length) :: g.opens := rfl
      have hPA : ∀ a, hx.P a → PrivA (g.RL L) a := fun a ha =>
        F_of_FK (g.RL L) (.inr (by rw [← hsp]; exact ha))
      have hLX : CallSegExt.XLive L env p Bnd c0 Loc fr Mx Dcap hx
          (fun a => M a ∨ slotZ callee s'.mem a) DE cs := {
        bnd := fun a ha => hLv'.bnd a (hPA a ha)
        dirty := fun a ha => by
          rcases hLv'.dirty a ha with h1 | h1 | h1 | h1
          · by_cases hpa : hx.P a
            · exact .inl hpa
            · exact .inr (.inr (.inr (.inr ⟨h1, hpa⟩)))
          · exact .inr (.inl (.inl h1))
          · exact .inr (.inr (.inl h1))
          · exact .inr (.inr (.inr (.inl h1)))
        reach := hRe1
        linv := hlin1
        place := by rw [hcs4]; exact hpl1
        nv := fun a k hk hv hNa => by
          rw [hcs4] at hv
          simp only [Clif.Mem.valid, List.any_eq_true] at hv
          obtain ⟨y, hy, hcy⟩ := hv
          rcases hal y hy with hy' | ⟨q, hq, -⟩
          · have hv' : s'.mem.valid a k = true := List.any_eq_true.mpr ⟨y, hy', hcy⟩
            rcases hNa with hgN | ⟨hpa, -⟩
            · exact hLv'.nv a k hk hv' hgN
            · have hnF := (hmr.valid a k hv').2 0 hk
              simp only [Nat.add_zero] at hnF
              rw [hS.ΓF] at hnF
              exact hnF hpa
          · exact absurd (hslx ▸ hq) List.not_mem_nil
        ndead := fun a hNa hc => by
          obtain ⟨h1, h2⟩ := hc
          change (spv tE.1 - BitVec.ofNat 64 d).toNat ≤ a + (g.K - d) at h1
          change a < (spv tE.1 - BitVec.ofNat 64 d).toNat at h2
          rw [hspX] at h1 h2
          rcases hNa with hgN | ⟨-, hnp⟩
          · apply hLv'.ndead a hgN
            rw [← hsp]; constructor <;> omega
          · apply hnp
            show StackBelow g.K (spv tE.1) (BitVec.ofNat 64 a)
            have hlt : a < 2 ^ 64 := by have := (spv tE.1).isLt; omega
            show (BitVec.ofNat 64 a).toNat < (spv tE.1).toNat ∧
              (spv tE.1).toNat ≤ (BitVec.ofNat 64 a).toNat + g.K
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
            omega
        opens := by
          rw [hxo, hxe]
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
        budget := by
          rw [hxe]
          change (Dcap - (g.ext.length + 1)) * Mx ≤ g.K - d
          exact hbud
        kle := by
          change g.K - d ≤ (spv tE.1 - BitVec.ofNat 64 d).toNat
          rw [hspX]; omega }
      refine ⟨k' + 1, _, RealizedT.trans hR hR1, .inr (.inr (.inr ⟨by omega, (L.M tE.1, tE.2),
        AG.x hx, ?_, ⟨hMC, hXe, hFCm, hpf, cs, _, rfl, hLX,
          ⟨hcs1, hcs2, hcs3, hcs4, B0, hB0, hcs5, hcs6, hcs7, hcs8⟩, ?_, ?_,
          fun a hfk hsb => dead_not_FK hS.wf (by rw [← hsp]; exact hsb) hfk, hspK,
          (checkSP_iff tE.1).mp (q_stRel hRQ.1).align, herrx, hPA, g.nm, g.F, hS.mem,
          (q_stRel hRQ.1).prog, ra_in hS.wf (hL.inside _ _ hS.mem) (callPc_of_pause hS.noCall hS.H
            hS.chk hS.H3 hS.checked hRQ.1 hPz hat hm2 hm3 hm4)⟩, ?_⟩))⟩
      · rw [List.take_add, hdrop]; exact hv0.append (.cons hs hp ho .nil)
      · show CallSegExt.ArgsInRegs callee.sig vals tE.1
        rw [hsig]
        exact (CallArgsEntry.callee_args hS.noCall hS.H hS.chk hS.res hS.cu hS.low hS.ind hS.ver
          hS.nt hS.out0 hS.slot hS.sym hS.H3 hS.checked hS.uv hS.dv hRQ.1 hPz hm2 hm3 hm4 hbody hcl
          he huniq hvals htys).1
      · have hmr' : MemRel (g.RL L).F syms s'.mem w := by
          rw [← hS.ΓF, ← hLv'.syms]; exact hmr
        exact CallSegExt.memRel_mono hmr' hmx fun a ha => F_of_FK (g.RL L) (by
          rcases ha with h1 | h1
          · exact .inl h1
          · exact .inr (by rw [← hsp]; exact h1))
      · -- the external's return resumes the caller
        intro z d'' hRet
        obtain ⟨sR, rvals, cm, regs, U2, hRA, hfR, hatR, hcR, hdone, hreg, hd1, hdirty, hreach,
          hlinv, hopens, hplace⟩ := hRet
        have hrty : rvals.map (·.ty) = Clif.AbiParam.tys e.sig.returns := by
          rw [ret_tys hcR hatR hdone, hfR, hsig]
        have hD : AllocInvD s'.mem g.ext.length
            ⟨{ { s'.frame with body := rest' } with regs := regs }, g.ext, cm⟩ :=
          hopens _ (by rw [hxo]; exact List.mem_cons_self ..)
        have hcmR : cm = (sR.mem.free (sR.frame.slots.map (·.2))).leave := by
          obtain ⟨hbR, xsR, hTR⟩ := hatR
          have hst := Clif.step_term env p sR hbR
          rw [hTR] at hst
          exact ((stepTerm_ret (env := env) (p := p) (xs := xsR) hcR).2.2 rvals cm
            (hst ▸ hdone)).2
        obtain ⟨ys, hpreB, hus⟩ := hRA.rets rvals cm hdone
        obtain ⟨vV'', vP'', cM'', h1, h2, h3, h4, h5⟩ := CallArity.resume_allAX hS.wf rfl
          hS.noCall hS.H hS.chk hS.ar hS.low hS.ind hS.ver hS.nt hS.out0 hS.ΓF hS.slot hS.sym hS.H3
          hS.checked hS.dv hRQ.1 hRQ.2 hPz hat hm2 hm3 hm4 hRA.pc hRA.err hRA.sp hRA.keep
          hRA.saved hRA.prog hRA.fp (usB := (xr e.name).map fun r => (r, r)) (ysB := ys)
          (fun j v q u hj hu => by
            rw [List.getElem?_map] at hj
            cases hr : (xr e.name)[j]? with
            | none => rw [hr] at hj; cases hj
            | some r =>
              rw [hr] at hj
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hj
              obtain ⟨-, rfl⟩ := hj
              exact hus j _ u hr hu) hpreB
          (by rw [List.map_map, show ((·.2) ∘ fun r => (r, r)) = fun r : Reg => r from rfl,
            List.map_id']; exact hL.defsRetX g.nm g.F e.name hS.mem hXe)
          (FB := fun _ => False) (by rw [hLv'.syms]; exact hRA.mem)
          (fun a n hv => valid_of_allocInvD hD rfl a n (hcmR ▸ hv)) (fun _ _ => rfl)
          hbody hcl he huniq hvals htys hrty hreg
        rw [← hcmR] at h1
        let sN : Clif.State :=
          { s' with frame := { s'.frame with regs := regs, body := rest' }, mem := cm }
        have hpe : pushC g.ext sN =
            ⟨{ { s'.frame with body := rest' } with regs := regs }, g.ext, cm⟩ := by
          simp [sN, pushC, hcall']
        refine ⟨sN, U2, by rw [hpe]; exact hd1, ⟨hS, hLv'.syms, hLv'.code, hLv'.bnd, hdirty,
          by rw [hpe]; exact hreach, hcall', hLv'.ret, by rw [hpe]; exact hlinv,
          by show cm.place = _; rw [hplace, hsp], fun a k hk hv => hLv'.nv a k hk
            (valid_of_allocInvD hD rfl a k hv), hLv'.ndead, fun om hom => ⟨(hLv'.opens om hom).1,
            by rw [hpe]; exact hopens om (by rw [hxo]; exact List.mem_cons_of_mem _ hom)⟩,
          hLv'.budget, hLv'.func⟩, ?_, hnm⟩
        exact chainP_resume (mon := z.2) hS (r0_saves hS) h1 h2 h3 h4 h5
    -- a compiled callee
    obtain ⟨FB, hFBm, hFn, hfr, hMx⟩ := hL.fn e.name callee hpf hXe
    obtain ⟨hNK, hbud⟩ := budget_call hLv'.budget hdlt (N := FB.af.frameSize + 16) (by omega)
    have hpK := (budget_call hLv'.budget hdlt hMx).1
    let KB := g.K - (FB.af.frameSize + 16)
    let RB := L.act FB (enter FB tE.1) KB (g.RL L).FK
    let NB : Nat → Prop := fun a => (g.N a ∨ (PrivA (g.RL L) a ∧ ¬ PrivA RB a)) ∧
      ¬ slotZ callee s'.mem a
    obtain ⟨h, hnm', hF, hs0, hK, hG, hra, hf, hsl, hext', hcaller, hop, hN, hsps, hsyms, hSB,
        hchB, hcinB, hnest, hM, -, -, hfx, hlr⟩ :=
      callee_chainP hS hLv'.syms hLv'.code hRQ.1 hPz hm2 hm3 hm4 hbody hcl he hvals htys hFBm hsig
        hFn (KB := KB) (by omega) (by omega) (sps := g.sps) (fr := fr) (by rw [hsp]; exact hpl0)
        (by rw [hcn]; exact hfr) hB0 hcs1 hcs2 hcs3 hcs4 hcs5 hcs6 hcs7 hcs8 hcs9 ext' g.F
        ((s'.mem, g.ext.length) :: g.opens) NB ((g.RL L).spB :: g.sps)
    have hRL : h.RL L = RB := by show L.act h.F h.s0 h.K h.G = _; rw [hF, hs0, hK, hG]
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
    refine ⟨k' + 1, _, RealizedT.trans hR hR1, .inr (.inr (.inr ⟨by omega, (L.M tE.1, tE.2),
      AG.c h, ?_,
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
        exact chainP_resume (mon := z.2) hS (r0_saves hS) h1 h2 h3 hq h5
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

/-- **`SegOkG` for every activation of a link of compiled functions** (module doc; `segOkG_ext`
without externals). -/
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
  obtain ⟨k, d', hR, hE⟩ := segOkG_ext (Xn := fun _ => False) (xr := fun _ => []) hP hdisj hLF hk
    hkp hpo hdep hL.toX g u c x d hI ls t' hr
  refine ⟨k, d', hR, ?_⟩
  rcases hE with h | h | h | ⟨hk, v, h', hv, hent, hres⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · cases h' with
    | c h' => exact .inr (.inr (.inr ⟨hk, v, h', hv, hent, hres⟩))
    | x hx => exact hent.2.1.elim

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

/-- **Every compiled activation of a link with externals is realized** (module doc,
`link_composeT` with the compiled activations' `segOkG_ext` and the externals' `xfunReal` from
their trusted contract `ExtEvContractT`): every precise run of the link's machine from an
activation's entry is realized on a prefix by the CLIF thread, up to the whole run, an `EndT` end,
or the activation's return. -/
theorem funRealT_link_ext {L : Link} {env : Clif.Env} {p : Clif.Program} {Bnd : Nat → Prop}
    {c0 : TState} {Loc : Nat → Nat → Prop} {fr : String → Option (Nat × (Clif.SlotId → Nat))}
    {Mx Dcap : Nat} {syms : String → Option Nat} {Xn : String → Prop} {xr : String → List Reg}
    (hP : PartsOk env p c0 Loc) (hdisj : PartDisj Loc)
    (hLF : ∀ f : Clif.Function, f ∈ Clif.Program.funcs p → Clif.LinkFree f)
    (hk : Clif.EnvKeepsAllocs env) (hkp : Clif.EnvKeepsPlace env)
    (hpo : PlaceOk p fr Mx) (hdep : ∀ S, RReach env p c0 (.run S) → S.callers.length < Dcap)
    (hL : LinkOkX L env p syms fr Mx Xn xr) (hX : CallSegExt.ExtEvContractT L env p syms Xn xr) :
    ∀ g u c, EntX L env p Bnd c0 Loc fr Mx Dcap syms Xn g u c →
      FunRealG (RealT env p Bnd) L.M (OkB Bnd) (RetX L env p c0 Loc fr syms xr g)
        (EndT env p Dcap) u c :=
  link_composeT (Ext := AG.IsX) (Inv := InvX L env p Bnd c0 Loc fr Mx Dcap syms)
    (fun _ _ _ h => EndT.app h)
    (fun g _ _ hg h => match g, hg, h with
      | .c _, _, h => h.2
      | .x _, hg, _ => (hg trivial).elim)
    (fun g hg => match g, hg with
      | .c g, _ => segOkG_ext hP hdisj hLF hk hkp hpo hdep hL g
      | .x _, hg => (hg trivial).elim)
    (fun g _ _ hg h => match g, hg, h with
      | .c _, hg, _ => hg.elim
      | .x _, _, h => CallSegExt.xfunReal hP hdisj hLF hk hkp hpo hdep hX h)

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

/-- **The program-level contract for threads of compiled code calling compiled functions and
externals** (`realizes_linked_calls` with `funRealT_link_ext`: the externals under their trusted
event contract `ExtEvContractT`). -/
theorem realizes_linked_calls_ext {n : Nat} {L : Link} {env : Clif.Env} {p : Clif.Program}
    {Bnd : Nat → Nat → Prop} {c0 : Nat → TState} {Loc : Nat → Nat → Nat → Prop}
    {fr : String → Option (Nat × (Clif.SlotId → Nat))} {Mx : Nat} {Dcap : Nat → Nat}
    {syms : String → Option Nat} {Xn : String → Prop} {xr : String → List Backend.Reg}
    {g : Nat → Act} {sA : Nat → CallCompose.AT} {cs : Nat → TState} {D0 : Nat → Nat → Prop}
    (hP : ∀ i < n, PartsOk env p (c0 i) (Loc i)) (hdisj : ∀ i < n, PartDisj (Loc i))
    (hLF : ∀ f : Clif.Function, f ∈ Clif.Program.funcs p → Clif.LinkFree f)
    (hk : Clif.EnvKeepsAllocs env) (hkp : Clif.EnvKeepsPlace env) (hpo : PlaceOk p fr Mx)
    (hdep : ∀ i < n, ∀ S, RReach env p (c0 i) (.run S) → S.callers.length < Dcap i)
    (hL : LinkOkX L env p syms fr Mx Xn xr) (hX : CallSegExt.ExtEvContractT L env p syms Xn xr)
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
      obtain ⟨k, c', hR, -⟩ := funRealT_link_ext (hP i hi) (hdisj i hi) hLF hk hkp hpo (hdep i hi)
        hL hX (AG.c (g i)) (sA i) (cs i, D0 i) (hent i hi) ls t' hr
      exact ⟨k, c'.1, c'.2, hR⟩) hr

end Concurrency.CallSegOkGT
