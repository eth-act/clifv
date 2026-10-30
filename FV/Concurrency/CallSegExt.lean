import FV.Concurrency.CallSegEnt
import FV.Concurrency.CallSegLive
import FV.Concurrency.CallSegPc
import FV.Concurrency.CallSegCall

/-!
# External callees of a link under their event contract (#649)

`CallSegOkGT.funRealT_link` covers links whose callees are compiled program functions. An
**external** callee (std, the allocator, libc: code we do not compile) is linked as Arm code of
the link (`(n, F) ∈ L.fns`, run by the linked machine like any linked code) with a CLIF-level
**specification**: a function `fs` of the CLIF program (`p.func? n = some fs`, entered by the
CLIF call as every program function, so `Clif.step` needs no environment extern for it). What the
external's Arm code does is not proven but assumed, by the trusted **`ExtEvContractT`**:

* `ArgsInRegs`, `Entered`: the call's arguments in their registers at the call; the CLIF state
  of the specification entered on them (`Clif.enterFunc`'s frame and memory);
* `XPriv K x`: the external's private stack, the `K` bytes below the caller's `sp` at the call
  `x` (its frame and its callees');
* `XRetA`: **the external's return** to the caller (AAPCS64): at the address after the `bl`,
  no model error, the caller's `sp`, the callee-saved registers (x19–x28, the low halves of
  v8–v15), the frame pointer x29 (AAPCS64 preserves r19–r29; Cranelift's frame addresses the
  caller's frame from it) and the caller's private memory `Fr` as at the call, back on the
  caller's program; the
  specification's CLIF memory at its `return` agreeing with the Arm memory (`MemRel`), the
  returned values in the external's return registers `rs`;
* **`ExtChain`**: the chain property of the external (as `CallSegOkG.ChainP` of a compiled
  activation): every precise run of the linked machine from the external's entry `enter F x`,
  its reads of its private stack returning its own bytes, realizes (`Refines Maps`, private set
  `XPriv K x`: **the external's Arm events are the events of its specification's CLIF run, in
  order, outside its private stack; its other writes are on its private stack**) a prefix that
  is the whole run, ends where the specification stops, or ends after the external returned
  (`XRetA`) with the specification at its own `return`;
* **`ExtEvContractT`** (trusted): `ExtChain` for every external of the link at every call
  whose arguments are in their registers, from a CLIF memory related to the Arm memory outside
  the caller's private set `Fr` and the external's stack (`MemRel`), with `Fr` outside the stack
  and the stack within the address space, `sp` 16-aligned and no model error.

The external's activation on the thread:

* `XAct`: the caller `g` paused at its call in `x`, the external `n` with code `F`, its
  specification `fs` entered on `vals` (the slot-placement oracle's drop `d`), the caller's frame
  after the call `cf` with the call's `results`, its CLIF memory `m`;
* `XLive`, `XEnt`: the invariants of the entered specification (as `CallSegLive.Live`: its
  private set within the bound, the start-dirty set, reachability, `LInv`, the oracle, the valid
  memory and the dead stack avoiding `N`, the open activations, the budget), and the entry;
* `XRet`: the external returned (`XRetA`) and the CLIF return into the caller's frame realized,
  with the caller's dirty set bound, reachability, `LInv`, the open activations' `AllocInvD` and
  the oracle popped;
* **`xfunReal`**: `FunRealG` of every entered external: the contract's chain segment lifted to
  the thread (`CallSegOkG.seg_endP`, the invariants along the specification's run as in
  `CallSegLive.seg_live`), then the CLIF return (`CallRetT.cstepS_ret_pop`, no label).
-/

namespace Concurrency.CallSegExt

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck ThreadRefine IselCall IselCallRet ArmAllocThread E2E
  ClifCStepTerm IselThread CallRetsEnd CallRetsN CallSegAbi LinkedMachine LinkedMachine.Link
  CallComposeT ClifLift CallSegOkG CallSegLive CallSegPc CallSegEnt CallSegCall CallEntryRel
  CallEnterClif CallValid CallSegRun CallResumeChecks FrameDisj CallStepT ClifThreadI

/-! ## The contract -/

/-- The call's argument values in their argument registers of `x` (`locsOf`; stack-passed
arguments are not described). -/
def ArgsInRegs (sig : Clif.Signature) (vals : List Clif.Val) (x : ArmState) : Prop :=
  ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf sig).zip vals → VHolds v (regVal x r)

/-- `s` is the bottom frame of `fs` entered on `vals` from the memory `m` (`Clif.enterFunc`). -/
def Entered (fs : Clif.Function) (vals : List Clif.Val) (m : Clif.Mem) (s : Clif.State) : Prop :=
  s.callers = [] ∧ s.frame.func = fs ∧ s.frame.slots = (Clif.enterSlots fs m).1 ∧
    s.mem = (Clif.enterSlots fs m).2 ∧ ∃ B0, fs.blocks[0]? = some B0 ∧
      s.frame.body = B0.body ∧ s.frame.term = B0.term ∧
      Clif.Regs.empty.setMany (B0.params.map (·.1)) vals = some s.frame.regs ∧
      vals.map (·.ty) = B0.params.map (·.2)

/-- The external's private stack: the `K` bytes below the caller's `sp` at the call `x`. -/
def XPriv (K : Nat) (x : ArmState) (a : Nat) : Prop := StackBelow K (spv x) (BitVec.ofNat 64 a)

/-- **The return of an external** called at `x` (module doc). -/
structure XRetA (syms : String → Option Nat) (rs : List Reg) (Fr : BitVec 64 → Prop)
    (env : Clif.Env) (p : Clif.Program) (x : ArmState) (s' : Clif.State) (v : ArmState) : Prop where
  pc : Arm.r .PC v = Arm.r .PC x + 4#64
  err : Arm.r .ERR v = .None
  sp : spv v = spv x
  saved : ∀ r ∈ calleeSaved, ckeep r (regVal v r) = ckeep r (regVal x r)
  keep : ∀ a, Fr a → v.mem a = x.mem a
  prog : v.program = x.program
  fp : xreg 29 v = xreg 29 x
  mem : MemRel (fun _ => False) syms s'.mem v
  rets : ∀ vals cm, Clif.step env p s' = .done vals cm → ∃ ys : List CV, PrefixHold vals ys ∧
    ∀ (j : Nat) (r : Reg) (y : CV), rs[j]? = some r → ys[j]? = some y → regVal v r = y

/-- **The chain property of an external** called at `x` with code `F`, from the CLIF state `s`
of its specification (module doc). -/
def ExtChain (L : Link) (env : Clif.Env) (p : Clif.Program) (syms : String → Option Nat)
    (rs : List Reg) (K : Nat) (Fr : BitVec 64 → Prop) (F : LFn) (x : ArmState) (mon : Mon)
    (s : Clif.State) : Prop :=
  ∀ ls t', PRun Policy.arm L.M (OkB (XPriv K x)) (enter F x, mon) ls t' →
    ∃ k trS t ψ, k ≤ ls.length ∧ CallCompose.XClosed (evTr (ls.take k)) ∧
      CRun env p (.run s) trS t ∧
      Refines Maps (XPriv K x) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ IselThread.Stop env p t ∨ ∃ s', t = .run s' ∧ s'.callers = [] ∧
        AtRetS s' ∧ ∃ v, PRun Policy.arm L.M (OkB (XPriv K x)) (enter F x, mon) (ls.take k) v ∧
          XRetA syms rs Fr env p x s' v.1)

/-- **The event contract of the externals `Xn` of a link** with return registers `xr`
(trusted; module doc). -/
structure ExtEvContractT (L : Link) (env : Clif.Env) (p : Clif.Program)
    (syms : String → Option Nat) (Xn : String → Prop) (xr : String → List Reg) : Prop where
  chain : ∀ n F fs, Xn n → (n, F) ∈ L.fns → p.func? n = some fs →
    ∀ (x : ArmState) (mon : Mon) (K : Nat) (Fr : BitVec 64 → Prop) (m : Clif.Mem)
      (vals : List Clif.Val) (s : Clif.State), Entered fs vals m s → ArgsInRegs fs.sig vals x →
      MemRel (fun a => Fr a ∨ StackBelow K (spv x) a) syms m x →
      (∀ a, Fr a → ¬ StackBelow K (spv x) a) → K ≤ (spv x).toNat → (spv x).toNat % 16 = 0 →
      Arm.r .ERR x = .None → (∃ nc Fc, (nc, Fc) ∈ L.fns ∧ x.program = Fc.fb.program Fc.base ∧
        Fc.InRange (Arm.r .PC x + 4#64)) → ExtChain L env p syms (xr n) K Fr F x mon s

/-! ## The external's activation -/

/-- **An external activation** (module doc). -/
structure XAct where
  g : Act
  x : ArmState
  n : String
  F : LFn
  fs : Clif.Function
  vals : List Clif.Val
  d : Nat
  cf : Clif.Frame
  results : List Clif.ValueId
  m : Clif.Mem

/-- **A memory relation for a smaller frame set, on a state agreeing outside the frame.** -/
theorem memRel_mono {F F' : BitVec 64 → Prop} {syms : String → Option Nat} {cm : Clif.Mem}
    {w x : ArmState} (h : MemRel F syms cm w) (hx : ∀ a, ¬ F a → x.mem a = w.mem a)
    (hF : ∀ a, F' a → F a) : MemRel F' syms cm x where
  bytes a b hv hb := by
    have hF0 : ¬ F (BitVec.ofNat 64 a) := by simpa using (h.valid a 1 hv).2 0 Nat.zero_lt_one
    have := h.bytes a b hv hb
    unfold Arm.read_mem at this ⊢
    rw [← this]
    simp only [Arm.read_store, hx _ hF0]
  valid a n hv := ⟨(h.valid a n hv).1, fun k hk hF' => (h.valid a n hv).2 k hk (hF _ hF')⟩
  symbols := h.symbols

namespace XAct

/-- The CLIF callers of the specification: the caller's frame below its own callers. -/
def ext (h : XAct) : List (Clif.Frame × List Clif.ValueId) := (h.cf, h.results) :: h.g.ext

/-- The open activations: the caller's, at its call, and its callers'. -/
def opens (h : XAct) : List (Clif.Mem × Nat) := (h.m, h.g.ext.length) :: h.g.opens

/-- The external's private stack. -/
def P (h : XAct) : Nat → Prop := XPriv h.g.K h.x

/-- The addresses no CLIF read of the specification starts at. -/
def N (L : Link) (h : XAct) : Nat → Prop := fun a => h.g.N a ∨ (PrivA (h.g.RL L) a ∧ ¬ h.P a)

/-- The slot-placement oracle's stack pointer of the specification. -/
def spX (h : XAct) : BitVec 64 := spv h.x - BitVec.ofNat 64 h.d

/-- The specification's callee budget. -/
def KX (h : XAct) : Nat := h.g.K - h.d

end XAct

section act
variable (L : Link) (env : Clif.Env) (p : Clif.Program) (Bnd : Nat → Prop) (c0 : TState)
  (Loc : Nat → Nat → Prop) (fr : String → Option (Nat × (Clif.SlotId → Nat))) (Mx Dcap : Nat)
  (syms : String → Option Nat)

/-- **The invariants of the entered specification** (module doc). -/
structure XLive (h : XAct) (U D : Nat → Prop) (s : Clif.State) : Prop where
  bnd : ∀ a, h.P a → Bnd a
  dirty : ∀ a, D a → h.P a ∨ U a ∨ (¬ ∃ n, Loc a n) ∨ h.N L a
  reach : RReach env p c0 (.run (pushC h.ext s))
  linv : Clif.LInv p (pushC h.ext s)
  place : s.mem.place = some ⟨h.spX :: spv h.x :: h.g.sps, fr, none⟩
  nv : ∀ a k, 0 < k → s.mem.valid a k = true → ¬ h.N L a
  ndead : ∀ a, h.N L a → ¬ (h.spX.toNat ≤ a + h.KX ∧ a < h.spX.toNat)
  opens : ∀ om ∈ h.opens, om.2 < h.ext.length ∧ AllocInvD om.1 om.2 (pushC h.ext s)
  budget : (Dcap - h.ext.length) * Mx ≤ h.KX
  kle : h.KX ≤ h.spX.toNat

/-- **An external entered** (module doc): the linked machine at the external's code, the CLIF
thread in its entered specification, and the contract's entry premises. -/
def XEnt (Xn : String → Prop) (h : XAct) (u : CallCompose.AT) (c : TState × (Nat → Prop)) :
    Prop :=
  u.1 = enter h.F h.x ∧ Xn h.n ∧ (h.n, h.F) ∈ L.fns ∧ p.func? h.n = some h.fs ∧
    ∃ s U, c.1 = encT U (.run (pushC h.ext s)) ∧ XLive L env p Bnd c0 Loc fr Mx Dcap h U c.2 s ∧
      Entered h.fs h.vals h.m s ∧ ArgsInRegs h.fs.sig h.vals h.x ∧
      MemRel (fun a => (h.g.RL L).FK a ∨ StackBelow h.g.K (spv h.x) a) syms h.m h.x ∧
      (∀ a, (h.g.RL L).FK a → ¬ StackBelow h.g.K (spv h.x) a) ∧ h.g.K ≤ (spv h.x).toNat ∧
      (spv h.x).toNat % 16 = 0 ∧ Arm.r .ERR h.x = .None ∧ (∀ a, h.P a → PrivA (h.g.RL L) a) ∧
      ∃ nc Fc, (nc, Fc) ∈ L.fns ∧ h.x.program = Fc.fb.program Fc.base ∧
        Fc.InRange (Arm.r .PC h.x + 4#64)

/-- **An external returned** (module doc). -/
def XRet (xr : String → List Reg) (h : XAct) (_u : CallCompose.AT) (_c : TState × (Nat → Prop))
    (v : CallCompose.AT) (d : TState × (Nat → Prop)) : Prop :=
  ∃ sR rvals cm regs U, XRetA syms (xr h.n) (h.g.RL L).FK env p h.x sR v.1 ∧
    sR.frame.func = h.fs ∧ AtRetS sR ∧ sR.callers = [] ∧ Clif.step env p sR = .done rvals cm ∧
    h.cf.regs.setMany h.results rvals = some regs ∧
    d.1 = encT U (.run ⟨{ h.cf with regs := regs }, h.g.ext, cm⟩) ∧
    (∀ a, d.2 a → PrivA (h.g.RL L) a ∨ U a ∨ (¬ ∃ n, Loc a n) ∨ h.g.N a) ∧
    RReach env p c0 (.run ⟨{ h.cf with regs := regs }, h.g.ext, cm⟩) ∧
    Clif.LInv p ⟨{ h.cf with regs := regs }, h.g.ext, cm⟩ ∧
    (∀ om ∈ h.opens, AllocInvD om.1 om.2 ⟨{ h.cf with regs := regs }, h.g.ext, cm⟩) ∧
    cm.place = some ⟨spv h.x :: h.g.sps, fr, none⟩

end act

/-! ## The external's function contract -/

section xfun
variable {L : Link} {env : Clif.Env} {p : Clif.Program} {Bnd : Nat → Prop} {c0 : TState}
  {Loc : Nat → Nat → Prop} {fr : String → Option (Nat × (Clif.SlotId → Nat))} {Mx Dcap : Nat}
  {syms : String → Option Nat} {Xn : String → Prop} {xr : String → List Reg}

/-- **Every entered external is realized up to its return** (module doc). -/
theorem xfunReal (hP : PartsOk env p c0 Loc) (hdisj : PartDisj Loc)
    (hLF : ∀ f : Clif.Function, f ∈ Clif.Program.funcs p → Clif.LinkFree f)
    (hk : Clif.EnvKeepsAllocs env) (hkp : Clif.EnvKeepsPlace env)
    (hpo : PlaceOk p fr Mx) (hdep : ∀ S, RReach env p c0 (.run S) → S.callers.length < Dcap)
    (hX : ExtEvContractT L env p syms Xn xr) {h : XAct} {u : CallCompose.AT}
    {c : TState × (Nat → Prop)} (he : XEnt L env p Bnd c0 Loc fr Mx Dcap syms Xn h u c) :
    FunRealG (RealT env p Bnd) L.M (OkB Bnd) (XRet L env p c0 Loc fr syms xr h)
      (EndT env p Dcap) u c := by
  intro ls t' hr
  obtain ⟨hu, hXn, hFm, hpf, s, U, hc1, hXL, hEn, hAr, hMR, hFK, hK, hal, herr, hPA, hcl⟩ := he
  obtain ⟨u1, mon⟩ := u
  obtain ⟨c1, D⟩ := c
  simp only at hu hc1
  subst hu hc1
  have hr' : PRun Policy.arm L.M (OkB h.P) (enter h.F h.x, mon) ls t' :=
    PRun.mono (fun _ _ ho e he hd hpa => ho e he hd (hXL.bnd _ hpa)) hr
  obtain ⟨k, trS, t, ψ, hk', hx, hrun, href, hend⟩ :=
    hX.chain h.n h.F h.fs hXn hFm hpf h.x mon h.g.K (h.g.RL L).FK h.m h.vals s hEn hAr hMR hFK
      hK hal herr hcl ls t' hr'
  obtain ⟨hcall, hfunc, -⟩ := hEn
  have hlinS : Clif.LInv p s :=
    ⟨hXL.linv.1, fun c hc => absurd (hcall ▸ hc) List.not_mem_nil⟩
  have hsI : SegInv p fr Mx h.spX (spv h.x :: h.g.sps) h.KX s.mem s :=
    segInv_start hlinS hcall hXL.place
  obtain ⟨hacc, -⟩ := seg_parts hP hXL.reach hrun
  have hev := segInv_crun hLF hk hkp hpo hXL.kle hdep hXL.budget hrun hXL.reach hsI
  have hN : ∀ q y, evAt trS q = some y → y.dir = .R → ¬ h.N L y.loc := by
    intro q y hy hR hNy
    have hn : 0 < y.n := (hacc q y hy).2 hR
    obtain ⟨evs, hm, hye⟩ := mem_of_evAt hy
    rcases hev evs hm y hye (by rw [hR]; decide) with hv | ⟨h1, h2⟩
    · exact hXL.nv _ _ hn hv hNy
    · exact hXL.ndead _ hNy ⟨h1, by omega⟩
  obtain ⟨k2, d2, hR2, hE2⟩ := seg_endP (Bnd := Bnd) (Dcap := Dcap) hXL.bnd hP hdisj hr hk' h.ext
    hXL.reach hrun hx href (N := h.N L) hXL.dirty hN
    (Pz := fun s' => s'.callers = [] ∧ AtRetS s' ∧ ∃ v, PRun Policy.arm L.M (OkB h.P)
      (enter h.F h.x, mon) (ls.take k) v ∧ XRetA syms (xr h.n) (h.g.RL L).FK env p h.x s' v.1)
    hend
  rcases hE2 with h' | h' | ⟨rfl, s', M, DE, ⟨hcall', hat, v, hv, hRA⟩, rfl, rfl, -, hDE, hreach'⟩
  · exact ⟨k2, d2, hR2, .inl h'⟩
  · exact ⟨k2, d2, hR2, .inr (.inl h')⟩
  -- the invariants along the specification's run
  obtain ⟨⟨hli, hop, hsI', hbot⟩, -⟩ := crun_preserve (c0 := c0) (ext := h.ext)
    (Q := fun S => Clif.LInv p (pushC h.ext S) ∧
      (∀ om ∈ h.opens, om.2 < h.ext.length ∧ AllocInvD om.1 om.2 (pushC h.ext S)) ∧
      SegInv p fr Mx h.spX (spv h.x :: h.g.sps) h.KX s.mem S ∧ Clif.State.bottom S = h.fs)
    (fun S evs S1 hRS hs ⟨h1, h2, h3, h4⟩ => by
      refine ⟨linv_cstep hLF hs h1, fun om hom => ⟨(h2 om hom).1,
        allocInvD_cstep hLF hk hs h1 (Nat.le_of_lt (h2 om hom).1) (h2 om hom).2⟩, ?_, ?_⟩
      · have hR1 : RReach env p c0 (.run (pushC h.ext S1)) := hRS.step (cstep_pushC hs)
        obtain ⟨B, S2, hst, he⟩ := cstep_next hs
        have hc2 : S2.callers = S1.callers := congrArg (·.callers) he
        have hd1 : S2.callers.length * Mx ≤ h.KX := by
          have := hdep _ hR1
          simp only [pushC, List.length_append] at this
          rw [hc2]
          calc S1.callers.length * Mx ≤ (Dcap - h.ext.length) * Mx :=
                Nat.mul_le_mul_right _ (by omega)
            _ ≤ h.KX := hXL.budget
        exact segInv_congr he (segInv_step hLF hk hkp hpo hXL.kle (segInv_withBytes.mpr h3) hst hd1)
      · obtain ⟨B, S2, hst, he⟩ := cstep_next hs
        have hc2 : S2.callers = S1.callers := congrArg (·.callers) he
        have hf2 : S2.frame = S1.frame := congrArg (·.frame) he
        have hI : Clif.LInv p (withBytes S B) := h3.linv
        have hb := (Clif.step_next_linv hLF hI hst).2
        have e : Clif.State.bottom S1 = Clif.State.bottom S2 := by
          simp only [Clif.State.bottom, hc2, hf2]
        rw [e, hb]; exact h4)
    hrun hXL.reach ⟨hXL.linv, hXL.opens, hsI, by simp [Clif.State.bottom, hcall, hfunc]⟩
  have hfunc' : s'.frame.func = h.fs := by simpa [Clif.State.bottom, hcall'] using hbot
  obtain ⟨l, hpl', hlen, -⟩ := hsI'.place
  rw [hcall'] at hlen
  obtain rfl : l = [] := List.eq_nil_of_length_eq_zero hlen
  obtain ⟨v0, hv0, -⟩ := CallCompose.take_prun hr k2
  obtain rfl : v0 = v :=
    PRun.det (PRun.mono (fun _ _ ho e he hd hpa => ho e he hd (hXL.bnd _ hpa)) hv0) hv
  -- the CLIF return
  obtain ⟨hbody, xs, hT⟩ := hat
  have hst0 := Clif.step_term env p s' hbody
  rw [hT] at hst0
  obtain ⟨hnn, -, hdn⟩ := stepTerm_ret (env := env) (p := p) (s := s') (xs := xs) hcall'
  have hRe : RReach env p c0 (encT M (.run (pushC h.ext s'))) :=
    hreach'.strip (strip_encT M _).symm
  cases hstep : Clif.step env p s' with
  | next s1 => exact absurd (hst0 ▸ hstep) (hnn s1)
  | trapped c =>
    exact ⟨k2, _, hR2, .inr (.inl (.inl ⟨h.ext, s', strip_encT M (.run (pushC h.ext s')),
      .inr (.inr (.inr (.inl ⟨c, by rw [step_pushC, hstep]; rfl⟩)))⟩))⟩
  | stuck msg =>
    exact ⟨k2, _, hR2, .inr (.inl (.inl ⟨h.ext, s', strip_encT M (.run (pushC h.ext s')),
      .inr (.inr (.inl ⟨msg, by rw [step_pushC, hstep]; rfl⟩))⟩))⟩
  | done rvals cm =>
    have hcm : cm = (s'.mem.free (s'.frame.slots.map (·.2))).leave :=
      (hdn rvals cm (hst0 ▸ hstep)).2
    cases hreg : h.cf.regs.setMany h.results rvals with
    | none =>
      exact ⟨k2, _, hR2, .inr (.inl (.inl ⟨h.ext, s', strip_encT M (.run (pushC h.ext s')),
        .inr (.inr (.inl (step_pushC_stuck hstep hreg)))⟩))⟩
    | some regs =>
      have hat' : AtRetS s' := ⟨hbody, xs, hT⟩
      have hpop := CallRetT.cstepS_ret_pop (env := env) (p := p) (cs := h.g.ext) hcall' hat' hstep
        hreg M
      have hR3 : RealizedT env p Bnd (ls.drop k2) 0 (encT M (.run (pushC h.ext s')))
          (encT M (.run ⟨{ h.cf with regs := regs }, h.g.ext, cm⟩)) DE (fun a => DE a ∨ False) :=
        realizedT_priv (Nat.zero_le _) (fun q y hy => by simp [evTr, evAt] at hy)
          (fun l hl => by simp at hl) (fun x hx => by simp at hx; exact hx) (.cons hpop .nil)
          (fun _ h => h.elim) DE
      have hstepR : Clif.step env p (pushC h.ext s') =
          .next ⟨{ h.cf with regs := regs }, h.g.ext, cm⟩ := by
        rw [step_pushC, hstep]; simp [push, XAct.ext, hreg]
      have hlen' : (pushC h.ext s').callers.length = h.g.ext.length + 1 := by
        simp [pushC, hcall', XAct.ext]
      refine ⟨k2 + 0, (encT M (.run ⟨{ h.cf with regs := regs }, h.g.ext, cm⟩),
        fun a => DE a ∨ False), RealizedT.trans hR2 hR3, .inr (.inr ⟨v0, hv0, s', rvals, cm, regs,
        M, hRA, hfunc', hat', hcall', hstep, hreg, rfl, fun a ha => ?_,
        (hRe.stepS hpop).strip (strip_encT M _), (Clif.step_next_linv hLF hli hstepR).1,
        fun om hom => ?_, ?_⟩)⟩
      · rcases ha with ha | ha
        · rcases hDE a ha with h1 | h1 | h1 | h1 | ⟨h1, -⟩
          · exact .inl (hPA a h1)
          · exact .inr (.inl h1)
          · exact .inr (.inr (.inl h1))
          · exact .inr (.inr (.inr h1))
          · exact .inl h1
        · exact ha.elim
      · have h1 := hop om hom
        refine allocInvD_step hLF hk hli h1.2 hstepR ?_ ?_
        · rw [hlen']; have := h1.1; simp [XAct.ext] at this; omega
        · have := h1.1; simp [XAct.ext] at this; simp; omega
      · rw [hcm]; simp [Clif.Mem.leave, Clif.Mem.free, hpl']

end xfun

end Concurrency.CallSegExt
