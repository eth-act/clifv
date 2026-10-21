import FV.Opt.Proof.SemFacts

/-!
# Simulations covering `call_indirect` and `try_call`/`try_call_indirect` (S1)

`Opt.IsSim` (`FV/Opt/Proof/SemSim.lean`) relates the local steps `lstep` of two frames;
`lstep` is stuck at a `call_indirect` statement and at a `try_call`/`try_call_indirect`
terminator, so `Opt.runLoop_refines` needs source runs without them (`CIFree`). Here the frame
relations carry two more obligations:

* `CIOk`: at a `call_indirect`, the target catches up (stuttering local steps) to a
  `call_indirect` whose prelude (`ciArgs`: the call site's signature, the callee address, the
  argument values) is the source's, and binding the call's results keeps the relation
  (`Cont`);
* `TryOk`: at a `try_call` (`try_call_indirect`), the target catches up to one whose prelude
  (`tcArgs`/`ticArgs`: the number of results and the normal-return successor; `callArgs`/
  `ciArgs`: the callee and argument values) gives the same callee and values, and binding the
  results (at each side's fresh values, `Function.freshValue`) and entering the normal-return
  successor keeps the relation (`TCont`).

`IsSimX` is `IsSim` with both; `FunSimX` the corresponding function simulation (with the
externs kept, which an indirect call of an extern reads: `Program.externNames`). Programs:
`runLoop_refinesX` lifts pointwise `FunSimX` to the runs of the programs, every source run
(no `CIFree` premise), and the target run of a source run that returns or traps reaches only
states with the call depths of source states (`Reach`, for the peak-stack theorems).
-/

namespace Opt

open Clif

/-! ## Preludes -/

/-- The prelude of `Clif.stepCallIndirect`: the call site's signature, the callee address, the
argument values. -/
def ciArgs (fr : Frame) (sig : Nat) (callee : ValueId) (args : List ValueId) :
    Res (Signature × Nat × List Val) := do
  let declared ← Res.ofOption s!"unknown signature sig{sig}" (fr.func.sigDecls.lookup sig)
  let cv ← fr.get callee
  let cv64 ← Res.ofOption "call_indirect: callee is not i64" (cv.as? .i64)
  let vals ← fr.getMany args
  pure (declared, cv64.toNat, vals)

/-- The continuation of `Clif.stepCallIndirect` after its prelude. -/
def ciCont (env : Env) (p : Program) (s : State) (rest : List Stmt) (results : List ValueId)
    (sig : Nat) (declared : Signature) (addr : Nat) (vals : List Val) : StepResult :=
  let fr := s.frame
  match p.funcs.find? fun f => (s.mem.symbols f.name) == some addr with
  | some target =>
    if declared.abiMatch target.sig then
      StepResult.ofRes (enterFunc target vals s.mem) fun (fr', mem') =>
        .next { frame := fr', callers := ({ fr with body := rest }, results) :: s.callers,
                mem := mem' }
    else .stuck s!"call_indirect sig{sig}: signature does not match %{target.name}"
  | none =>
    StepResult.ofRes (callExternAt env p s.mem declared addr vals) fun (rvals, mem') =>
      continueWith s rest results rvals mem'

theorem stepCallIndirect_eq (env : Env) (p : Program) (s : State) (rest : List Stmt)
    (results : List ValueId) (sig : Nat) (callee : ValueId) (args : List ValueId) :
    stepCallIndirect env p s rest results sig callee args =
      StepResult.ofRes (ciArgs s.frame sig callee args) fun (d, a, vals) =>
        ciCont env p s rest results sig d a vals := rfl

theorem stepCall_eq (env : Env) (p : Program) (s : State) (rest : List Stmt)
    (results : List ValueId) (fn : FnRef) (args : List ValueId) :
    stepCall env p s rest results fn args =
      StepResult.ofRes (callArgs s.frame fn args) fun (ext, vals) =>
        callCont env p s rest results ext vals := rfl

/-- The prelude of `Clif.stepTryCall`: the number of results, their first value, the
normal-return successor. -/
def tcArgs (fr : Frame) (fn : FnRef) (et : ExnTable) : Res (Nat × ValueId × BlockCall) := do
  let ext ← Res.ofOption s!"unknown function reference fn{fn}" (fr.func.extern? fn)
  let sig ← Res.ofOption s!"unknown signature sig{et.sig}" (fr.func.sigDecls.lookup et.sig)
  Res.check (AbiParam.tys sig.params == AbiParam.tys ext.sig.params &&
      AbiParam.tys sig.returns == AbiParam.tys ext.sig.returns)
    s!"try_call: sig{et.sig} is not the signature of fn{fn}"
  let base := fr.func.freshValue
  let bc ← tryNormal et base
  pure (ext.sig.returns.length, base, bc)

/-- The prelude of `Clif.stepTryCallIndirect`. -/
def ticArgs (fr : Frame) (et : ExnTable) : Res (Nat × ValueId × BlockCall) := do
  let sig ← Res.ofOption s!"unknown signature sig{et.sig}" (fr.func.sigDecls.lookup et.sig)
  let base := fr.func.freshValue
  let bc ← tryNormal et base
  pure (sig.returns.length, base, bc)

/-- The frame of a `try_call` once its call returns: the jump to the normal-return successor. -/
def jumpFrame (fr : Frame) (bc : BlockCall) : Frame := { fr with body := [], term := .jump bc }

/-- The result values of a `try_call` with `n` results bound from `base`. -/
def tryRets (n : Nat) (base : ValueId) : List ValueId := (List.range n).map (base + ·)

theorem getMany_jump (fr : Frame) (bc : BlockCall) (xs : List ValueId) :
    (jumpFrame fr bc).getMany xs = fr.getMany xs := getMany_congr (fun _ _ => rfl)

theorem callArgs_jump (fr : Frame) (bc : BlockCall) (fn : FnRef) (args : List ValueId) :
    callArgs (jumpFrame fr bc) fn args = callArgs fr fn args := by
  unfold callArgs; rw [getMany_jump]; rfl

theorem ciArgs_jump (fr : Frame) (bc : BlockCall) (sig : Nat) (callee : ValueId)
    (args : List ValueId) : ciArgs (jumpFrame fr bc) sig callee args = ciArgs fr sig callee args := by
  unfold ciArgs; rw [getMany_jump]; rfl

theorem stepTryCall_eq (env : Env) (p : Program) (s : State) (fn : FnRef) (args : List ValueId)
    (et : ExnTable) :
    stepTryCall env p s fn args et =
      StepResult.ofRes (tcArgs s.frame fn et) fun (n, base, bc) =>
        StepResult.ofRes (callArgs s.frame fn args) fun (ext, vals) =>
          callCont env p { s with frame := jumpFrame s.frame bc } [] (tryRets n base) ext vals := by
  unfold stepTryCall
  show StepResult.ofRes (tcArgs s.frame fn et) _ = _
  congr 1
  funext x
  obtain ⟨n, base, bc⟩ := x
  rw [← callArgs_jump s.frame bc]
  rfl

theorem stepTryCallIndirect_eq (env : Env) (p : Program) (s : State) (callee : ValueId)
    (args : List ValueId) (et : ExnTable) :
    stepTryCallIndirect env p s callee args et =
      StepResult.ofRes (ticArgs s.frame et) fun (n, base, bc) =>
        StepResult.ofRes (ciArgs s.frame et.sig callee args) fun (d, a, vals) =>
          ciCont env p { s with frame := jumpFrame s.frame bc } [] (tryRets n base) et.sig d a
            vals := by
  unfold stepTryCallIndirect
  show StepResult.ofRes (ticArgs s.frame et) _ = _
  congr 1
  funext x
  obtain ⟨n, base, bc⟩ := x
  rw [← ciArgs_jump s.frame bc]
  rfl

/-! ## Frame obligations -/

/-- After a `try_call` returns: binding the results `vs` (of types `rtys`) at `rs`/`rs'` and
entering the normal-return successors `bc`/`bc'` gives frames related by `R`. -/
def TCont (R : Frame → Frame → Prop) (fr : Frame) (rs : List ValueId) (bc : BlockCall)
    (fr' : Frame) (rs' : List ValueId) (bc' : BlockCall) (rtys : List Ty) : Prop :=
  ∀ vs regs, vs.map (·.ty) = rtys → fr.regs.setMany rs vs = some regs →
    ∃ regs', fr'.regs.setMany rs' vs = some regs' ∧
      ∀ fr1, enterBlock { fr with regs } bc = .ok fr1 →
        ∃ fr1', enterBlock { fr' with regs := regs' } bc' = .ok fr1' ∧ R fr1 fr1'

/-- A `call_indirect` is matched (module doc). -/
def CIOk (syms : String → Option Nat) (R : Frame → Frame → Prop) : Prop :=
  ∀ {fr fr' : Frame} {m : Mem} {st : Stmt} {rest : List Stmt} {sig : Nat} {callee : ValueId}
    {args : List ValueId} {d : Signature} {a : Nat} {vals : List Val},
    R fr fr' → m.symbols = syms → fr.body = st :: rest →
    st.inst = .callIndirect sig callee args → ciArgs fr sig callee args = .ok (d, a, vals) →
    ∃ fr2 st' rest' sig' callee' args', LStar fr' m fr2 m ∧ fr2.body = st' :: rest' ∧
      st'.inst = .callIndirect sig' callee' args' ∧
      ciArgs fr2 sig' callee' args' = .ok (d, a, vals) ∧
      Cont R { fr with body := rest } st.results { fr2 with body := rest' } st'.results
        (AbiParam.tys d.returns)

/-- A `try_call` and a `try_call_indirect` are matched (module doc). -/
structure TryOk (syms : String → Option Nat) (R : Frame → Frame → Prop) : Prop where
  call : ∀ {fr fr' : Frame} {m : Mem} {fn : FnRef} {args : List ValueId} {et : ExnTable}
    {n : Nat} {base : ValueId} {bc : BlockCall} {ext : ExtFunc} {vals : List Val},
    R fr fr' → m.symbols = syms → fr.body = [] → fr.term = .tryCall fn args et →
    tcArgs fr fn et = .ok (n, base, bc) → callArgs fr fn args = .ok (ext, vals) →
    ∃ fr2 fn' args' et' base' bc', LStar fr' m fr2 m ∧ fr2.body = [] ∧
      fr2.term = .tryCall fn' args' et' ∧ tcArgs fr2 fn' et' = .ok (n, base', bc') ∧
      callArgs fr2 fn' args' = .ok (ext, vals) ∧
      TCont R fr (tryRets n base) bc fr2 (tryRets n base') bc' (AbiParam.tys ext.sig.returns)
  ind : ∀ {fr fr' : Frame} {m : Mem} {callee : ValueId} {args : List ValueId} {et : ExnTable}
    {n : Nat} {base : ValueId} {bc : BlockCall} {d : Signature} {a : Nat} {vals : List Val},
    R fr fr' → m.symbols = syms → fr.body = [] → fr.term = .tryCallIndirect callee args et →
    ticArgs fr et = .ok (n, base, bc) → ciArgs fr et.sig callee args = .ok (d, a, vals) →
    ∃ fr2 callee' args' et' base' bc', LStar fr' m fr2 m ∧ fr2.body = [] ∧
      fr2.term = .tryCallIndirect callee' args' et' ∧ ticArgs fr2 et' = .ok (n, base', bc') ∧
      ciArgs fr2 et'.sig callee' args' = .ok (d, a, vals) ∧
      TCont R fr (tryRets n base) bc fr2 (tryRets n base') bc' (AbiParam.tys d.returns)

/-- `R` is a simulation of frames covering `call_indirect` and `try_call`/`try_call_indirect`. -/
structure IsSimX (syms : String → Option Nat) (R : Frame → Frame → Prop) : Prop where
  toIsSim : IsSim syms R
  ci : CIOk syms R
  tc : TryOk syms R

/-- `g` simulates `f`, `call_indirect` and `try_call`/`try_call_indirect` included. -/
structure FunSimX (f g : Function) : Prop where
  name : g.name = f.name
  sig : g.sig = f.sig
  slots : g.slots = f.slots
  externs : g.externs = f.externs
  sim : ∀ syms, ∃ R, IsSimX syms R ∧ ∀ b, f.entry? = some b → ∃ b', g.entry? = some b' ∧
    b'.params = b.params ∧ ∀ args regs (slots : List (SlotId × Nat)),
      args.map (·.ty) = b.params.map (·.2) →
      Regs.empty.setMany (b.params.map (·.1)) args = some regs →
      slots.map (·.1) = f.slots.map (·.1) →
      R ⟨f, regs, slots, b.body, b.term⟩ ⟨g, regs, slots, b'.body, b'.term⟩

theorem FunSimX.toFunSim {f g : Function} (h : FunSimX f g) : FunSim f g where
  name := h.name
  sig := h.sig
  slots := h.slots
  sim syms := by
    obtain ⟨R, hR, he⟩ := h.sim syms
    exact ⟨R, hR.toIsSim, he⟩

/-! ## Composition -/

theorem TCont.comp {R₁ R₂ : Frame → Frame → Prop} {a b c : Frame} {rs rs' rs'' : List ValueId}
    {bc bc' bc'' : BlockCall} {rtys : List Ty} (h1 : TCont R₁ a rs bc b rs' bc' rtys)
    (h2 : TCont R₂ b rs' bc' c rs'' bc'' rtys) :
    TCont (fun x z => ∃ y, R₁ x y ∧ R₂ y z) a rs bc c rs'' bc'' rtys := by
  intro vs regs ht hr
  obtain ⟨regs', hr', h1'⟩ := h1 vs regs ht hr
  obtain ⟨regs'', hr'', h2'⟩ := h2 vs regs' ht hr'
  refine ⟨regs'', hr'', fun fr1 he => ?_⟩
  obtain ⟨fr1', he', hR1⟩ := h1' fr1 he
  obtain ⟨fr1'', he'', hR2⟩ := h2' fr1' he'
  exact ⟨fr1'', he'', fr1', hR1, hR2⟩

theorem TCont.mono {R R' : Frame → Frame → Prop} (hR : ∀ a b, R a b → R' a b) {a b : Frame}
    {rs rs' : List ValueId} {bc bc' : BlockCall} {rtys : List Ty}
    (h : TCont R a rs bc b rs' bc' rtys) : TCont R' a rs bc b rs' bc' rtys := by
  intro vs regs ht hr
  obtain ⟨regs', h1, h2⟩ := h vs regs ht hr
  refine ⟨regs', h1, fun fr1 he => ?_⟩
  obtain ⟨fr1', he', hr'⟩ := h2 fr1 he
  exact ⟨fr1', he', hR _ _ hr'⟩

theorem IsSimX.comp {syms R₁ R₂} (h1 : IsSimX syms R₁) (h2 : IsSimX syms R₂) :
    IsSimX syms (fun x z => ∃ y, R₁ x y ∧ R₂ y z) where
  toIsSim := h1.toIsSim.comp h2.toIsSim
  ci := by
    rintro fr fr'' m st rest sig callee args d a vals ⟨fr', ha, hb⟩ hm hs hi hca
    obtain ⟨f2, st2, rest2, sig2, ce2, args2, hs1, hb2, hi2, hca2, hk1⟩ := h1.ci ha hm hs hi hca
    obtain ⟨g2, hs2, hr2⟩ := h2.toIsSim.star hb hm hs1
    obtain ⟨g3, st3, rest3, sig3, ce3, args3, hs3, hb3, hi3, hca3, hk3⟩ :=
      h2.ci hr2 hm hb2 hi2 hca2
    exact ⟨g3, st3, rest3, sig3, ce3, args3, hs2.trans hs3, hb3, hi3, hca3, hk1.comp hk3⟩
  tc := by
    refine ⟨?_, ?_⟩
    · rintro fr fr'' m fn args et n base bc ext vals ⟨fr', ha, hb⟩ hm hs ht htc hca
      obtain ⟨f2, fn2, args2, et2, base2, bc2, hs1, hb2, ht2, htc2, hca2, hk1⟩ :=
        h1.tc.call ha hm hs ht htc hca
      obtain ⟨g2, hs2, hr2⟩ := h2.toIsSim.star hb hm hs1
      obtain ⟨g3, fn3, args3, et3, base3, bc3, hs3, hb3, ht3, htc3, hca3, hk3⟩ :=
        h2.tc.call hr2 hm hb2 ht2 htc2 hca2
      exact ⟨g3, fn3, args3, et3, base3, bc3, hs2.trans hs3, hb3, ht3, htc3, hca3, hk1.comp hk3⟩
    · rintro fr fr'' m callee args et n base bc d a vals ⟨fr', ha, hb⟩ hm hs ht htc hca
      obtain ⟨f2, c2, args2, et2, base2, bc2, hs1, hb2, ht2, htc2, hca2, hk1⟩ :=
        h1.tc.ind ha hm hs ht htc hca
      obtain ⟨g2, hs2, hr2⟩ := h2.toIsSim.star hb hm hs1
      obtain ⟨g3, c3, args3, et3, base3, bc3, hs3, hb3, ht3, htc3, hca3, hk3⟩ :=
        h2.tc.ind hr2 hm hb2 ht2 htc2 hca2
      exact ⟨g3, c3, args3, et3, base3, bc3, hs2.trans hs3, hb3, ht3, htc3, hca3, hk1.comp hk3⟩

theorem IsSimX.eq (syms) : IsSimX syms (· = ·) where
  toIsSim := IsSim.eq syms
  ci := by
    rintro fr _ m st rest sig callee args d a vals rfl _ hs hi hca
    exact ⟨fr, st, rest, sig, callee, args, .refl _ _, hs, hi, hca,
      fun vs regs _ hr => ⟨regs, hr, rfl⟩⟩
  tc := by
    refine ⟨?_, ?_⟩
    · rintro fr _ m fn args et n base bc ext vals rfl _ hs ht htc hca
      exact ⟨fr, fn, args, et, base, bc, .refl _ _, hs, ht, htc, hca,
        fun vs regs _ hr => ⟨regs, hr, fun fr1 he => ⟨fr1, he, rfl⟩⟩⟩
    · rintro fr _ m callee args et n base bc d a vals rfl _ hs ht htc hca
      exact ⟨fr, callee, args, et, base, bc, .refl _ _, hs, ht, htc, hca,
        fun vs regs _ hr => ⟨regs, hr, fun fr1 he => ⟨fr1, he, rfl⟩⟩⟩

theorem FunSimX.refl (f : Function) : FunSimX f f where
  name := rfl
  sig := rfl
  slots := rfl
  externs := rfl
  sim syms := ⟨_, IsSimX.eq syms, fun b hb => ⟨b, hb, rfl, fun _ _ _ _ _ _ => rfl⟩⟩

theorem FunSimX.trans {f g h : Function} (h1 : FunSimX f g) (h2 : FunSimX g h) : FunSimX f h where
  name := h2.name.trans h1.name
  sig := h2.sig.trans h1.sig
  slots := h2.slots.trans h1.slots
  externs := h2.externs.trans h1.externs
  sim syms := by
    obtain ⟨R₁, hs1, he1⟩ := h1.sim syms
    obtain ⟨R₂, hs2, he2⟩ := h2.sim syms
    refine ⟨_, hs1.comp hs2, fun b hb => ?_⟩
    obtain ⟨b', hb', hp', hr1⟩ := he1 b hb
    obtain ⟨b'', hb'', hp'', hr2⟩ := he2 b' hb'
    refine ⟨b'', hb'', hp''.trans hp', fun args regs slots ht hr hsl => ?_⟩
    refine ⟨_, hr1 args regs slots ht hr hsl, ?_⟩
    rw [← hp'] at ht hr
    exact hr2 args regs slots ht hr (hsl.trans (by rw [h1.slots]))


/-! ## Programs -/

@[simp] theorem Frame.getMany_ne_trap (fr : Frame) (xs : List ValueId) (c : TrapCode) :
    fr.getMany xs = .trap c ↔ False := ⟨getMany_not_trap fr xs c, False.elim⟩

theorem mapM_ne_trap {α β : Type} {f : α → Res β} {c : TrapCode} (h : ∀ a, f a ≠ .trap c) :
    ∀ l : List α, l.mapM f ≠ .trap c
  | [] => by simp
  | a :: l => by
    simp only [List.mapM_cons, ne_eq, Res.bind_eq_trap, not_or, not_exists, not_and]
    refine ⟨h a, fun b _ => ⟨mapM_ne_trap h l, fun bs _ => by simp⟩⟩

theorem tryNormal_ne_trap (et : ExnTable) (base : ValueId) (c : TrapCode) :
    tryNormal et base ≠ .trap c := by
  unfold tryNormal
  simp only [ne_eq, Res.bind_eq_trap, not_or, not_exists, not_and]
  refine ⟨mapM_ne_trap (fun a => ?_) _, fun _ _ => by simp⟩
  cases a <;> simp

theorem ciArgs_ne_trap (fr : Frame) (sig : Nat) (callee : ValueId) (args : List ValueId)
    (c : TrapCode) : ciArgs fr sig callee args ≠ .trap c := by
  simp [ciArgs]

theorem tcArgs_ne_trap (fr : Frame) (fn : FnRef) (et : ExnTable) (c : TrapCode) :
    tcArgs fr fn et ≠ .trap c := by
  simp [tcArgs, tryNormal_ne_trap]

theorem ticArgs_ne_trap (fr : Frame) (et : ExnTable) (c : TrapCode) : ticArgs fr et ≠ .trap c := by
  simp [ticArgs, tryNormal_ne_trap]

theorem callArgs_ne_trap (fr : Frame) (fn : FnRef) (args : List ValueId) (c : TrapCode) :
    callArgs fr fn args ≠ .trap c := by
  simp [callArgs, checkTys]

/-- `enterBlock` reads neither the body nor the terminator of the frame. -/
theorem enterBlock_bt (fr : Frame) (b : List Stmt) (t : Terminator) (bc : BlockCall) :
    enterBlock { fr with body := b, term := t } bc = enterBlock fr bc := by
  unfold enterBlock
  rw [getMany_congr (fr := fr) (fr' := { fr with body := b, term := t }) (fun _ _ => rfl)]

/-- Frames about to jump to the normal-return successor of a `try_call` whose call returned:
entering the successors gives frames related by `R`. -/
def JR (R : Frame → Frame → Prop) (a b : Frame) : Prop :=
  a.body = [] ∧ b.body = [] ∧ ∃ bc bc', a.term = .jump bc ∧ b.term = .jump bc' ∧
    ∀ a1, enterBlock a bc = .ok a1 → ∃ b1, enterBlock b bc' = .ok b1 ∧ R a1 b1

/-- The frame relation of a program pair: some simulation relates the frames, or their
normal-return successors. -/
def GRX (syms : String → Option Nat) (fr fr' : Frame) : Prop :=
  ∃ R, IsSimX syms R ∧ (R fr fr' ∨ JR R fr fr')

theorem GRX.of {syms R} (hR : IsSimX syms R) {a b : Frame} (h : R a b) : GRX syms a b :=
  ⟨R, hR, .inl h⟩

/-- A returned `try_call`'s caller frames (`jumpFrame`) are related. -/
theorem TCont.toCont {syms R} (hR : IsSimX syms R) {fr fr' : Frame} {rs rs' : List ValueId}
    {bc bc' : BlockCall} {rtys : List Ty} (h : TCont R fr rs bc fr' rs' bc' rtys) :
    Cont (GRX syms) (jumpFrame fr bc) rs (jumpFrame fr' bc') rs' rtys := by
  intro vs regs ht hs
  obtain ⟨regs', h1, h2⟩ := h vs regs ht hs
  refine ⟨regs', h1, R, hR, .inr ⟨rfl, rfl, bc, bc', rfl, rfl, fun a1 he => ?_⟩⟩
  have he' : enterBlock { fr with regs } bc = .ok a1 := by
    rw [← enterBlock_bt { fr with regs } [] (.jump bc)]; exact he
  obtain ⟨b1, hb1, hr⟩ := h2 a1 he'
  exact ⟨b1, by rw [← hb1, ← enterBlock_bt { fr' with regs := regs' } [] (.jump bc')]; rfl, hr⟩

/-- Suspended callers, related through their continuations. -/
inductive CallersRelX (syms : String → Option Nat) :
    List Ty → List (Frame × List ValueId) → List (Frame × List ValueId) → Prop
  | nil (rtys) : CallersRelX syms rtys [] []
  | cons {rtys c rs c' rs' cs cs'} : Cont (GRX syms) c rs c' rs' rtys →
      CallersRelX syms (AbiParam.tys c.func.sig.returns) cs cs' →
      CallersRelX syms rtys ((c, rs) :: cs) ((c', rs') :: cs')

theorem CallersRelX.length {syms rtys cs cs'} (h : CallersRelX syms rtys cs cs') :
    cs'.length = cs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Related machine states. -/
structure SRX (syms : String → Option Nat) (s s' : State) : Prop where
  mem : s'.mem = s.mem
  symbols : s.mem.symbols = syms
  frame : GRX syms s.frame s'.frame
  callers : CallersRelX syms (AbiParam.tys s.frame.func.sig.returns) s.callers s'.callers

/-- Related step results. -/
def StepRelX (syms : String → Option Nat) (r r' : StepResult) : Prop :=
  (∀ s1, r = .next s1 → ∃ s1', r' = .next s1' ∧ SRX syms s1 s1') ∧
    (∀ vs m, r = .done vs m → r' = .done vs m) ∧ (∀ c, r = .trapped c → r' = .trapped c)

theorem StepRelX.trapped {syms c r'} (h : r' = StepResult.trapped c) :
    StepRelX syms (.trapped c) r' :=
  ⟨(fun _ h' => by cases h'), (fun _ _ h' => by cases h'), (fun _ h' => by cases h'; exact h)⟩

theorem StepRelX.stuck {syms m r'} : StepRelX syms (.stuck m) r' :=
  ⟨(fun _ h' => by cases h'), (fun _ _ h' => by cases h'), (fun _ h' => by cases h')⟩

/-- Pointwise `FunSimX` between the functions of two programs. -/
inductive FunsSimX : List Function → List Function → Prop
  | nil : FunsSimX [] []
  | cons {f g fs gs} : FunSimX f g → FunsSimX fs gs → FunsSimX (f :: fs) (g :: gs)

theorem FunsSimX.map {fs : List Function} {T : Function → Function} (h : ∀ f, FunSimX f (T f)) :
    FunsSimX fs (fs.map T) := by
  induction fs with
  | nil => exact .nil
  | cons f fs ih => exact .cons (h f) ih

theorem FunsSimX.toFunsSim {fs gs : List Function} (h : FunsSimX fs gs) : FunsSim fs gs := by
  induction h with
  | nil => exact .nil
  | cons hf _ ih => exact .cons hf.toFunSim ih

/-- Corresponding functions are found by any predicate on their names. -/
theorem FunsSimX.findP {fs gs : List Function} (h : FunsSimX fs gs) (P : String → Bool) :
    (∀ f, fs.find? (fun x => P x.name) = some f →
      ∃ g, gs.find? (fun x => P x.name) = some g ∧ FunSimX f g) ∧
      (fs.find? (fun x => P x.name) = none → gs.find? (fun x => P x.name) = none) := by
  induction h with
  | nil => simp
  | @cons f g fs gs hfg _ ih =>
    simp only [List.find?_cons, hfg.name]
    split
    · exact ⟨fun f' hf => by cases hf; exact ⟨g, rfl, hfg⟩, fun h => (by cases h)⟩
    · exact ih

theorem FunsSimX.externNames {fs gs : List Function} (h : FunsSimX fs gs) :
    gs.flatMap (fun f => f.externs.map (·.2.name)) = fs.flatMap (fun f => f.externs.map (·.2.name)) := by
  induction h with
  | nil => rfl
  | cons hf _ ih => simp only [List.flatMap_cons, hf.externs, ih]

theorem callExternAt_congr {env : Env} {p q : Program} (h : q.externNames = p.externNames)
    (mem : Mem) (d : Signature) (a : Nat) (vals : List Val) :
    callExternAt env q mem d a vals = callExternAt env p mem d a vals := by
  unfold callExternAt; rw [h]

theorem funSimX_entry {syms f g} (h : FunSimX f g) {vals mem fr mem'}
    (he : enterFunc f vals mem = .ok (fr, mem')) :
    ∃ fr', enterFunc g vals mem = .ok (fr', mem') ∧ GRX syms fr fr' ∧
      mem'.symbols = mem.symbols := by
  obtain ⟨b, regs, hb, h1, h2, hr, hsl, hfr⟩ := enterFunc_ok he
  obtain ⟨R, hR, hent⟩ := h.sim syms
  obtain ⟨b', hb', hp, hrel⟩ := hent b hb
  have hids := enterSlots_ids f mem
  rw [hsl] at hids
  refine ⟨⟨g, regs, fr.slots, b'.body, b'.term⟩, ?_, GRX.of hR ?_, hids.2⟩
  · rw [enterFunc_of hb' (by rw [h.sig]; exact h1) (by rw [hp]; exact h2) (by rw [hp]; exact hr),
      enterSlots_congr h.name h.slots, hsl]
  · rw [hfr]; exact hrel vals regs fr.slots h2 hr hids.1

theorem returnValues_relX {syms : String → Option Nat} {s : State} {fr2 : Frame}
    {cs' : List (Frame × List ValueId)} {m : Mem} {vals : List Val} {mem0 : Mem}
    (hsig : fr2.func.sig = s.frame.func.sig) (hsl : fr2.slots = s.frame.slots)
    (hc : CallersRelX syms (AbiParam.tys s.frame.func.sig.returns) s.callers cs')
    (hsym : mem0.symbols = syms) :
    StepRelX syms (returnValues s vals mem0) (returnValues ⟨fr2, cs', m⟩ vals mem0) := by
  simp only [returnValues, hsig, hsl]
  by_cases hty : vals.map (·.ty) = AbiParam.tys s.frame.func.sig.returns
  · have hck : ∀ w, checkTys w vals (AbiParam.tys s.frame.func.sig.returns) = .ok () := by
      intro w; simp [checkTys, hty]
    simp only [hck, StepResult.ofRes_ok]
    obtain ⟨frame, callers, mem⟩ := s
    simp only at hc ⊢
    cases hc with
    | nil =>
      exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h; rfl), fun _ h => (by cases h)⟩
    | @cons _ c rs c' rs' cs cs' hk hcs =>
      simp only
      cases hsm : c.regs.setMany rs vals with
      | none => exact StepRelX.stuck
      | some regs =>
        obtain ⟨regs', hr', hg⟩ := hk vals regs hty hsm
        simp only [hr']
        refine ⟨fun s1 h => ?_, fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
        cases h
        exact ⟨_, rfl, rfl, by rw [Mem.leave_symbols, ← hsym]; rfl, hg, hcs⟩
  · have hck : ∀ w, ∃ m, checkTys w vals (AbiParam.tys s.frame.func.sig.returns) = .stuck m := by
      intro w; simp [checkTys, hty, Res.check]
    obtain ⟨m1, h1⟩ := hck s!"return values of %{s.frame.func.name}"
    rw [h1]
    exact StepRelX.stuck

theorem callCont_relX {syms : String → Option Nat} {env : Env} (hE : EnvKeepsSymbols env)
    {p q : Program} (hP : FunsSimX p.funcs q.funcs) {s : State} {fr2 : Frame}
    {cs' : List (Frame × List ValueId)} {ext : ExtFunc} {vals : List Val} {rs rs' : List ValueId}
    {rest rest' : List Stmt} (hsym : s.mem.symbols = syms)
    (hc : CallersRelX syms (AbiParam.tys s.frame.func.sig.returns) s.callers cs')
    (hk : Cont (GRX syms) { s.frame with body := rest } rs { fr2 with body := rest' } rs'
      (AbiParam.tys ext.sig.returns)) :
    StepRelX syms (callCont env p s rest rs ext vals)
      (callCont env q ⟨fr2, cs', s.mem⟩ rest' rs' ext vals) := by
  obtain ⟨hs, hn⟩ := hP.findP (· == ext.name)
  simp only [callCont, Program.func?]
  cases hpf : p.funcs.find? (·.name == ext.name) with
  | some callee =>
    obtain ⟨callee', hq, hfs⟩ := hs callee hpf
    simp only [hq, hfs.sig]
    split
    · rename_i hcond
      cases he : enterFunc callee vals s.mem with
      | trap c => exact absurd he (enterFunc_not_trap _ _ _ _)
      | stuck m => exact StepRelX.stuck
      | ok x =>
        obtain ⟨frc, mem'⟩ := x
        obtain ⟨frc', he', hg, hsy⟩ := funSimX_entry (syms := syms) hfs he
        simp only [he', StepResult.ofRes_ok]
        refine ⟨fun s1 h => ?_, fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
        cases h
        have hret : AbiParam.tys callee.sig.returns = AbiParam.tys ext.sig.returns := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond; exact hcond.2
        refine ⟨_, rfl, rfl, hsy.trans hsym, hg, ?_⟩
        obtain ⟨_, _, _, _, _, _, _, this⟩ := enterFunc_ok he
        simp only
        rw [this]
        exact .cons (by rw [hret]; exact hk) hc
    · exact StepRelX.stuck
  | none =>
    simp only [hn hpf]
    cases hx : env.extern ext.name with
    | none => exact StepRelX.stuck
    | some fx =>
      simp only
      cases hr : fx vals s.mem with
      | trapped c => exact StepRelX.trapped rfl
      | stuck m => exact StepRelX.stuck
      | outOfFuel => exact StepRelX.stuck
      | returned rvals mem' =>
        simp only
        split
        · rename_i hty
          simp only [beq_iff_eq] at hty
          simp only [continueWith]
          cases hsm : s.frame.regs.setMany rs rvals with
          | none => exact StepRelX.stuck
          | some regs =>
            obtain ⟨regs', hr', hg⟩ := hk rvals regs hty hsm
            simp only at hr'
            simp only [hr']
            refine ⟨fun s1 h => ?_, fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
            cases h
            exact ⟨_, rfl, rfl, (hE _ _ hx _ _ _ _ hr).trans hsym, hg, hc⟩
        · exact StepRelX.stuck

theorem tailCont_relX {syms : String → Option Nat} {env : Env} (hE : EnvKeepsSymbols env)
    {p q : Program} (hP : FunsSimX p.funcs q.funcs) {s : State} {fr2 : Frame}
    {cs' : List (Frame × List ValueId)} {ext : ExtFunc} {vals : List Val}
    (hsym : s.mem.symbols = syms)
    (hc : CallersRelX syms (AbiParam.tys s.frame.func.sig.returns) s.callers cs')
    (hsig : fr2.func.sig = s.frame.func.sig) (hsl : fr2.slots = s.frame.slots)
    (hret : AbiParam.tys ext.sig.returns = AbiParam.tys s.frame.func.sig.returns) :
    StepRelX syms (tailCont env p s ext vals) (tailCont env q ⟨fr2, cs', s.mem⟩ ext vals) := by
  obtain ⟨hs, hn⟩ := hP.findP (· == ext.name)
  simp only [tailCont, Program.func?]
  cases hpf : p.funcs.find? (·.name == ext.name) with
  | some callee =>
    obtain ⟨callee', hq, hfs⟩ := hs callee hpf
    simp only [hq, hfs.sig, hsl]
    split
    · rename_i hcond
      cases he : enterFunc callee vals (s.mem.free (s.frame.slots.map (·.2))).leave with
      | trap c => exact absurd he (enterFunc_not_trap _ _ _ _)
      | stuck m => exact StepRelX.stuck
      | ok x =>
        obtain ⟨frc, mem'⟩ := x
        obtain ⟨frc', he', hg, hsy⟩ := funSimX_entry (syms := syms) hfs he
        simp only [he', StepResult.ofRes_ok]
        refine ⟨fun s1 h => ?_, fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
        cases h
        have hr2 : AbiParam.tys callee.sig.returns = AbiParam.tys ext.sig.returns := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond; exact hcond.2
        refine ⟨_, rfl, rfl, hsy.trans (by rw [Mem.leave_symbols]; exact hsym), hg, ?_⟩
        obtain ⟨_, _, _, _, _, _, _, this⟩ := enterFunc_ok he
        simp only
        rw [this]
        simp only
        rw [hr2, hret]
        exact hc
    · exact StepRelX.stuck
  | none =>
    simp only [hn hpf]
    cases hx : env.extern ext.name with
    | none => exact StepRelX.stuck
    | some fx =>
      simp only
      cases hr : fx vals s.mem with
      | trapped c => exact StepRelX.trapped rfl
      | stuck m => exact StepRelX.stuck
      | outOfFuel => exact StepRelX.stuck
      | returned rvals mem' =>
        exact returnValues_relX hsig hsl hc ((hE _ _ hx _ _ _ _ hr).trans hsym)

/-- An extern called indirectly (`callExternAt`) keeps the symbols. -/
theorem callExternAt_symbols {env : Env} (hE : EnvKeepsSymbols env) {p : Program} {mem : Mem}
    {d : Signature} {a : Nat} {vals rvals : List Val} {mem' : Mem}
    (h : callExternAt env p mem d a vals = .ok (rvals, mem')) : mem'.symbols = mem.symbols := by
  unfold callExternAt at h
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.check_eq_ok] at h
  obtain ⟨name, -, g, hg, u, -, u2, -, h⟩ := h
  split at h
  · rename_i rv m hgr
    split at h
    · simp only [Res.pure_eq_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hE _ _ hg _ _ _ _ hgr
    · cases h
  all_goals cases h

theorem callExternAt_tys {env : Env} {p : Program} {mem : Mem}
    {d : Signature} {a : Nat} {vals rvals : List Val} {mem' : Mem}
    (h : callExternAt env p mem d a vals = .ok (rvals, mem')) :
    rvals.map (·.ty) = AbiParam.tys d.returns := by
  unfold callExternAt at h
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.check_eq_ok] at h
  obtain ⟨name, -, g, hg, u, -, u2, -, h⟩ := h
  split at h
  · split at h
    · rename_i hty
      simp only [Res.pure_eq_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simpa using hty
    · cases h
  all_goals cases h

theorem ciCont_relX {syms : String → Option Nat} {env : Env} (hE : EnvKeepsSymbols env)
    {p q : Program} (hP : FunsSimX p.funcs q.funcs) {s : State} {fr2 : Frame}
    {cs' : List (Frame × List ValueId)} {sig sig' : Nat} {d : Signature} {a : Nat}
    {vals : List Val} {rs rs' : List ValueId} {rest rest' : List Stmt}
    (hsym : s.mem.symbols = syms)
    (hc : CallersRelX syms (AbiParam.tys s.frame.func.sig.returns) s.callers cs')
    (hk : Cont (GRX syms) { s.frame with body := rest } rs { fr2 with body := rest' } rs'
      (AbiParam.tys d.returns)) :
    StepRelX syms (ciCont env p s rest rs sig d a vals)
      (ciCont env q ⟨fr2, cs', s.mem⟩ rest' rs' sig' d a vals) := by
  obtain ⟨hs, hn⟩ := hP.findP (fun n => s.mem.symbols n == some a)
  simp only [ciCont]
  cases hpf : p.funcs.find? (fun f => s.mem.symbols f.name == some a) with
  | some target =>
    obtain ⟨target', hq, hfs⟩ := hs target hpf
    simp only [hq, hfs.sig]
    split
    · rename_i hcond
      cases he : enterFunc target vals s.mem with
      | trap c => exact absurd he (enterFunc_not_trap _ _ _ _)
      | stuck m => exact StepRelX.stuck
      | ok x =>
        obtain ⟨frc, mem'⟩ := x
        obtain ⟨frc', he', hg, hsy⟩ := funSimX_entry (syms := syms) hfs he
        simp only [he', StepResult.ofRes_ok]
        refine ⟨fun s1 h => ?_, fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
        cases h
        have hret : AbiParam.tys d.returns = AbiParam.tys target.sig.returns :=
          (Signature.abiMatch_eq_true.1 hcond).2.2
        refine ⟨_, rfl, rfl, hsy.trans hsym, hg, ?_⟩
        obtain ⟨_, _, _, _, _, _, _, this⟩ := enterFunc_ok he
        simp only
        rw [this]
        exact .cons (by rw [← hret]; exact hk) hc
    · exact StepRelX.stuck
  | none =>
    simp only [hn hpf, callExternAt_congr (env := env) (FunsSimX.externNames hP)]
    cases hx : callExternAt env p s.mem d a vals with
    | trap c => exact StepRelX.trapped rfl
    | stuck m => exact StepRelX.stuck
    | ok x =>
      obtain ⟨rvals, mem'⟩ := x
      simp only [StepResult.ofRes_ok, continueWith]
      cases hsm : s.frame.regs.setMany rs rvals with
      | none => exact StepRelX.stuck
      | some regs =>
        obtain ⟨regs', hr', hg⟩ := hk rvals regs (callExternAt_tys hx) hsm
        simp only at hr'
        simp only [hr']
        refine ⟨fun s1 h => ?_, fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
        cases h
        exact ⟨_, rfl, rfl, (callExternAt_symbols hE hx).trans hsym, hg, hc⟩


/-! ## Runs -/

/-- Target steps that keep the callers (stuttering). -/
inductive Stut (env : Env) (p : Program) : State → State → Prop
  | refl (s : State) : Stut env p s s
  | step {s s1 s2 : State} : step env p s = .next s1 → s1.callers = s.callers → Stut env p s1 s2 →
      Stut env p s s2

/-- Reachability by `next` steps (`E2E.Reaches`). -/
inductive Reach (env : Env) (p : Program) : State → State → Prop
  | refl (s : State) : Reach env p s s
  | next {s s' s'' : State} : step env p s = .next s' → Reach env p s' s'' → Reach env p s s''

theorem Reach.inv {env : Env} {p : Program} {s u : State} (h : Reach env p s u) :
    u = s ∨ ∃ s1, step env p s = .next s1 ∧ Reach env p s1 u := by
  cases h with
  | refl => exact .inl rfl
  | next h1 h2 => exact .inr ⟨_, h1, h2⟩

theorem LStar.stut {env : Env} {p : Program} {fr : Frame} {m : Mem} {fr2 : Frame} {m2 : Mem}
    (h : LStar fr m fr2 m2) (cs : List (Frame × List ValueId)) :
    Stut env p ⟨fr, cs, m⟩ ⟨fr2, cs, m2⟩ := by
  induction h with
  | refl => exact .refl _
  | @step fr0 m0 fr1 m1 fr3 m3 h1 _ ih =>
    refine Stut.step (s1 := ⟨fr1, cs, m1⟩) ?_ rfl ih
    rw [step_eq_lift_of (s := ⟨fr0, cs, m0⟩) h1 (fun _ h => by cases h)]
    rfl

theorem Stut.callers {env : Env} {p : Program} {s s2 : State} (h : Stut env p s s2) :
    s2.callers = s.callers := by
  induction h with
  | refl => rfl
  | step _ hc _ ih => rw [ih, hc]

theorem Stut.runLoop {env : Env} {p : Program} {s s2 : State} (h : Stut env p s s2) :
    ∃ k, ∀ n, Clif.runLoop env p (n + k) s = Clif.runLoop env p n s2 := by
  induction h with
  | refl => exact ⟨0, fun _ => rfl⟩
  | step h1 _ _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, fun n => ?_⟩
    rw [← Nat.add_assoc, runLoop_succ, h1]
    exact hk n

theorem Stut.reach {env : Env} {p : Program} {s s2 : State} (h : Stut env p s s2) {u : State}
    (hu : Reach env p s u) : u.callers = s.callers ∨ Reach env p s2 u := by
  induction h with
  | refl => exact .inr hu
  | step h1 hc _ ih =>
    rcases hu.inv with rfl | ⟨s1', h1', hr⟩
    · exact .inl rfl
    · rw [h1] at h1'; cases h1'
      rcases ih hr with h | h
      · exact .inl (h.trans hc)
      · exact .inr h

/-- One source step whose head is not a `call_indirect` nor a `try_call`. -/
theorem sim_step_lstep {syms : String → Option Nat} {env : Env} (hE : EnvKeepsSymbols env)
    {p q : Program} (hP : FunsSimX p.funcs q.funcs) {R : Frame → Frame → Prop}
    (hR : IsSimX syms R) {s : State} {fr' : Frame} {cs' : List (Frame × List ValueId)}
    (hr : R s.frame fr') (hsym : s.mem.symbols = syms)
    (hc : CallersRelX syms (AbiParam.tys s.frame.func.sig.returns) s.callers cs')
    (hci : HeadNoCI s.frame) :
    (∃ s1 s1', step env p s = .next s1 ∧ Stut env q ⟨fr', cs', s.mem⟩ s1' ∧ SRX syms s1 s1') ∨
    (∃ s2, Stut env q ⟨fr', cs', s.mem⟩ s2 ∧ StepRelX syms (step env p s) (step env q s2)) := by
  have hS := hR.toIsSim
  rw [step_eq_lift env p s hci]
  cases hl : lstep s.frame s.mem with
  | next fr1 m1 =>
    left
    obtain ⟨fr1', hst, hr1⟩ := hS.next hr hsym hl
    have hf := lstep_next_frame hl
    refine ⟨_, ⟨fr1', cs', m1⟩, rfl, hst.stut cs', rfl, hf.2.2.trans hsym, GRX.of hR hr1, ?_⟩
    simp only [hf.1]; exact hc
  | call ext vals rs rest =>
    right
    obtain ⟨fr2, rs', rest', hst, hl2, hk⟩ := hS.call hr hsym hl
    refine ⟨⟨fr2, cs', s.mem⟩, hst.stut cs', ?_⟩
    rw [step_eq_lift_of (s := ⟨fr2, cs', s.mem⟩) hl2 (fun _ h => by cases h)]
    simp only [LRes.lift]
    exact callCont_relX hE hP hsym hc (hk.mono fun a b h => GRX.of hR h)
  | ret vals =>
    right
    obtain ⟨fr2, hst, hl2⟩ := hS.ret hr hsym hl
    refine ⟨⟨fr2, cs', s.mem⟩, hst.stut cs', ?_⟩
    rw [step_eq_lift_of (s := ⟨fr2, cs', s.mem⟩) hl2 (fun _ h => by cases h)]
    simp only [LRes.lift]
    have hf := LStar.frame hst
    have hs := hS.frame hr
    exact returnValues_relX (by rw [hf.1]; exact hs.2) (by rw [hf.2.1]; exact hs.1) hc hsym
  | tail ext vals =>
    right
    obtain ⟨fr2, hst, hl2⟩ := hS.tail hr hsym hl
    refine ⟨⟨fr2, cs', s.mem⟩, hst.stut cs', ?_⟩
    rw [step_eq_lift_of (s := ⟨fr2, cs', s.mem⟩) hl2 (fun _ h => by cases h)]
    simp only [LRes.lift]
    have hf := LStar.frame hst
    have hs := hS.frame hr
    exact tailCont_relX hE hP hsym hc (by rw [hf.1]; exact hs.2) (by rw [hf.2.1]; exact hs.1)
      (lstep_tail_returns hl)
  | trap c =>
    right
    obtain ⟨fr2, m2, hst, hl2⟩ := hS.trap hr hsym hl
    refine ⟨⟨fr2, cs', m2⟩, ?_, ?_⟩
    · have := hst.stut (env := env) (p := q) cs'
      exact this
    rw [step_eq_lift_of (s := ⟨fr2, cs', m2⟩) hl2 (fun _ h => by cases h)]
    simp only [LRes.lift]
    exact StepRelX.trapped rfl
  | stuck m =>
    right
    exact ⟨_, .refl _, StepRelX.stuck⟩

theorem step_callIndirect' {env : Env} {p : Program} {s : State} {st : Stmt} {rest : List Stmt}
    {sig : Nat} {callee : ValueId} {args : List ValueId} (hb : s.frame.body = st :: rest)
    (hi : st.inst = .callIndirect sig callee args) :
    step env p s = stepCallIndirect env p s rest st.results sig callee args := by
  unfold step; rw [hb]; simp only [hi]

/-- **One source step**, any statement or terminator: a local `next` step matched by target
stuttering steps, or a step matched by target stuttering steps followed by one related step. -/
theorem sim_stepX {syms : String → Option Nat} {env : Env} (hE : EnvKeepsSymbols env)
    {p q : Program} (hP : FunsSimX p.funcs q.funcs) {s s' : State} (h : SRX syms s s') :
    (∃ s1 s1', step env p s = .next s1 ∧ Stut env q s' s1' ∧ SRX syms s1 s1') ∨
    (∃ s2, Stut env q s' s2 ∧ StepRelX syms (step env p s) (step env q s2)) := by
  obtain ⟨hm, hsym, ⟨R, hR, hfr⟩, hc⟩ := h
  obtain ⟨fr', cs', m'⟩ := s'
  simp only at hm hfr hc
  subst hm
  rcases hfr with hr | ⟨hb, hb', bc, bc', ht, ht', hj⟩
  · by_cases hci : HeadNoCI s.frame
    · exact sim_step_lstep hE hP hR hr hsym hc hci
    right
    cases hb : s.frame.body with
    | cons st rest =>
      have : ∃ sig callee args, st.inst = .callIndirect sig callee args := by
        apply Classical.byContradiction
        intro hn
        refine hci ⟨fun st' rest' hb' sig callee args hi => ?_, fun h => by rw [hb] at h; cases h⟩
        rw [hb] at hb'; cases hb'
        exact hn ⟨sig, callee, args, hi⟩
      obtain ⟨sig, callee, args, hi⟩ := this
      rw [step_callIndirect' hb hi, stepCallIndirect_eq]
      cases hca : ciArgs s.frame sig callee args with
      | trap c => exact absurd hca (ciArgs_ne_trap _ _ _ _ _)
      | stuck msg => exact ⟨_, .refl _, StepRelX.stuck⟩
      | ok x =>
        obtain ⟨d, a, vals⟩ := x
        obtain ⟨fr2, st', rest', sig', callee', args', hst, hb2, hi2, hca2, hk⟩ :=
          hR.ci hr hsym hb hi hca
        refine ⟨⟨fr2, cs', s.mem⟩, hst.stut cs', ?_⟩
        rw [step_callIndirect' (s := ⟨fr2, cs', s.mem⟩) hb2 hi2, stepCallIndirect_eq]
        simp only [hca2, StepResult.ofRes_ok]
        exact ciCont_relX hE hP hsym hc (hk.mono fun a b h => GRX.of hR h)
    | nil =>
      have hT : s.frame.term.isTry = true := by
        cases h2 : s.frame.term.isTry
        · exact absurd (show HeadNoCI s.frame from
            ⟨fun st rest h => (by rw [hb] at h; cases h), fun _ => h2⟩) hci
        · rfl
      rw [step_term env p s hb]
      cases ht : s.frame.term with
      | tryCall fn args et =>
        simp only [stepTerm]
        rw [stepTryCall_eq]
        cases htc : tcArgs s.frame fn et with
        | trap c => exact absurd htc (tcArgs_ne_trap _ _ _ _)
        | stuck msg => exact ⟨_, .refl _, StepRelX.stuck⟩
        | ok x =>
          obtain ⟨n, base, bc⟩ := x
          simp only [StepResult.ofRes_ok]
          cases hca : callArgs s.frame fn args with
          | trap c => exact absurd hca (callArgs_ne_trap _ _ _ _)
          | stuck msg => exact ⟨_, .refl _, StepRelX.stuck⟩
          | ok y =>
            obtain ⟨ext, vals⟩ := y
            obtain ⟨fr2, fn', args', et', base', bc', hst, hb2, ht2, htc2, hca2, hk⟩ :=
              hR.tc.call hr hsym hb ht htc hca
            refine ⟨⟨fr2, cs', s.mem⟩, hst.stut cs', ?_⟩
            rw [step_term env q ⟨fr2, cs', s.mem⟩ hb2]
            simp only [ht2, stepTerm]
            rw [stepTryCall_eq]
            simp only [htc2, hca2, StepResult.ofRes_ok]
            exact callCont_relX (s := { s with frame := jumpFrame s.frame bc }) hE hP hsym hc
              (hk.toCont hR)
      | tryCallIndirect callee args et =>
        simp only [stepTerm]
        rw [stepTryCallIndirect_eq]
        cases htc : ticArgs s.frame et with
        | trap c => exact absurd htc (ticArgs_ne_trap _ _ _)
        | stuck msg => exact ⟨_, .refl _, StepRelX.stuck⟩
        | ok x =>
          obtain ⟨n, base, bc⟩ := x
          simp only [StepResult.ofRes_ok]
          cases hca : ciArgs s.frame et.sig callee args with
          | trap c => exact absurd hca (ciArgs_ne_trap _ _ _ _ _)
          | stuck msg => exact ⟨_, .refl _, StepRelX.stuck⟩
          | ok y =>
            obtain ⟨d, a, vals⟩ := y
            obtain ⟨fr2, callee', args', et', base', bc', hst, hb2, ht2, htc2, hca2, hk⟩ :=
              hR.tc.ind hr hsym hb ht htc hca
            refine ⟨⟨fr2, cs', s.mem⟩, hst.stut cs', ?_⟩
            rw [step_term env q ⟨fr2, cs', s.mem⟩ hb2]
            simp only [ht2, stepTerm]
            rw [stepTryCallIndirect_eq]
            simp only [htc2, hca2, StepResult.ofRes_ok]
            exact ciCont_relX (s := { s with frame := jumpFrame s.frame bc }) hE hP hsym hc
              (hk.toCont hR)
      | _ => rw [ht] at hT; simp [Terminator.isTry] at hT
  · right
    refine ⟨⟨fr', cs', s.mem⟩, .refl _, ?_⟩
    rw [step_term env p s hb, step_term env q ⟨fr', cs', s.mem⟩ hb']
    simp only [ht, ht', stepTerm]
    cases he : enterBlock s.frame bc with
    | trap c => exact absurd he (enterBlock_not_trap _ _ _)
    | stuck m => exact StepRelX.stuck
    | ok a1 =>
      obtain ⟨b1, hb1, hr1⟩ := hj a1 he
      simp only [hb1, StepResult.ofRes_ok]
      unfold StepRelX
      refine ⟨fun s1 h => ?_, fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
      cases h
      refine ⟨_, rfl, rfl, hsym, GRX.of hR hr1, ?_⟩
      obtain ⟨_, _, _, _, _, _, _, rfl⟩ := enterBlock_ok he
      exact hc

/-- A returned or trapped outcome. -/
def Final : Outcome → Prop
  | .returned _ _ => True
  | .trapped _ => True
  | _ => False

/-- **Program refinement, `call_indirect` and `try_call`/`try_call_indirect` included.** If
every function of `p` is simulated (`FunSimX`) by the corresponding function of `q`, related
states have related runs: a source run that returns or traps within `n` steps is matched by a
target run of some length; and then every state the target run reaches has the call depth of
some state the source run reaches. -/
theorem runLoop_refinesX {syms : String → Option Nat} {env : Env} (hE : EnvKeepsSymbols env)
    {p q : Program} (hP : FunsSimX p.funcs q.funcs) :
    ∀ n (s s' : State), SRX syms s s' →
      ∃ n', OutcomeRefines (runLoop env p n s) (runLoop env q n' s') ∧
        (Final (runLoop env p n s) → ∀ u, Reach env q s' u →
          ∃ v, Reach env p s v ∧ v.callers.length = u.callers.length) := by
  intro n
  induction n with
  | zero =>
    intro s s' _
    exact ⟨0, ⟨fun _ _ h => (by cases h), fun _ h => (by cases h)⟩, fun h => by
      simp [Final] at h⟩
  | succ n ih =>
    intro s s' h
    have hlen : s'.callers.length = s.callers.length := h.callers.length
    rcases sim_stepX hE hP h with ⟨s1, s1', hst, hstut, hr⟩ | ⟨s2, hstut, hr⟩
    · obtain ⟨n1, hn1, hd1⟩ := ih s1 s1' hr
      obtain ⟨k, hk⟩ := hstut.runLoop
      refine ⟨n1 + k, ?_, fun hf u hu => ?_⟩
      · rw [hk, runLoop_succ, hst]; exact hn1
      · rw [runLoop_succ, hst] at hf
        rcases hstut.reach hu with hcu | hu1
        · exact ⟨s, .refl _, by rw [hcu, hlen]⟩
        · obtain ⟨v, hv, hl⟩ := hd1 hf u hu1
          exact ⟨v, .next hst hv, hl⟩
    · obtain ⟨hn, hd, ht⟩ := hr
      obtain ⟨k, hk⟩ := hstut.runLoop
      have hc2 := hstut.callers
      -- target states reached up to and including `s2`
      have hpre : ∀ u, Reach env q s' u → u.callers = s'.callers ∨
          ∃ s1', step env q s2 = .next s1' ∧ Reach env q s1' u := by
        intro u hu
        rcases hstut.reach hu with h1 | h1
        · exact .inl h1
        · rcases h1.inv with rfl | h2
          · exact .inl hc2
          · exact .inr h2
      rw [runLoop_succ]
      cases hs : step env p s with
      | next s1 =>
        obtain ⟨s1', hs', hr'⟩ := hn s1 hs
        obtain ⟨n1, hn1, hd1⟩ := ih _ _ hr'
        refine ⟨n1 + 1 + k, ?_, fun hf u hu => ?_⟩
        · rw [hk, runLoop_succ, hs']; exact hn1
        · rcases hpre u hu with hcu | ⟨x, hx, hxu⟩
          · exact ⟨s, .refl _, by rw [hcu, hlen]⟩
          · rw [hs'] at hx; cases hx
            obtain ⟨v, hv, hl⟩ := hd1 hf u hxu
            exact ⟨v, .next hs hv, hl⟩
      | done vs m =>
        refine ⟨0 + 1 + k, ?_, fun _ u hu => ?_⟩
        · rw [hk, runLoop_succ, hd vs m hs]
          exact ⟨fun _ _ h => h, fun _ h => (by cases h)⟩
        · rcases hpre u hu with hcu | ⟨x, hx, -⟩
          · exact ⟨s, .refl _, by rw [hcu, hlen]⟩
          · rw [hd vs m hs] at hx; cases hx
      | trapped c =>
        refine ⟨0 + 1 + k, ?_, fun _ u hu => ?_⟩
        · rw [hk, runLoop_succ, ht c hs]
          exact ⟨fun _ _ h => (by cases h), fun _ h => h⟩
        · rcases hpre u hu with hcu | ⟨x, hx, -⟩
          · exact ⟨s, .refl _, by rw [hcu, hlen]⟩
          · rw [ht c hs] at hx; cases hx
      | stuck m =>
        exact ⟨0, ⟨fun _ _ h => (by cases h), fun _ h => (by cases h)⟩, fun h => by
          simp [Final] at h⟩

end Opt
