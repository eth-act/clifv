module

public import FV.Opt.Proof.SemSimX
public import FV.Opt.Proof.SemRaise

@[expose] public section

/-!
# Simulations with unwinding: the handler edges of `try_call` (S10f, #233)

`Opt.IsSimX` (`FV/Opt/Proof/SemSimX.lean`) relates the normal-return successors of the
`try_call`s two frames make (`TryOk`, `TCont`); the runs with unwinding (`Clif.runLoopX`) also
resume a frame at a handler of its `try_call`'s exception table when the callee unwinds
(`Clif.catchIn`). Here:

* `HCont R fr et fr' et'`: for every exception, the tables `et`/`et'` catch it alike, and the
  frames resumed at the handlers (pending jumps, the payload bound at the fresh values) enter
  `R`-related blocks (`JR R`);
* `TryOkU`: `TryOk` with `HCont` for the same target `try_call`; `IsSimU`, `FunSimU`,
  `FunsSimU`: `IsSimX`, `FunSimX`, `FunsSimX` with it (`IsSimU.toX`, `FunSimU.toX`);
* the states with unwinding (`XState`: the suspended callers' pending tables) are related by
  `SRU`: `SRX`'s frame and caller relations (`GRU`, `CallersRelU`), with each caller's pending
  table catching alike (`TabRel`);
* **`runLoopX_refinesU`**: pointwise `FunSimU` gives the refinement of the runs with unwinding:
  a source run that returns, traps or ends `unwound e m` is matched by a target run with the
  same outcome (`XOutcomeRefines`). Steps where no callee unwinds are `sim_stepX`'s
  (`sim_stepU_core`, its copy at the level of `XState`); a step whose callee unwinds is matched
  by the target's corresponding call raising the same exception with the same memory
  (`sim_raiseU`): the target catches it at a related handler or leaves related frames
  (`unwindFrom_relU`).
-/

namespace Opt

open Clif

/-! ## Handler edges -/

/-- After a `try_call`'s callee unwinds: the tables `et`/`et'` catch alike, and the frames
resumed at the handlers enter `R`-related blocks. -/
def HCont (R : Frame → Frame → Prop) (fr : Frame) (et : ExnTable) (fr' : Frame)
    (et' : ExnTable) : Prop :=
  ∀ e, (catchIn fr et e = none → catchIn fr' et' e = none) ∧
    ∀ fr1, catchIn fr et e = some (.ok fr1) →
      ∃ fr1', catchIn fr' et' e = some (.ok fr1') ∧ JR R fr1 fr1'

theorem JR.mono {R R' : Frame → Frame → Prop} (hR : ∀ a b, R a b → R' a b) {a b : Frame}
    (h : JR R a b) : JR R' a b := by
  obtain ⟨ha, hb, bc, bc', hta, htb, h⟩ := h
  refine ⟨ha, hb, bc, bc', hta, htb, fun a1 he => ?_⟩
  obtain ⟨b1, h1, h2⟩ := h a1 he
  exact ⟨b1, h1, hR _ _ h2⟩

theorem JR.comp {R₁ R₂ : Frame → Frame → Prop} {a b c : Frame} (h1 : JR R₁ a b)
    (h2 : JR R₂ b c) : JR (fun x z => ∃ y, R₁ x y ∧ R₂ y z) a c := by
  obtain ⟨ha, -, bc, bc', hta, htb, h1⟩ := h1
  obtain ⟨-, hc, bc2, bc'', htb2, htc, h2⟩ := h2
  rw [htb] at htb2
  cases htb2
  refine ⟨ha, hc, bc, bc'', hta, htc, fun a1 he => ?_⟩
  obtain ⟨b1, hb1, hr1⟩ := h1 a1 he
  obtain ⟨c1, hc1, hr2⟩ := h2 b1 hb1
  exact ⟨c1, hc1, b1, hr1, hr2⟩

theorem HCont.mono {R R' : Frame → Frame → Prop} (hR : ∀ a b, R a b → R' a b) {fr fr' : Frame}
    {et et' : ExnTable} (h : HCont R fr et fr' et') : HCont R' fr et fr' et' := by
  intro e
  refine ⟨(h e).1, fun fr1 hc => ?_⟩
  obtain ⟨fr1', hc', hj⟩ := (h e).2 fr1 hc
  exact ⟨fr1', hc', hj.mono hR⟩

theorem HCont.comp {R₁ R₂ : Frame → Frame → Prop} {a b c : Frame} {et et' et'' : ExnTable}
    (h1 : HCont R₁ a et b et') (h2 : HCont R₂ b et' c et'') :
    HCont (fun x z => ∃ y, R₁ x y ∧ R₂ y z) a et c et'' := by
  intro e
  refine ⟨fun hn => (h2 e).1 ((h1 e).1 hn), fun fr1 hc => ?_⟩
  obtain ⟨fr1', hc', hj1⟩ := (h1 e).2 fr1 hc
  obtain ⟨fr1'', hc'', hj2⟩ := (h2 e).2 fr1' hc'
  exact ⟨fr1'', hc'', hj1.comp hj2⟩

theorem HCont.refl (fr : Frame) (et : ExnTable) : HCont (· = ·) fr et fr et := by
  intro e
  refine ⟨id, fun fr1 h => ⟨fr1, h, ?_⟩⟩
  obtain ⟨-, -, hb, bc, ht⟩ := catchIn_func h
  exact ⟨hb, hb, bc, bc, ht, ht, fun a1 he => ⟨a1, he, rfl⟩⟩

/-- `TryOk` with the handler edges of the same target `try_call` (module doc). -/
structure TryOkU (syms : String → Option Nat) (R : Frame → Frame → Prop) : Prop where
  call : ∀ {fr fr' : Frame} {m : Mem} {fn : FnRef} {args : List ValueId} {et : ExnTable}
    {n : Nat} {base : ValueId} {bc : BlockCall} {ext : ExtFunc} {vals : List Val},
    R fr fr' → m.symbols = syms → fr.body = [] → fr.term = .tryCall fn args et →
    tcArgs fr fn et = .ok (n, base, bc) → callArgs fr fn args = .ok (ext, vals) →
    ∃ fr2 fn' args' et' base' bc', LStar fr' m fr2 m ∧ fr2.body = [] ∧
      fr2.term = .tryCall fn' args' et' ∧ tcArgs fr2 fn' et' = .ok (n, base', bc') ∧
      callArgs fr2 fn' args' = .ok (ext, vals) ∧
      TCont R fr (tryRets n base) bc fr2 (tryRets n base') bc' (AbiParam.tys ext.sig.returns) ∧
      HCont R fr et fr2 et'
  ind : ∀ {fr fr' : Frame} {m : Mem} {callee : ValueId} {args : List ValueId} {et : ExnTable}
    {n : Nat} {base : ValueId} {bc : BlockCall} {d : Signature} {a : Nat} {vals : List Val},
    R fr fr' → m.symbols = syms → fr.body = [] → fr.term = .tryCallIndirect callee args et →
    ticArgs fr et = .ok (n, base, bc) → ciArgs fr et.sig callee args = .ok (d, a, vals) →
    ∃ fr2 callee' args' et' base' bc', LStar fr' m fr2 m ∧ fr2.body = [] ∧
      fr2.term = .tryCallIndirect callee' args' et' ∧ ticArgs fr2 et' = .ok (n, base', bc') ∧
      ciArgs fr2 et'.sig callee' args' = .ok (d, a, vals) ∧
      TCont R fr (tryRets n base) bc fr2 (tryRets n base') bc' (AbiParam.tys d.returns) ∧
      HCont R fr et fr2 et'

/-- `R` is a simulation of frames covering `call_indirect`, `try_call`/`try_call_indirect` and
their handler edges. -/
structure IsSimU (syms : String → Option Nat) (R : Frame → Frame → Prop) : Prop where
  toIsSim : IsSim syms R
  ci : CIOk syms R
  tc : TryOkU syms R

theorem IsSimU.toX {syms R} (h : IsSimU syms R) : IsSimX syms R where
  toIsSim := h.toIsSim
  ci := h.ci
  tc := by
    refine ⟨?_, ?_⟩
    · intro fr fr' m fn args et n base bc ext vals hr hm hb ht htc hca
      obtain ⟨fr2, fn', args', et', base', bc', h1, h2, h3, h4, h5, h6, -⟩ :=
        h.tc.call hr hm hb ht htc hca
      exact ⟨fr2, fn', args', et', base', bc', h1, h2, h3, h4, h5, h6⟩
    · intro fr fr' m callee args et n base bc d a vals hr hm hb ht htc hca
      obtain ⟨fr2, c', args', et', base', bc', h1, h2, h3, h4, h5, h6, -⟩ :=
        h.tc.ind hr hm hb ht htc hca
      exact ⟨fr2, c', args', et', base', bc', h1, h2, h3, h4, h5, h6⟩

theorem IsSimU.comp {syms R₁ R₂} (h1 : IsSimU syms R₁) (h2 : IsSimU syms R₂) :
    IsSimU syms (fun x z => ∃ y, R₁ x y ∧ R₂ y z) where
  toIsSim := h1.toIsSim.comp h2.toIsSim
  ci := (h1.toX.comp h2.toX).ci
  tc := by
    refine ⟨?_, ?_⟩
    · rintro fr fr'' m fn args et n base bc ext vals ⟨fr', ha, hb⟩ hm hs ht htc hca
      obtain ⟨f2, fn2, args2, et2, base2, bc2, hs1, hb2, ht2, htc2, hca2, hk1, hh1⟩ :=
        h1.tc.call ha hm hs ht htc hca
      obtain ⟨g2, hs2, hr2⟩ := h2.toIsSim.star hb hm hs1
      obtain ⟨g3, fn3, args3, et3, base3, bc3, hs3, hb3, ht3, htc3, hca3, hk3, hh3⟩ :=
        h2.tc.call hr2 hm hb2 ht2 htc2 hca2
      exact ⟨g3, fn3, args3, et3, base3, bc3, hs2.trans hs3, hb3, ht3, htc3, hca3, hk1.comp hk3,
        hh1.comp hh3⟩
    · rintro fr fr'' m callee args et n base bc d a vals ⟨fr', ha, hb⟩ hm hs ht htc hca
      obtain ⟨f2, c2, args2, et2, base2, bc2, hs1, hb2, ht2, htc2, hca2, hk1, hh1⟩ :=
        h1.tc.ind ha hm hs ht htc hca
      obtain ⟨g2, hs2, hr2⟩ := h2.toIsSim.star hb hm hs1
      obtain ⟨g3, c3, args3, et3, base3, bc3, hs3, hb3, ht3, htc3, hca3, hk3, hh3⟩ :=
        h2.tc.ind hr2 hm hb2 ht2 htc2 hca2
      exact ⟨g3, c3, args3, et3, base3, bc3, hs2.trans hs3, hb3, ht3, htc3, hca3, hk1.comp hk3,
        hh1.comp hh3⟩

theorem IsSimU.eq (syms) : IsSimU syms (· = ·) where
  toIsSim := IsSim.eq syms
  ci := (IsSimX.eq syms).ci
  tc := by
    refine ⟨?_, ?_⟩
    · rintro fr _ m fn args et n base bc ext vals rfl _ hs ht htc hca
      exact ⟨fr, fn, args, et, base, bc, .refl _ _, hs, ht, htc, hca,
        fun vs regs _ hr => ⟨regs, hr, fun fr1 he => ⟨fr1, he, rfl⟩⟩, HCont.refl fr et⟩
    · rintro fr _ m callee args et n base bc d a vals rfl _ hs ht htc hca
      exact ⟨fr, callee, args, et, base, bc, .refl _ _, hs, ht, htc, hca,
        fun vs regs _ hr => ⟨regs, hr, fun fr1 he => ⟨fr1, he, rfl⟩⟩, HCont.refl fr et⟩

/-- `g` simulates `f`, the handler edges included. -/
structure FunSimU (f g : Function) : Prop where
  name : g.name = f.name
  sig : g.sig = f.sig
  slots : g.slots = f.slots
  externs : g.externs = f.externs
  sim : ∀ syms, ∃ R, IsSimU syms R ∧ ∀ b, f.entry? = some b → ∃ b', g.entry? = some b' ∧
    b'.params = b.params ∧ ∀ args regs (slots : List (SlotId × Nat)),
      args.map (·.ty) = b.params.map (·.2) →
      Regs.empty.setMany (b.params.map (·.1)) args = some regs →
      slots.map (·.1) = f.slots.map (·.1) →
      R ⟨f, regs, slots, b.body, b.term⟩ ⟨g, regs, slots, b'.body, b'.term⟩

theorem FunSimU.toX {f g : Function} (h : FunSimU f g) : FunSimX f g where
  name := h.name
  sig := h.sig
  slots := h.slots
  externs := h.externs
  sim syms := by
    obtain ⟨R, hR, he⟩ := h.sim syms
    exact ⟨R, hR.toX, he⟩

theorem FunSimU.refl (f : Function) : FunSimU f f where
  name := rfl
  sig := rfl
  slots := rfl
  externs := rfl
  sim syms := ⟨_, IsSimU.eq syms, fun b hb => ⟨b, hb, rfl, fun _ _ _ _ _ _ => rfl⟩⟩

theorem FunSimU.trans {f g h : Function} (h1 : FunSimU f g) (h2 : FunSimU g h) : FunSimU f h where
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

/-- Pointwise `FunSimU` between the functions of two programs. -/
inductive FunsSimU : List Function → List Function → Prop
  | nil : FunsSimU [] []
  | cons {f g fs gs} : FunSimU f g → FunsSimU fs gs → FunsSimU (f :: fs) (g :: gs)

theorem FunsSimU.map {fs : List Function} {T : Function → Function} (h : ∀ f, FunSimU f (T f)) :
    FunsSimU fs (fs.map T) := by
  induction fs with
  | nil => exact .nil
  | cons f fs ih => exact .cons (h f) ih

theorem FunsSimU.toX {fs gs : List Function} (h : FunsSimU fs gs) : FunsSimX fs gs := by
  induction h with
  | nil => exact .nil
  | cons hf _ ih => exact .cons hf.toX ih

theorem FunsSimU.findP {fs gs : List Function} (h : FunsSimU fs gs) (P : String → Bool) :
    (∀ f, fs.find? (fun x => P x.name) = some f →
      ∃ g, gs.find? (fun x => P x.name) = some g ∧ FunSimU f g) ∧
      (fs.find? (fun x => P x.name) = none → gs.find? (fun x => P x.name) = none) := by
  induction h with
  | nil => simp
  | @cons f g fs gs hfg _ ih =>
    simp only [List.find?_cons, hfg.name]
    split
    · exact ⟨fun f' hf => by cases hf; exact ⟨g, rfl, hfg⟩, fun h => (by cases h)⟩
    · exact ih

/-- The frame relation with unwinding: some `IsSimU` relates the frames, or their pending
jumps. -/
def GRU (syms : String → Option Nat) (fr fr' : Frame) : Prop :=
  ∃ R, IsSimU syms R ∧ (R fr fr' ∨ JR R fr fr')

theorem GRU.of {syms R} (hR : IsSimU syms R) {a b : Frame} (h : R a b) : GRU syms a b :=
  ⟨R, hR, .inl h⟩

/-- A returned `try_call`'s caller frames (`jumpFrame`) are related. -/
theorem TCont.toContU {syms R} (hR : IsSimU syms R) {fr fr' : Frame} {rs rs' : List ValueId}
    {bc bc' : BlockCall} {rtys : List Ty} (h : TCont R fr rs bc fr' rs' bc' rtys) :
    Cont (GRU syms) (jumpFrame fr bc) rs (jumpFrame fr' bc') rs' rtys := by
  intro vs regs ht hs
  obtain ⟨regs', h1, h2⟩ := h vs regs ht hs
  refine ⟨regs', h1, R, hR, .inr ⟨rfl, rfl, bc, bc', rfl, rfl, fun a1 he => ?_⟩⟩
  have he' : enterBlock { fr with regs } bc = .ok a1 := by
    rw [← enterBlock_bt { fr with regs } [] (.jump bc)]; exact he
  obtain ⟨b1, hb1, hr⟩ := h2 a1 he'
  exact ⟨b1, by rw [← hb1, ← enterBlock_bt { fr' with regs := regs' } [] (.jump bc')]; rfl, hr⟩

/-- The pending tables `t`/`t'` of suspended callers `c`/`c'` catch alike, at related handler
frames. -/
def TabRel (syms : String → Option Nat) (c : Frame) (t : Option ExnTable) (c' : Frame)
    (t' : Option ExnTable) : Prop :=
  ∀ e, (t.bind (catchIn c · e) = none → t'.bind (catchIn c' · e) = none) ∧
    ∀ fr1, t.bind (catchIn c · e) = some (.ok fr1) →
      ∃ fr1', t'.bind (catchIn c' · e) = some (.ok fr1') ∧ GRU syms fr1 fr1'

theorem TabRel.none' (syms : String → Option Nat) (c c' : Frame) : TabRel syms c none c' none :=
  fun _ => ⟨fun _ => rfl, fun _ h => (by cases h)⟩

theorem TabRel.ofH {syms R} (hR : IsSimU syms R) {fr fr' : Frame} {et et' : ExnTable}
    (h : HCont R fr et fr' et') : TabRel syms fr (some et) fr' (some et') := by
  intro e
  simp only [Option.bind]
  refine ⟨(h e).1, fun fr1 h1 => ?_⟩
  obtain ⟨fr1', h2, hj⟩ := (h e).2 fr1 h1
  exact ⟨fr1', h2, R, hR, .inr hj⟩

theorem TabRel.bt {syms : String → Option Nat} {fr fr' : Frame} {t t' : Option ExnTable}
    (h : TabRel syms fr t fr' t') (b b' : List Stmt) (tm tm' : Terminator) :
    TabRel syms { fr with body := b, term := tm } t { fr' with body := b', term := tm' } t' := by
  intro e
  simp only [catchIn_bt]
  exact h e

/-- Suspended callers with their pending tables, related through their continuations and
handlers. -/
inductive CallersRelU (syms : String → Option Nat) :
    List Ty → List (Frame × List ValueId) → List (Option ExnTable) →
      List (Frame × List ValueId) → List (Option ExnTable) → Prop
  | nil (rtys) : CallersRelU syms rtys [] [] [] []
  | cons {rtys c rs t c' rs' t' cs ts cs' ts'} : Cont (GRU syms) c rs c' rs' rtys →
      c'.slots = c.slots → TabRel syms c t c' t' →
      CallersRelU syms (AbiParam.tys c.func.sig.returns) cs ts cs' ts' →
      CallersRelU syms rtys ((c, rs) :: cs) (t :: ts) ((c', rs') :: cs') (t' :: ts')

theorem CallersRelU.length {syms rtys cs ts cs' ts'} (h : CallersRelU syms rtys cs ts cs' ts') :
    cs'.length = cs.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ ih => simp [ih]

/-- Related states with unwinding. -/
structure SRU (syms : String → Option Nat) (xs xs' : XState) : Prop where
  mem : xs'.s.mem = xs.s.mem
  symbols : xs.s.mem.symbols = syms
  frame : GRU syms xs.s.frame xs'.s.frame
  callers : CallersRelU syms (AbiParam.tys xs.s.frame.func.sig.returns) xs.s.callers xs.tries
    xs'.s.callers xs'.tries

/-- Related step results with unwinding. -/
def XStepRelU (syms : String → Option Nat) (r r' : XStepResult) : Prop :=
  (∀ xs1, r = .next xs1 → ∃ xs1', r' = .next xs1' ∧ SRU syms xs1 xs1') ∧
    (∀ vs m, r = .done vs m → r' = .done vs m) ∧ (∀ c, r = .trapped c → r' = .trapped c) ∧
    (∀ e m, r = .unwound e m → r' = .unwound e m)

section
variable {syms : String → Option Nat} {n : Nat} {t t' : Option ExnTable}
  {ts ts' : List (Option ExnTable)}

theorem XStepRelU.stuck' {msg : String} {r' : XStepResult} :
    XStepRelU syms (liftWith n t ts (.stuck msg)) r' :=
  ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h), fun _ _ h => (by cases h)⟩

theorem XStepRelU.trapped' {c : TrapCode} :
    XStepRelU syms (liftWith n t ts (.trapped c)) (liftWith n t' ts' (.trapped c)) :=
  ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => h, fun _ _ h => (by cases h)⟩

theorem XStepRelU.done' {vs : List Val} {m : Mem} :
    XStepRelU syms (liftWith n t ts (.done vs m)) (liftWith n t' ts' (.done vs m)) :=
  ⟨fun _ h => (by cases h), fun _ _ h => h, fun _ h => (by cases h), fun _ _ h => (by cases h)⟩

theorem XStepRelU.same' {s1 s1' : State} (h1 : s1.callers.length = n)
    (h2 : s1'.callers.length = n) (h : SRU syms ⟨s1, ts⟩ ⟨s1', ts'⟩) :
    XStepRelU syms (liftWith n t ts (.next s1)) (liftWith n t' ts' (.next s1')) := by
  rw [liftWith_same h1, liftWith_same h2]
  exact ⟨fun xs1 hx => (by cases hx; exact ⟨_, rfl, h⟩), fun _ _ h => (by cases h),
    fun _ h => (by cases h), fun _ _ h => (by cases h)⟩

theorem XStepRelU.push' {s1 s1' : State} (h1 : s1.callers.length = n + 1)
    (h2 : s1'.callers.length = n + 1) (h : SRU syms ⟨s1, t :: ts⟩ ⟨s1', t' :: ts'⟩) :
    XStepRelU syms (liftWith n t ts (.next s1)) (liftWith n t' ts' (.next s1')) := by
  rw [liftWith_push h1, liftWith_push h2]
  exact ⟨fun xs1 hx => (by cases hx; exact ⟨_, rfl, h⟩), fun _ _ h => (by cases h),
    fun _ h => (by cases h), fun _ _ h => (by cases h)⟩

theorem XStepRelU.pop' {s1 s1' : State} (h1 : s1.callers.length + 1 = n)
    (h2 : s1'.callers.length + 1 = n) (h : SRU syms ⟨s1, ts.tail⟩ ⟨s1', ts'.tail⟩) :
    XStepRelU syms (liftWith n t ts (.next s1)) (liftWith n t' ts' (.next s1')) := by
  rw [liftWith_pop h1, liftWith_pop h2]
  exact ⟨fun xs1 hx => (by cases hx; exact ⟨_, rfl, h⟩), fun _ _ h => (by cases h),
    fun _ h => (by cases h), fun _ _ h => (by cases h)⟩

end

theorem funSimU_entry {syms f g} (h : FunSimU f g) {vals mem fr mem'}
    (he : enterFunc f vals mem = .ok (fr, mem')) :
    ∃ fr', enterFunc g vals mem = .ok (fr', mem') ∧ GRU syms fr fr' ∧
      mem'.symbols = mem.symbols := by
  obtain ⟨b, regs, hb, h1, h2, hr, hsl, hfr⟩ := enterFunc_ok he
  obtain ⟨R, hR, hent⟩ := h.sim syms
  obtain ⟨b', hb', hp, hrel⟩ := hent b hb
  have hids := enterSlots_ids f mem
  rw [hsl] at hids
  refine ⟨⟨g, regs, fr.slots, b'.body, b'.term⟩, ?_, GRU.of hR ?_, hids.2⟩
  · rw [enterFunc_of hb' (by rw [h.sig]; exact h1) (by rw [hp]; exact h2) (by rw [hp]; exact hr),
      enterSlots_congr h.name h.slots, hsl]
  · rw [hfr]; exact hrel vals regs fr.slots h2 hr hids.1

theorem returnValues_relU {syms : String → Option Nat} {s : State} {fr2 : Frame}
    {cs' : List (Frame × List ValueId)} {m : Mem} {vals : List Val} {mem0 : Mem}
    {t t' : Option ExnTable} {ts ts' : List (Option ExnTable)}
    (hsig : fr2.func.sig = s.frame.func.sig) (hsl : fr2.slots = s.frame.slots)
    (hc : CallersRelU syms (AbiParam.tys s.frame.func.sig.returns) s.callers ts cs' ts')
    (hsym : mem0.symbols = syms) :
    XStepRelU syms (liftWith s.callers.length t ts (returnValues s vals mem0))
      (liftWith s.callers.length t' ts' (returnValues ⟨fr2, cs', m⟩ vals mem0)) := by
  simp only [returnValues, hsig, hsl]
  by_cases hty : vals.map (·.ty) = AbiParam.tys s.frame.func.sig.returns
  · have hck : ∀ w, checkTys w vals (AbiParam.tys s.frame.func.sig.returns) = .ok () := by
      intro w; simp [checkTys, hty]
    simp only [hck, StepResult.ofRes_ok]
    obtain ⟨frame, callers, mem⟩ := s
    simp only at hc ⊢
    cases hc with
    | nil => exact XStepRelU.done'
    | @cons _ c rs t0 c' rs' t0' cs ts0 cs' ts0' hk hcsl hT hcs =>
      simp only
      cases hsm : c.regs.setMany rs vals with
      | none => exact XStepRelU.stuck'
      | some regs =>
        obtain ⟨regs', hr', hg⟩ := hk vals regs hty hsm
        simp only [hr']
        exact XStepRelU.pop' rfl (by simp [hcs.length])
          ⟨rfl, by rw [Mem.leave_symbols, ← hsym]; rfl, hg, hcs⟩
  · have hck : ∀ w, ∃ m, checkTys w vals (AbiParam.tys s.frame.func.sig.returns) = .stuck m := by
      intro w; simp [checkTys, hty, Res.check]
    obtain ⟨m1, h1⟩ := hck s!"return values of %{s.frame.func.name}"
    rw [h1]
    exact XStepRelU.stuck'

theorem callCont_relU {syms : String → Option Nat} {env : Env} (hE : EnvKeepsSymbols env)
    {p q : Program} (hP : FunsSimU p.funcs q.funcs) {s : State} {fr2 : Frame}
    {cs' : List (Frame × List ValueId)} {ext : ExtFunc} {vals : List Val} {rs rs' : List ValueId}
    {rest rest' : List Stmt} {t t' : Option ExnTable} {ts ts' : List (Option ExnTable)}
    (hsym : s.mem.symbols = syms)
    (hc : CallersRelU syms (AbiParam.tys s.frame.func.sig.returns) s.callers ts cs' ts')
    (hk : Cont (GRU syms) { s.frame with body := rest } rs { fr2 with body := rest' } rs'
      (AbiParam.tys ext.sig.returns))
    (hsl : fr2.slots = s.frame.slots)
    (hT : TabRel syms { s.frame with body := rest } t { fr2 with body := rest' } t') :
    XStepRelU syms (liftWith s.callers.length t ts (callCont env p s rest rs ext vals))
      (liftWith s.callers.length t' ts' (callCont env q ⟨fr2, cs', s.mem⟩ rest' rs' ext vals)) := by
  have hlen := hc.length
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
      | stuck m => exact XStepRelU.stuck'
      | ok x =>
        obtain ⟨frc, mem'⟩ := x
        obtain ⟨frc', he', hg, hsy⟩ := funSimU_entry (syms := syms) hfs he
        simp only [he', StepResult.ofRes_ok]
        have hret : AbiParam.tys callee.sig.returns = AbiParam.tys ext.sig.returns := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond; exact hcond.2
        obtain ⟨_, _, _, _, _, _, _, hfr⟩ := enterFunc_ok he
        refine XStepRelU.push' (by simp) (by simp [hlen]) ⟨rfl, hsy.trans hsym, hg, ?_⟩
        simp only
        rw [hfr]
        exact .cons (by rw [hret]; exact hk) hsl hT hc
    · exact XStepRelU.stuck'
  | none =>
    simp only [hn hpf]
    cases hx : env.extern ext.name with
    | none => exact XStepRelU.stuck'
    | some fx =>
      simp only
      cases hr : fx vals s.mem with
      | trapped c => exact XStepRelU.trapped'
      | stuck m => exact XStepRelU.stuck'
      | outOfFuel => exact XStepRelU.stuck'
      | returned rvals mem' =>
        simp only
        split
        · rename_i hty
          simp only [beq_iff_eq] at hty
          simp only [continueWith]
          cases hsm : s.frame.regs.setMany rs rvals with
          | none => exact XStepRelU.stuck'
          | some regs =>
            obtain ⟨regs', hr', hg⟩ := hk rvals regs hty hsm
            simp only at hr'
            simp only [hr']
            exact XStepRelU.same' rfl hlen ⟨rfl, (hE _ _ hx _ _ _ _ hr).trans hsym, hg, hc⟩
        · exact XStepRelU.stuck'

theorem tailCont_relU {syms : String → Option Nat} {env : Env} (hE : EnvKeepsSymbols env)
    {p q : Program} (hP : FunsSimU p.funcs q.funcs) {s : State} {fr2 : Frame}
    {cs' : List (Frame × List ValueId)} {ext : ExtFunc} {vals : List Val}
    {t t' : Option ExnTable} {ts ts' : List (Option ExnTable)}
    (hsym : s.mem.symbols = syms)
    (hc : CallersRelU syms (AbiParam.tys s.frame.func.sig.returns) s.callers ts cs' ts')
    (hsig : fr2.func.sig = s.frame.func.sig) (hsl : fr2.slots = s.frame.slots)
    (hret : AbiParam.tys ext.sig.returns = AbiParam.tys s.frame.func.sig.returns) :
    XStepRelU syms (liftWith s.callers.length t ts (tailCont env p s ext vals))
      (liftWith s.callers.length t' ts' (tailCont env q ⟨fr2, cs', s.mem⟩ ext vals)) := by
  have hlen := hc.length
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
      | stuck m => exact XStepRelU.stuck'
      | ok x =>
        obtain ⟨frc, mem'⟩ := x
        obtain ⟨frc', he', hg, hsy⟩ := funSimU_entry (syms := syms) hfs he
        simp only [he', StepResult.ofRes_ok]
        have hr2 : AbiParam.tys callee.sig.returns = AbiParam.tys ext.sig.returns := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond; exact hcond.2
        obtain ⟨_, _, _, _, _, _, _, hfr⟩ := enterFunc_ok he
        refine XStepRelU.same' rfl hlen
          ⟨rfl, hsy.trans (by rw [Mem.leave_symbols]; exact hsym), hg, ?_⟩
        simp only
        rw [hfr]
        simp only
        rw [hr2, hret]
        exact hc
    · exact XStepRelU.stuck'
  | none =>
    simp only [hn hpf]
    cases hx : env.extern ext.name with
    | none => exact XStepRelU.stuck'
    | some fx =>
      simp only
      cases hr : fx vals s.mem with
      | trapped c => exact XStepRelU.trapped'
      | stuck m => exact XStepRelU.stuck'
      | outOfFuel => exact XStepRelU.stuck'
      | returned rvals mem' =>
        exact returnValues_relU hsig hsl hc ((hE _ _ hx _ _ _ _ hr).trans hsym)

theorem ciCont_relU {syms : String → Option Nat} {env : Env} (hE : EnvKeepsSymbols env)
    {p q : Program} (hP : FunsSimU p.funcs q.funcs) {s : State} {fr2 : Frame}
    {cs' : List (Frame × List ValueId)} {sig sig' : Nat} {d : Signature} {a : Nat}
    {vals : List Val} {rs rs' : List ValueId} {rest rest' : List Stmt}
    {t t' : Option ExnTable} {ts ts' : List (Option ExnTable)}
    (hsym : s.mem.symbols = syms)
    (hc : CallersRelU syms (AbiParam.tys s.frame.func.sig.returns) s.callers ts cs' ts')
    (hk : Cont (GRU syms) { s.frame with body := rest } rs { fr2 with body := rest' } rs'
      (AbiParam.tys d.returns))
    (hsl : fr2.slots = s.frame.slots)
    (hT : TabRel syms { s.frame with body := rest } t { fr2 with body := rest' } t') :
    XStepRelU syms (liftWith s.callers.length t ts (ciCont env p s rest rs sig d a vals))
      (liftWith s.callers.length t' ts' (ciCont env q ⟨fr2, cs', s.mem⟩ rest' rs' sig' d a vals)) := by
  have hlen := hc.length
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
      | stuck m => exact XStepRelU.stuck'
      | ok x =>
        obtain ⟨frc, mem'⟩ := x
        obtain ⟨frc', he', hg, hsy⟩ := funSimU_entry (syms := syms) hfs he
        simp only [he', StepResult.ofRes_ok]
        have hret : AbiParam.tys d.returns = AbiParam.tys target.sig.returns :=
          (Signature.abiMatch_eq_true.1 hcond).2.2
        obtain ⟨_, _, _, _, _, _, _, hfr⟩ := enterFunc_ok he
        refine XStepRelU.push' (by simp) (by simp [hlen]) ⟨rfl, hsy.trans hsym, hg, ?_⟩
        simp only
        rw [hfr]
        exact .cons (by rw [← hret]; exact hk) hsl hT hc
    · exact XStepRelU.stuck'
  | none =>
    simp only [hn hpf, callExternAt_congr (env := env) (FunsSimX.externNames hP.toX)]
    cases hx : callExternAt env p s.mem d a vals with
    | trap c => exact XStepRelU.trapped'
    | stuck m => exact XStepRelU.stuck'
    | ok x =>
      obtain ⟨rvals, mem'⟩ := x
      simp only [StepResult.ofRes_ok, continueWith]
      cases hsm : s.frame.regs.setMany rs rvals with
      | none => exact XStepRelU.stuck'
      | some regs =>
        obtain ⟨regs', hr', hg⟩ := hk rvals regs (callExternAt_tys hx) hsm
        simp only at hr'
        simp only [hr']
        exact XStepRelU.same' rfl hlen ⟨rfl, (callExternAt_symbols hE hx).trans hsym, hg, hc⟩

/-! ## Steps where no callee unwinds -/

/-- One source step whose head is not a `call_indirect` nor a `try_call` (`sim_step_lstep`). -/
theorem sim_step_lstepU {syms : String → Option Nat} {env : Env} (hE : EnvKeepsSymbols env)
    {p q : Program} (hP : FunsSimU p.funcs q.funcs) {R : Frame → Frame → Prop}
    (hR : IsSimU syms R) {s : State} {ts : List (Option ExnTable)} {fr' : Frame}
    {cs' : List (Frame × List ValueId)} {ts' : List (Option ExnTable)}
    (hr : R s.frame fr') (hsym : s.mem.symbols = syms)
    (hc : CallersRelU syms (AbiParam.tys s.frame.func.sig.returns) s.callers ts cs' ts')
    (hci : HeadNoCI s.frame) :
    (∃ s1 s1', step env p s = .next s1 ∧ Stut env q ⟨fr', cs', s.mem⟩ s1' ∧
      s1.callers = s.callers ∧ SRU syms ⟨s1, ts⟩ ⟨s1', ts'⟩) ∨
    (∃ s2, Stut env q ⟨fr', cs', s.mem⟩ s2 ∧
      XStepRelU syms (liftWith s.callers.length (pendingOf s) ts (step env p s))
        (liftWith s.callers.length (pendingOf s2) ts' (step env q s2))) := by
  have hS := hR.toIsSim
  have hsl0 := (hS.frame hr).1
  rw [step_eq_lift env p s hci]
  cases hl : lstep s.frame s.mem with
  | next fr1 m1 =>
    left
    obtain ⟨fr1', hst, hr1⟩ := hS.next hr hsym hl
    have hf := lstep_next_frame hl
    refine ⟨_, ⟨fr1', cs', m1⟩, rfl, hst.stut cs', rfl, rfl, hf.2.2.trans hsym, GRU.of hR hr1, ?_⟩
    simp only [hf.1]; exact hc
  | call ext vals rs rest =>
    right
    obtain ⟨fr2, rs', rest', hst, hl2, hk⟩ := hS.call hr hsym hl
    obtain ⟨st, fn, args, hb, -, -, -⟩ := lstep_call_inv hl
    obtain ⟨st', fn', args', hb2, -, -, -⟩ := lstep_call_inv hl2
    refine ⟨⟨fr2, cs', s.mem⟩, hst.stut cs', ?_⟩
    rw [step_eq_lift_of (s := ⟨fr2, cs', s.mem⟩) hl2 (fun _ h => by cases h),
      pendingOf_cons (s := s) hb, pendingOf_cons (s := ⟨fr2, cs', s.mem⟩) hb2]
    simp only [LRes.lift]
    exact callCont_relU hE hP hsym hc (hk.mono fun a b h => GRU.of hR h)
      (by rw [(LStar.frame hst).2.1, hsl0]) (TabRel.none' _ _ _)
  | ret vals =>
    right
    obtain ⟨fr2, hst, hl2⟩ := hS.ret hr hsym hl
    refine ⟨⟨fr2, cs', s.mem⟩, hst.stut cs', ?_⟩
    rw [step_eq_lift_of (s := ⟨fr2, cs', s.mem⟩) hl2 (fun _ h => by cases h)]
    simp only [LRes.lift]
    have hf := LStar.frame hst
    have hs := hS.frame hr
    exact returnValues_relU (by rw [hf.1]; exact hs.2) (by rw [hf.2.1]; exact hs.1) hc hsym
  | tail ext vals =>
    right
    obtain ⟨fr2, hst, hl2⟩ := hS.tail hr hsym hl
    refine ⟨⟨fr2, cs', s.mem⟩, hst.stut cs', ?_⟩
    rw [step_eq_lift_of (s := ⟨fr2, cs', s.mem⟩) hl2 (fun _ h => by cases h)]
    simp only [LRes.lift]
    have hf := LStar.frame hst
    have hs := hS.frame hr
    exact tailCont_relU hE hP hsym hc (by rw [hf.1]; exact hs.2) (by rw [hf.2.1]; exact hs.1)
      (lstep_tail_returns hl)
  | trap c =>
    right
    obtain ⟨fr2, m2, hst, hl2⟩ := hS.trap hr hsym hl
    refine ⟨⟨fr2, cs', m2⟩, hst.stut cs', ?_⟩
    rw [step_eq_lift_of (s := ⟨fr2, cs', m2⟩) hl2 (fun _ h => by cases h)]
    simp only [LRes.lift]
    exact XStepRelU.trapped'
  | stuck m =>
    right
    exact ⟨_, .refl _, XStepRelU.stuck'⟩

/-- **One source step where no callee unwinds** (`sim_stepX` with the pending tables). -/
theorem sim_stepU_core {syms : String → Option Nat} {env : Env} (hE : EnvKeepsSymbols env)
    {p q : Program} (hP : FunsSimU p.funcs q.funcs) {R : Frame → Frame → Prop}
    (hR : IsSimU syms R) {s : State} {ts : List (Option ExnTable)} {fr' : Frame}
    {cs' : List (Frame × List ValueId)} {ts' : List (Option ExnTable)}
    (hfr : R s.frame fr' ∨ JR R s.frame fr') (hsym : s.mem.symbols = syms)
    (hc : CallersRelU syms (AbiParam.tys s.frame.func.sig.returns) s.callers ts cs' ts') :
    (∃ s1 s1', step env p s = .next s1 ∧ Stut env q ⟨fr', cs', s.mem⟩ s1' ∧
      s1.callers = s.callers ∧ SRU syms ⟨s1, ts⟩ ⟨s1', ts'⟩) ∨
    (∃ s2, Stut env q ⟨fr', cs', s.mem⟩ s2 ∧
      XStepRelU syms (liftWith s.callers.length (pendingOf s) ts (step env p s))
        (liftWith s.callers.length (pendingOf s2) ts' (step env q s2))) := by
  have hlen := hc.length
  rcases hfr with hr | ⟨hb, hb', bc, bc', ht, ht', hj⟩
  · have hsl0 := (hR.toIsSim.frame hr).1
    by_cases hci : HeadNoCI s.frame
    · exact sim_step_lstepU hE hP hR hr hsym hc hci
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
      rw [step_callIndirect' hb hi, stepCallIndirect_eq, pendingOf_cons (s := s) hb]
      cases hca : ciArgs s.frame sig callee args with
      | trap c => exact absurd hca (ciArgs_ne_trap _ _ _ _ _)
      | stuck msg => exact ⟨_, .refl _, XStepRelU.stuck'⟩
      | ok x =>
        obtain ⟨d, a, vals⟩ := x
        obtain ⟨fr2, st', rest', sig', callee', args', hst, hb2, hi2, hca2, hk⟩ :=
          hR.ci hr hsym hb hi hca
        refine ⟨⟨fr2, cs', s.mem⟩, hst.stut cs', ?_⟩
        rw [step_callIndirect' (s := ⟨fr2, cs', s.mem⟩) hb2 hi2, stepCallIndirect_eq,
          pendingOf_cons (s := ⟨fr2, cs', s.mem⟩) hb2]
        simp only [hca2, StepResult.ofRes_ok]
        exact ciCont_relU hE hP hsym hc (hk.mono fun a b h => GRU.of hR h)
          (by rw [(LStar.frame hst).2.1, hsl0]) (TabRel.none' _ _ _)
    | nil =>
      have hT : s.frame.term.isTry = true := by
        cases h2 : s.frame.term.isTry
        · exact absurd (show HeadNoCI s.frame from
            ⟨fun st rest h => (by rw [hb] at h; cases h), fun _ => h2⟩) hci
        · rfl
      rw [step_term env p s hb]
      cases ht : s.frame.term with
      | tryCall fn args et =>
        rw [pendingOf_try hb ht]
        simp only [stepTerm]
        rw [stepTryCall_eq]
        cases htc : tcArgs s.frame fn et with
        | trap c => exact absurd htc (tcArgs_ne_trap _ _ _ _)
        | stuck msg => exact ⟨_, .refl _, XStepRelU.stuck'⟩
        | ok x =>
          obtain ⟨n, base, bc⟩ := x
          simp only [StepResult.ofRes_ok]
          cases hca : callArgs s.frame fn args with
          | trap c => exact absurd hca (callArgs_ne_trap _ _ _ _)
          | stuck msg => exact ⟨_, .refl _, XStepRelU.stuck'⟩
          | ok y =>
            obtain ⟨ext, vals⟩ := y
            obtain ⟨fr2, fn', args', et', base', bc', hst, hb2, ht2, htc2, hca2, hk, hh⟩ :=
              hR.tc.call hr hsym hb ht htc hca
            refine ⟨⟨fr2, cs', s.mem⟩, hst.stut cs', ?_⟩
            rw [step_term env q ⟨fr2, cs', s.mem⟩ hb2,
              pendingOf_try (s := ⟨fr2, cs', s.mem⟩) hb2 ht2]
            simp only [ht2, stepTerm]
            rw [stepTryCall_eq]
            simp only [htc2, hca2, StepResult.ofRes_ok]
            exact callCont_relU (s := { s with frame := jumpFrame s.frame bc }) hE hP hsym hc
              (hk.toContU hR) (show fr2.slots = s.frame.slots by rw [(LStar.frame hst).2.1, hsl0])
              ((TabRel.ofH hR hh).bt [] [] (.jump bc) (.jump bc'))
      | tryCallIndirect callee args et =>
        rw [pendingOf_tryInd hb ht]
        simp only [stepTerm]
        rw [stepTryCallIndirect_eq]
        cases htc : ticArgs s.frame et with
        | trap c => exact absurd htc (ticArgs_ne_trap _ _ _)
        | stuck msg => exact ⟨_, .refl _, XStepRelU.stuck'⟩
        | ok x =>
          obtain ⟨n, base, bc⟩ := x
          simp only [StepResult.ofRes_ok]
          cases hca : ciArgs s.frame et.sig callee args with
          | trap c => exact absurd hca (ciArgs_ne_trap _ _ _ _ _)
          | stuck msg => exact ⟨_, .refl _, XStepRelU.stuck'⟩
          | ok y =>
            obtain ⟨d, a, vals⟩ := y
            obtain ⟨fr2, callee', args', et', base', bc', hst, hb2, ht2, htc2, hca2, hk, hh⟩ :=
              hR.tc.ind hr hsym hb ht htc hca
            refine ⟨⟨fr2, cs', s.mem⟩, hst.stut cs', ?_⟩
            rw [step_term env q ⟨fr2, cs', s.mem⟩ hb2,
              pendingOf_tryInd (s := ⟨fr2, cs', s.mem⟩) hb2 ht2]
            simp only [ht2, stepTerm]
            rw [stepTryCallIndirect_eq]
            simp only [htc2, hca2, StepResult.ofRes_ok]
            exact ciCont_relU (s := { s with frame := jumpFrame s.frame bc }) hE hP hsym hc
              (hk.toContU hR) (show fr2.slots = s.frame.slots by rw [(LStar.frame hst).2.1, hsl0])
              ((TabRel.ofH hR hh).bt [] [] (.jump bc) (.jump bc'))
      | _ => rw [ht] at hT; simp [Terminator.isTry] at hT
  · right
    refine ⟨⟨fr', cs', s.mem⟩, .refl _, ?_⟩
    rw [step_term env p s hb, step_term env q ⟨fr', cs', s.mem⟩ hb']
    simp only [ht, ht', stepTerm]
    cases he : enterBlock s.frame bc with
    | trap c => exact absurd he (enterBlock_not_trap _ _ _)
    | stuck m => exact XStepRelU.stuck'
    | ok a1 =>
      obtain ⟨b1, hb1, hr1⟩ := hj a1 he
      simp only [hb1, StepResult.ofRes_ok]
      obtain ⟨_, _, _, _, _, _, _, rfl⟩ := enterBlock_ok he
      exact XStepRelU.same' rfl hlen ⟨rfl, hsym, GRU.of hR hr1, hc⟩

/-! ## Raising steps -/

/-- `Clif.callIndRaise` after its prelude (`ciArgs`): the address resolves to no function of
the program and to an extern that unwinds. -/
def indRaise (env : XEnv) (p : Program) (mem : Mem) (d : Signature) (a : Nat) (vals : List Val) :
    Option (Exn × Mem) :=
  match p.funcs.find? fun f => (mem.symbols f.name) == some a with
  | some _ => none
  | none => externAtRaise env p mem d a vals

theorem callIndRaise_eq (env : XEnv) (p : Program) (mem : Mem) (fr : Frame) (sig : Nat)
    (callee : ValueId) (args : List ValueId) :
    callIndRaise env p mem fr sig callee args = match ciArgs fr sig callee args with
      | .ok (d, a, vals) => indRaise env p mem d a vals
      | _ => none := by
  unfold callIndRaise
  cases h : ciArgs fr sig callee args with
  | ok x =>
    obtain ⟨d, a, vals⟩ := x
    unfold ciArgs at h
    rw [h]
    rfl
  | trap c =>
    unfold ciArgs at h
    rw [h]
  | stuck m =>
    unfold ciArgs at h
    rw [h]

theorem callIndRaise_inv {env : XEnv} {p : Program} {mem : Mem} {fr : Frame} {sig : Nat}
    {callee : ValueId} {args : List ValueId} {r : Exn × Mem}
    (h : callIndRaise env p mem fr sig callee args = some r) :
    ∃ d a vals, ciArgs fr sig callee args = .ok (d, a, vals) ∧ indRaise env p mem d a vals = some r := by
  rw [callIndRaise_eq] at h
  split at h
  · rename_i d a vals hc
    exact ⟨d, a, vals, hc, h⟩
  · cases h

theorem tryCallRaise_eq (env : XEnv) (p : Program) (mem : Mem) (fr : Frame) (fn : FnRef)
    (args : List ValueId) (et : ExnTable) :
    tryCallRaise env p mem fr fn args et = match tcArgs fr fn et with
      | .ok _ => callRaise env p mem fr fn args
      | _ => none := by
  unfold tryCallRaise
  cases h : tcArgs fr fn et with
  | ok x =>
    unfold tcArgs at h
    rw [h]
  | trap c =>
    unfold tcArgs at h
    rw [h]
  | stuck m =>
    unfold tcArgs at h
    rw [h]

theorem tryCallIndRaise_eq (env : XEnv) (p : Program) (mem : Mem) (fr : Frame) (callee : ValueId)
    (args : List ValueId) (et : ExnTable) :
    tryCallIndRaise env p mem fr callee args et = match ticArgs fr et with
      | .ok _ => callIndRaise env p mem fr et.sig callee args
      | _ => none := by
  unfold tryCallIndRaise
  cases h : ticArgs fr et with
  | ok x =>
    unfold ticArgs at h
    rw [h]
  | trap c =>
    unfold ticArgs at h
    rw [h]
  | stuck m =>
    unfold ticArgs at h
    rw [h]

theorem extRaise_congr {p q : Program} (hP : FunsSimX p.funcs q.funcs) (env : XEnv) (mem : Mem)
    (ext : ExtFunc) (vals : List Val) :
    extRaise env q mem ext vals = extRaise env p mem ext vals := by
  obtain ⟨hs, hn⟩ := hP.findP (· == ext.name)
  unfold extRaise
  simp only [Program.func?]
  cases hpf : p.funcs.find? (·.name == ext.name) with
  | some callee =>
    obtain ⟨g, hq, -⟩ := hs callee hpf
    have hq' : q.funcs.find? (·.name == ext.name) = some g := hq
    rw [hq']
  | none =>
    have hq' : q.funcs.find? (·.name == ext.name) = none := hn hpf
    rw [hq']

theorem indRaise_congr {p q : Program} (hP : FunsSimX p.funcs q.funcs) (env : XEnv) (mem : Mem)
    (d : Signature) (a : Nat) (vals : List Val) :
    indRaise env q mem d a vals = indRaise env p mem d a vals := by
  obtain ⟨hs, hn⟩ := hP.findP (fun n => mem.symbols n == some a)
  have hx : q.externNames = p.externNames := FunsSimX.externNames hP
  have hea : externAtRaise env q mem d a vals = externAtRaise env p mem d a vals := by
    unfold externAtRaise; rw [hx]
  unfold indRaise
  rw [hea]
  cases hpf : p.funcs.find? (fun f => mem.symbols f.name == some a) with
  | some t =>
    obtain ⟨t', hq, -⟩ := hs t hpf
    have hq' : q.funcs.find? (fun f => mem.symbols f.name == some a) = some t' := hq
    rw [hq']
  | none =>
    have hq' : q.funcs.find? (fun f => mem.symbols f.name == some a) = none := hn hpf
    rw [hq']

/-- Leaving related frames: the callers' pending tables catch alike, or the run ends with the
same exception and memory. -/
theorem unwindFrom_relU {syms : String → Option Nat} (e : Exn) :
    ∀ {rtys : List Ty} {fr fr' : Frame} {cs cs' : List (Frame × List ValueId)}
      {ts ts' : List (Option ExnTable)} {m : Mem},
      fr'.slots = fr.slots → m.symbols = syms → CallersRelU syms rtys cs ts cs' ts' →
      XStepRelU syms (unwindFrom e fr cs ts m) (unwindFrom e fr' cs' ts' m) := by
  intro rtys fr fr' cs cs' ts ts' m hsl hsym hc
  induction hc generalizing fr fr' m with
  | nil =>
    simp only [unwindFrom, hsl]
    exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h), fun _ _ h => h⟩
  | @cons rtys c rs t c' rs' t' cs ts cs' ts' hk hsl' hT hcs ih =>
    simp only [unwindFrom, hsl]
    have hsym' : ((m.free (fr.slots.map (·.2))).leave).symbols = syms := by
      rw [leave_free_symbols]; exact hsym
    obtain ⟨hn, hok⟩ := hT e
    cases hcat : t.bind (catchIn c · e) with
    | none =>
      rw [hn hcat]
      exact ih hsl' hsym'
    | some r =>
      cases r with
      | ok fr1 =>
        obtain ⟨fr1', hcat', hg⟩ := hok fr1 hcat
        rw [hcat']
        simp only [XStepResult.ofRes]
        refine ⟨fun xs1 h => ?_, fun _ _ h => (by cases h), fun _ h => (by cases h),
          fun _ _ h => (by cases h)⟩
        cases h
        obtain ⟨et, -, hc1⟩ := bind_catchIn hcat
        have hf := (catchIn_func hc1).1
        refine ⟨_, rfl, rfl, hsym', hg, ?_⟩
        show CallersRelU syms (AbiParam.tys fr1.func.sig.returns) cs ts cs' ts'
        rw [hf]; exact hcs
      | trap c0 =>
        obtain ⟨et, -, hc1⟩ := bind_catchIn hcat
        exact absurd hc1 (catchIn_ne_trap _ _ _ _)
      | stuck msg =>
        simp only [XStepResult.ofRes]
        exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h),
          fun _ _ h => (by cases h)⟩

/-- Both frames raise `e` with memory `m1` at their calls: their own tables catch alike, else
both frames are left. -/
theorem raiseIn_relU {syms : String → Option Nat} {s : State} {ts : List (Option ExnTable)}
    {fr2 : Frame} {cs' : List (Frame × List ValueId)} {ts' : List (Option ExnTable)} {e : Exn}
    {m1 : Mem} (hT : TabRel syms s.frame (pendingOf s) fr2 (pendingOf ⟨fr2, cs', s.mem⟩))
    (hsl : fr2.slots = s.frame.slots) (hsym : m1.symbols = syms)
    (hc : CallersRelU syms (AbiParam.tys s.frame.func.sig.returns) s.callers ts cs' ts') :
    XStepRelU syms (raiseIn ⟨s, ts⟩ e m1) (raiseIn ⟨⟨fr2, cs', s.mem⟩, ts'⟩ e m1) := by
  unfold raiseIn
  simp only
  obtain ⟨hn, hok⟩ := hT e
  cases hcat : (pendingOf s).bind (catchIn s.frame · e) with
  | none =>
    rw [hn hcat]
    exact unwindFrom_relU e hsl hsym hc
  | some r =>
    cases r with
    | ok fr1 =>
      obtain ⟨fr1', hcat', hg⟩ := hok fr1 hcat
      rw [hcat']
      simp only [XStepResult.ofRes]
      refine ⟨fun xs1 h => ?_, fun _ _ h => (by cases h), fun _ h => (by cases h),
        fun _ _ h => (by cases h)⟩
      cases h
      obtain ⟨et, -, hc1⟩ := bind_catchIn hcat
      have hf := (catchIn_func hc1).1
      refine ⟨_, rfl, rfl, hsym, hg, ?_⟩
      show CallersRelU syms (AbiParam.tys fr1.func.sig.returns) s.callers ts cs' ts'
      rw [hf]; exact hc
    | trap c0 =>
      obtain ⟨et, -, hc1⟩ := bind_catchIn hcat
      exact absurd hc1 (catchIn_ne_trap _ _ _ _)
    | stuck msg =>
      simp only [XStepResult.ofRes]
      exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h),
        fun _ _ h => (by cases h)⟩

/-- **A source step whose callee unwinds**: the target catches up to the corresponding call,
which raises the same exception with the same memory. -/
theorem sim_raiseU {syms : String → Option Nat} {env : XEnv} (hE : EnvKeepsSymbolsX env)
    {p q : Program} (hP : FunsSimU p.funcs q.funcs) {R : Frame → Frame → Prop}
    (hR : IsSimU syms R) {s : State} {ts : List (Option ExnTable)} {fr' : Frame}
    {cs' : List (Frame × List ValueId)} {ts' : List (Option ExnTable)}
    (hr : R s.frame fr') (hsym : s.mem.symbols = syms)
    (hc : CallersRelU syms (AbiParam.tys s.frame.func.sig.returns) s.callers ts cs' ts')
    {e : Exn} {m1 : Mem} (hra : raiseAt? env p s = some (e, m1)) :
    ∃ s2, Stut env.toEnv q ⟨fr', cs', s.mem⟩ s2 ∧
      XStepRelU syms (stepX env p ⟨s, ts⟩) (stepX env q ⟨s2, ts'⟩) := by
  have hS := hR.toIsSim
  have hsl0 := (hS.frame hr).1
  have hPX := hP.toX
  have hm1 : m1.symbols = syms := (raiseAt_symbols hE hra).trans hsym
  rw [stepX_raise (xs := ⟨s, ts⟩) hra]
  have key : ∀ fr2, LStar fr' s.mem fr2 s.mem → raiseAt? env q ⟨fr2, cs', s.mem⟩ = some (e, m1) →
      TabRel syms s.frame (pendingOf s) fr2 (pendingOf ⟨fr2, cs', s.mem⟩) →
      ∃ s2, Stut env.toEnv q ⟨fr', cs', s.mem⟩ s2 ∧
        XStepRelU syms (raiseIn ⟨s, ts⟩ e m1) (stepX env q ⟨s2, ts'⟩) := by
    intro fr2 hst hra2 hT
    refine ⟨⟨fr2, cs', s.mem⟩, hst.stut cs', ?_⟩
    rw [stepX_raise (xs := ⟨⟨fr2, cs', s.mem⟩, ts'⟩) hra2]
    exact raiseIn_relU hT (by rw [(LStar.frame hst).2.1, hsl0]) hm1 hc
  have hra' := hra
  unfold raiseAt? at hra'
  cases hb : s.frame.body with
  | cons st rest =>
    rw [hb] at hra'
    simp only at hra'
    split at hra'
    · rename_i fn args hi
      obtain ⟨ext, vals, hca, hx⟩ := callRaise_inv hra'
      have hl : lstep s.frame s.mem = .call ext vals st.results rest := by
        rw [lstep_call hb hi, hca]; rfl
      obtain ⟨fr2, rs', rest', hst, hl2, -⟩ := hS.call hr hsym hl
      obtain ⟨st', fn', args', hb2, hi2, -, hca2⟩ := lstep_call_inv hl2
      refine key fr2 hst ?_ ?_
      · simp only [raiseAt?, hb2, hi2, callRaise_eq, hca2]
        exact (extRaise_congr hPX env s.mem ext vals).trans hx
      · rw [pendingOf_cons (s := s) hb, pendingOf_cons (s := ⟨fr2, cs', s.mem⟩) hb2]
        exact TabRel.none' _ _ _
    · rename_i sig callee args hi
      obtain ⟨d, a, vals, hca, hx⟩ := callIndRaise_inv hra'
      obtain ⟨fr2, st', rest', sig', callee', args', hst, hb2, hi2, hca2, -⟩ :=
        hR.ci hr hsym hb hi hca
      refine key fr2 hst ?_ ?_
      · simp only [raiseAt?, hb2, hi2, callIndRaise_eq, hca2]
        exact (indRaise_congr hPX env s.mem d a vals).trans hx
      · rw [pendingOf_cons (s := s) hb, pendingOf_cons (s := ⟨fr2, cs', s.mem⟩) hb2]
        exact TabRel.none' _ _ _
    · cases hra'
  | nil =>
    rw [hb] at hra'
    simp only at hra'
    split at hra'
    · rename_i fn args ht
      obtain ⟨ext, vals, hta, hx⟩ := returnCallRaise_inv hra'
      have hl : lstep s.frame s.mem = .tail ext vals := by
        rw [lstep_term hb, ht]; simp only [hta]; rfl
      obtain ⟨fr2, hst, hl2⟩ := hS.tail hr hsym hl
      obtain ⟨hb2, fn', args', ht2, hta2⟩ := lstep_tail_inv' hl2
      refine key fr2 hst ?_ ?_
      · simp only [raiseAt?, hb2, ht2, returnCallRaise_eq, hta2]
        exact (extRaise_congr hPX env s.mem ext vals).trans hx
      · rw [pendingOf_notTry (s := s) hb (by rw [ht]; rfl),
          pendingOf_notTry (s := ⟨fr2, cs', s.mem⟩) hb2 (by rw [ht2]; rfl)]
        exact TabRel.none' _ _ _
    · rename_i fn args et ht
      rw [tryCallRaise_eq] at hra'
      split at hra'
      · rename_i x htc
        obtain ⟨n, base, bc⟩ := x
        obtain ⟨ext, vals, hca, hx⟩ := callRaise_inv hra'
        obtain ⟨fr2, fn', args', et', base', bc', hst, hb2, ht2, htc2, hca2, -, hh⟩ :=
          hR.tc.call hr hsym hb ht htc hca
        refine key fr2 hst ?_ ?_
        · simp only [raiseAt?, hb2, ht2, tryCallRaise_eq, htc2, callRaise_eq, hca2]
          exact (extRaise_congr hPX env s.mem ext vals).trans hx
        · rw [pendingOf_try (s := s) hb ht, pendingOf_try (s := ⟨fr2, cs', s.mem⟩) hb2 ht2]
          exact TabRel.ofH hR hh
      · cases hra'
    · rename_i callee args et ht
      rw [tryCallIndRaise_eq] at hra'
      split at hra'
      · rename_i x htc
        obtain ⟨n, base, bc⟩ := x
        obtain ⟨d, a, vals, hca, hx⟩ := callIndRaise_inv hra'
        obtain ⟨fr2, callee', args', et', base', bc', hst, hb2, ht2, htc2, hca2, -, hh⟩ :=
          hR.tc.ind hr hsym hb ht htc hca
        refine key fr2 hst ?_ ?_
        · simp only [raiseAt?, hb2, ht2, tryCallIndRaise_eq, htc2, callIndRaise_eq, hca2]
          exact (indRaise_congr hPX env s.mem d a vals).trans hx
        · rw [pendingOf_tryInd (s := s) hb ht,
            pendingOf_tryInd (s := ⟨fr2, cs', s.mem⟩) hb2 ht2]
          exact TabRel.ofH hR hh
      · cases hra'
    · cases hra'

/-! ## Runs -/

theorem Stut.runLoopX {env : XEnv} {q : Program} {s s2 : State} (h : Stut env.toEnv q s s2)
    (ts : List (Option ExnTable)) :
    ∃ k, ∀ n, Clif.runLoopX env q (n + k) ⟨s, ts⟩ = Clif.runLoopX env q n ⟨s2, ts⟩ := by
  induction h with
  | refl => exact ⟨0, fun _ => rfl⟩
  | step h1 hc _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, fun n => ?_⟩
    rw [← Nat.add_assoc, runLoopX_of_next (stepX_of_same ts h1 hc)]
    exact hk n

/-- A related target step is the target's step with unwinding where the source step is not
`stuck`. -/
theorem XStepRelU.toStepX {syms : String → Option Nat} {env : XEnv} {q : Program}
    {r : XStepResult} {s2 : State} {ts' : List (Option ExnTable)} {n : Nat}
    (h : XStepRelU syms r (liftWith n (pendingOf s2) ts' (step env.toEnv q s2)))
    (hn : s2.callers.length = n) : XStepRelU syms r (stepX env q ⟨s2, ts'⟩) := by
  subst hn
  have key : ∀ r', liftWith s2.callers.length (pendingOf s2) ts' (step env.toEnv q s2) = r' →
      (∀ m, r' ≠ .stuck m) → stepX env q ⟨s2, ts'⟩ = r' := by
    intro r' h1 h2
    have hns : ∀ msg, step env.toEnv q s2 ≠ .stuck msg := by
      intro msg hm; rw [hm] at h1; exact h2 msg h1.symm
    rw [stepX_of_not_stuck (xs := ⟨s2, ts'⟩) hns, liftStep_eq]
    exact h1
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun xs1 hx => ?_, fun vs m hx => ?_, fun c hx => ?_, fun e m hx => ?_⟩
  · obtain ⟨xs1', he, hr⟩ := h1 xs1 hx
    exact ⟨xs1', key _ he (fun _ h => by cases h), hr⟩
  · exact key _ (h2 vs m hx) (fun _ h => by cases h)
  · exact key _ (h3 c hx) (fun _ h => by cases h)
  · exact key _ (h4 e m hx) (fun _ h => by cases h)

/-- **One source step with unwinding**: matched by target stuttering steps, or by target
stuttering steps followed by one related step. -/
theorem sim_stepU {syms : String → Option Nat} {env : XEnv} (hE : EnvKeepsSymbolsX env)
    {p q : Program} (hP : FunsSimU p.funcs q.funcs) {xs xs' : XState} (h : SRU syms xs xs') :
    (∃ xs1 s1', stepX env p xs = .next xs1 ∧ Stut env.toEnv q xs'.s s1' ∧
      SRU syms xs1 ⟨s1', xs'.tries⟩) ∨
    (∃ s2, Stut env.toEnv q xs'.s s2 ∧
      XStepRelU syms (stepX env p xs) (stepX env q ⟨s2, xs'.tries⟩)) := by
  obtain ⟨s, ts⟩ := xs
  obtain ⟨⟨fr', cs', m'⟩, ts'⟩ := xs'
  obtain ⟨hm, hsym, ⟨R, hR, hfr⟩, hc⟩ := h
  simp only at hm hsym hfr hc
  subst hm
  cases hra : raiseAt? env p s with
  | some em =>
    obtain ⟨e, m1⟩ := em
    right
    rcases hfr with hr | ⟨hb, -, bc, -, ht, -, -⟩
    · exact sim_raiseU hE hP hR hr hsym hc hra
    · rw [raiseAt_jump hb ht] at hra; cases hra
  | none =>
    have hstep := stepX_none (xs := ⟨s, ts⟩) hra
    rcases sim_stepU_core hE.toEnv hP hR hfr hsym hc with
      ⟨s1, s1', hs1, hstut, hcl, hrel⟩ | ⟨s2, hstut, hrel⟩
    · left
      refine ⟨⟨s1, ts⟩, s1', ?_, hstut, hrel⟩
      rw [hstep, liftStep_eq]
      simp only [hs1]
      exact liftWith_same (by rw [hcl])
    · right
      refine ⟨s2, hstut, ?_⟩
      rw [hstep, liftStep_eq]
      exact hrel.toStepX (by rw [hstut.callers]; exact hc.length)

/-- Refinement of outcomes with unwinding: a return, a trap and an exception leaving the run
are matched exactly. -/
def XOutcomeRefines (o o' : XOutcome) : Prop :=
  (∀ vals m, o = .returned vals m → o' = .returned vals m) ∧
    (∀ c, o = .trapped c → o' = .trapped c) ∧ (∀ e m, o = .unwound e m → o' = .unwound e m)

/-- **Program refinement with unwinding.** If every function of `p` is simulated with its
handler edges (`FunSimU`) by the corresponding function of `q`, related states have related
runs with unwinding: a source run that returns, traps or ends `unwound e m` within `n` steps is
matched by a target run of some length with the same outcome. -/
theorem runLoopX_refinesU {syms : String → Option Nat} {env : XEnv} (hE : EnvKeepsSymbolsX env)
    {p q : Program} (hP : FunsSimU p.funcs q.funcs) :
    ∀ n (xs xs' : XState), SRU syms xs xs' →
      ∃ n', XOutcomeRefines (Clif.runLoopX env p n xs) (Clif.runLoopX env q n' xs') := by
  intro n
  induction n with
  | zero =>
    intro xs xs' _
    exact ⟨0, fun _ _ h => (by cases h), fun _ h => (by cases h), fun _ _ h => (by cases h)⟩
  | succ n ih =>
    intro xs xs' h
    obtain ⟨s', ts'⟩ := xs'
    rcases sim_stepU hE hP h with ⟨xs1, s1', hst, hstut, hr⟩ | ⟨s2, hstut, hr⟩
    · obtain ⟨n1, hn1⟩ := ih xs1 _ hr
      obtain ⟨k, hk⟩ := hstut.runLoopX ts'
      refine ⟨n1 + k, ?_⟩
      rw [hk, runLoopX_of_next hst]
      exact hn1
    · obtain ⟨hn, hd, ht, hu⟩ := hr
      obtain ⟨k, hk⟩ := hstut.runLoopX ts'
      rw [Clif.runLoopX]
      cases hs : stepX env p xs with
      | next xs1 =>
        obtain ⟨xs1', hs', hr'⟩ := hn xs1 hs
        obtain ⟨n1, hn1⟩ := ih _ _ hr'
        refine ⟨n1 + 1 + k, ?_⟩
        rw [hk, runLoopX_of_next hs']
        exact hn1
      | done vs m =>
        refine ⟨0 + 1 + k, ?_⟩
        rw [hk, Clif.runLoopX, hd vs m hs]
        exact ⟨fun _ _ h => h, fun _ h => (by cases h), fun _ _ h => (by cases h)⟩
      | trapped c =>
        refine ⟨0 + 1 + k, ?_⟩
        rw [hk, Clif.runLoopX, ht c hs]
        exact ⟨fun _ _ h => (by cases h), fun _ h => h, fun _ _ h => (by cases h)⟩
      | unwound e m =>
        refine ⟨0 + 1 + k, ?_⟩
        rw [hk, Clif.runLoopX, hu e m hs]
        exact ⟨fun _ _ h => (by cases h), fun _ h => (by cases h), fun _ _ h => h⟩
      | stuck m =>
        exact ⟨0, fun _ _ h => (by cases h), fun _ h => (by cases h), fun _ _ h => (by cases h)⟩

end Opt
