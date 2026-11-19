import FV.Opt.Proof.SemSimU

/-!
# Memory-aware simulations (#1119)

`Opt.IsSimU` (`FV/Opt/Proof/SemSimU.lean`) relates frames by `R : Frame → Frame → Prop`, with
the memory quantified away at every step, so it cannot say "this load is redundant because the
memory holds `v`". Here the relation also takes the memory both sides run at:
`R : Frame → Frame → Mem → Prop`.

* `IsSimM`: `IsSim` with the memory: each local step of the source from memory `m` is matched by
  target steps from the same `m` landing in the source's memory; where control comes back from
  another function (a call's return: `ContM`) the relation must hold at every memory with the
  link-time symbols;
* `CIOkM`, `TContM`, `TryOkM`, `HContM`, `TryOkMU`, `IsSimMU`: `CIOk`, `TCont`, `TryOk`, `HCont`,
  `TryOkU`, `IsSimU` likewise (the handler frames of `HContM` are related at every memory with
  the symbols, since the unwinding callee may have changed it);
* `FunSimMU`, `FunsSimMU`: `FunSimU`, `FunsSimU` with an `IsSimMU`, whose entry frames are related
  at every memory with the symbols. Every `FunSimU` is one (`FunSimU.toMU`: the relation ignores
  the memory); `FunSimMU` is reflexive and transitive.

The program-level refinement is in `FV/Opt/Proof/SemSimMU.lean` (`runLoopX_refinesMU`).
-/

namespace Opt

open Clif

/-! ## Simulations with the memory -/

/-- Continuation of a call: binding the returned values (of types `rtys`) keeps `R`, at every
memory with the symbols `syms` the callee may have left. -/
def ContM (syms : String → Option Nat) (R : Frame → Frame → Mem → Prop) (fr : Frame)
    (rs : List ValueId) (fr' : Frame) (rs' : List ValueId) (rtys : List Ty) : Prop :=
  ∀ vs regs m, vs.map (·.ty) = rtys → m.symbols = syms → fr.regs.setMany rs vs = some regs →
    ∃ regs', fr'.regs.setMany rs' vs = some regs' ∧ R { fr with regs } { fr' with regs := regs' } m

/-- `R` is a (stuttering, forward) simulation of frames running at the same memory, in memories
whose symbols are `syms`. -/
structure IsSimM (syms : String → Option Nat) (R : Frame → Frame → Mem → Prop) : Prop where
  frame : ∀ {fr fr' m}, R fr fr' m → fr'.slots = fr.slots ∧ fr'.func.sig = fr.func.sig
  next : ∀ {fr fr' m fr1 m1}, R fr fr' m → m.symbols = syms → lstep fr m = .next fr1 m1 →
    ∃ fr1', LStar fr' m fr1' m1 ∧ R fr1 fr1' m1
  call : ∀ {fr fr' m ext vals rs rest}, R fr fr' m → m.symbols = syms →
    lstep fr m = .call ext vals rs rest →
    ∃ fr2 rs' rest', LStar fr' m fr2 m ∧ lstep fr2 m = .call ext vals rs' rest' ∧
      ContM syms R { fr with body := rest } rs { fr2 with body := rest' } rs'
        (AbiParam.tys ext.sig.returns)
  ret : ∀ {fr fr' m vals}, R fr fr' m → m.symbols = syms → lstep fr m = .ret vals →
    ∃ fr2, LStar fr' m fr2 m ∧ lstep fr2 m = .ret vals
  tail : ∀ {fr fr' m ext vals}, R fr fr' m → m.symbols = syms → lstep fr m = .tail ext vals →
    ∃ fr2, LStar fr' m fr2 m ∧ lstep fr2 m = .tail ext vals
  trap : ∀ {fr fr' m c}, R fr fr' m → m.symbols = syms → lstep fr m = .trap c →
    ∃ fr2 m2, LStar fr' m fr2 m2 ∧ lstep fr2 m2 = .trap c

theorem IsSimM.star {syms R} (hR : IsSimM syms R) {fr fr' m fr1 m1} (h : R fr fr' m)
    (hm : m.symbols = syms) (hs : LStar fr m fr1 m1) :
    ∃ fr1', LStar fr' m fr1' m1 ∧ R fr1 fr1' m1 := by
  induction hs generalizing fr' with
  | refl => exact ⟨fr', .refl _ _, h⟩
  | step h1 _ ih =>
    obtain ⟨fa, ha, hra⟩ := hR.next h hm h1
    obtain ⟨fb, hb, hrb⟩ := ih hra ((lstep_next_frame h1).2.2.trans hm)
    exact ⟨fb, ha.trans hb, hrb⟩

theorem ContM.comp {syms} {R₁ R₂ : Frame → Frame → Mem → Prop} {a rs b rs' c rs'' rtys}
    (h1 : ContM syms R₁ a rs b rs' rtys) (h2 : ContM syms R₂ b rs' c rs'' rtys) :
    ContM syms (fun x z m => ∃ y, R₁ x y m ∧ R₂ y z m) a rs c rs'' rtys := by
  intro vs regs m ht hm hr
  obtain ⟨regs', hr', h1'⟩ := h1 vs regs m ht hm hr
  obtain ⟨regs'', hr'', h2'⟩ := h2 vs regs' m ht hm hr'
  exact ⟨regs'', hr'', _, h1', h2'⟩

theorem ContM.mono {syms} {R R' : Frame → Frame → Mem → Prop} (hR : ∀ a b m, R a b m → R' a b m)
    {a rs b rs' rtys} (h : ContM syms R a rs b rs' rtys) : ContM syms R' a rs b rs' rtys := by
  intro vs regs m ht hm hr
  obtain ⟨regs', h1, h2⟩ := h vs regs m ht hm hr
  exact ⟨regs', h1, hR _ _ _ h2⟩

theorem IsSimM.comp {syms R₁ R₂} (h1 : IsSimM syms R₁) (h2 : IsSimM syms R₂) :
    IsSimM syms (fun x z m => ∃ y, R₁ x y m ∧ R₂ y z m) where
  frame := by
    rintro _ _ _ ⟨y, ha, hb⟩
    exact ⟨(h2.frame hb).1.trans (h1.frame ha).1, (h2.frame hb).2.trans (h1.frame ha).2⟩
  next := by
    rintro fr fr'' m fr1 m1 ⟨fr', ha, hb⟩ hm hs
    obtain ⟨fr1', hs1, hr1⟩ := h1.next ha hm hs
    obtain ⟨fr1'', hs2, hr2⟩ := h2.star hb hm hs1
    exact ⟨fr1'', hs2, fr1', hr1, hr2⟩
  call := by
    rintro fr fr'' m ext vals rs rest ⟨fr', ha, hb⟩ hm hs
    obtain ⟨f2, rs', rest', hs1, hc1, hk1⟩ := h1.call ha hm hs
    obtain ⟨g2, hs2, hr2⟩ := h2.star hb hm hs1
    obtain ⟨g3, rs'', rest'', hs3, hc3, hk3⟩ := h2.call hr2 hm hc1
    exact ⟨g3, rs'', rest'', hs2.trans hs3, hc3, hk1.comp hk3⟩
  ret := by
    rintro fr fr'' m vals ⟨fr', ha, hb⟩ hm hs
    obtain ⟨f2, hs1, hc1⟩ := h1.ret ha hm hs
    obtain ⟨g2, hs2, hr2⟩ := h2.star hb hm hs1
    obtain ⟨g3, hs3, hc3⟩ := h2.ret hr2 hm hc1
    exact ⟨g3, hs2.trans hs3, hc3⟩
  tail := by
    rintro fr fr'' m ext vals ⟨fr', ha, hb⟩ hm hs
    obtain ⟨f2, hs1, hc1⟩ := h1.tail ha hm hs
    obtain ⟨g2, hs2, hr2⟩ := h2.star hb hm hs1
    obtain ⟨g3, hs3, hc3⟩ := h2.tail hr2 hm hc1
    exact ⟨g3, hs2.trans hs3, hc3⟩
  trap := by
    rintro fr fr'' m c ⟨fr', ha, hb⟩ hm hs
    obtain ⟨f2, m2, hs1, hc1⟩ := h1.trap ha hm hs
    obtain ⟨g2, hs2, hr2⟩ := h2.star hb hm hs1
    obtain ⟨g3, m3, hs3, hc3⟩ := h2.trap hr2 ((LStar.frame hs1).2.2.trans hm) hc1
    exact ⟨g3, m3, hs2.trans hs3, hc3⟩

/-! ## `call_indirect`, `try_call` and handler edges -/

/-- A `call_indirect` is matched (`CIOk` with the memory). -/
def CIOkM (syms : String → Option Nat) (R : Frame → Frame → Mem → Prop) : Prop :=
  ∀ {fr fr' : Frame} {m : Mem} {st : Stmt} {rest : List Stmt} {sig : Nat} {callee : ValueId}
    {args : List ValueId} {d : Signature} {a : Nat} {vals : List Val},
    R fr fr' m → m.symbols = syms → fr.body = st :: rest →
    st.inst = .callIndirect sig callee args → ciArgs fr sig callee args = .ok (d, a, vals) →
    ∃ fr2 st' rest' sig' callee' args', LStar fr' m fr2 m ∧ fr2.body = st' :: rest' ∧
      st'.inst = .callIndirect sig' callee' args' ∧
      ciArgs fr2 sig' callee' args' = .ok (d, a, vals) ∧
      ContM syms R { fr with body := rest } st.results { fr2 with body := rest' } st'.results
        (AbiParam.tys d.returns)

/-- After a `try_call` returns (at any memory with the symbols `syms`): binding the results and
entering the normal-return successors gives `R`-related frames at that memory. -/
def TContM (syms : String → Option Nat) (R : Frame → Frame → Mem → Prop) (fr : Frame)
    (rs : List ValueId) (bc : BlockCall) (fr' : Frame) (rs' : List ValueId) (bc' : BlockCall)
    (rtys : List Ty) : Prop :=
  ∀ vs regs m, vs.map (·.ty) = rtys → m.symbols = syms → fr.regs.setMany rs vs = some regs →
    ∃ regs', fr'.regs.setMany rs' vs = some regs' ∧
      ∀ fr1, enterBlock { fr with regs } bc = .ok fr1 →
        ∃ fr1', enterBlock { fr' with regs := regs' } bc' = .ok fr1' ∧ R fr1 fr1' m

/-- A `try_call` and a `try_call_indirect` are matched (`TryOk` with the memory). -/
structure TryOkM (syms : String → Option Nat) (R : Frame → Frame → Mem → Prop) : Prop where
  call : ∀ {fr fr' : Frame} {m : Mem} {fn : FnRef} {args : List ValueId} {et : ExnTable}
    {n : Nat} {base : ValueId} {bc : BlockCall} {ext : ExtFunc} {vals : List Val},
    R fr fr' m → m.symbols = syms → fr.body = [] → fr.term = .tryCall fn args et →
    tcArgs fr fn et = .ok (n, base, bc) → callArgs fr fn args = .ok (ext, vals) →
    ∃ fr2 fn' args' et' base' bc', LStar fr' m fr2 m ∧ fr2.body = [] ∧
      fr2.term = .tryCall fn' args' et' ∧ tcArgs fr2 fn' et' = .ok (n, base', bc') ∧
      callArgs fr2 fn' args' = .ok (ext, vals) ∧
      TContM syms R fr (tryRets n base) bc fr2 (tryRets n base') bc' (AbiParam.tys ext.sig.returns)
  ind : ∀ {fr fr' : Frame} {m : Mem} {callee : ValueId} {args : List ValueId} {et : ExnTable}
    {n : Nat} {base : ValueId} {bc : BlockCall} {d : Signature} {a : Nat} {vals : List Val},
    R fr fr' m → m.symbols = syms → fr.body = [] → fr.term = .tryCallIndirect callee args et →
    ticArgs fr et = .ok (n, base, bc) → ciArgs fr et.sig callee args = .ok (d, a, vals) →
    ∃ fr2 callee' args' et' base' bc', LStar fr' m fr2 m ∧ fr2.body = [] ∧
      fr2.term = .tryCallIndirect callee' args' et' ∧ ticArgs fr2 et' = .ok (n, base', bc') ∧
      ciArgs fr2 et'.sig callee' args' = .ok (d, a, vals) ∧
      TContM syms R fr (tryRets n base) bc fr2 (tryRets n base') bc' (AbiParam.tys d.returns)

/-- After a `try_call`'s callee unwinds: the tables `et`/`et'` catch alike, and the frames
resumed at the handlers enter blocks related by `R` at every memory with the symbols `syms`
(the memory the unwinding left). -/
def HContM (syms : String → Option Nat) (R : Frame → Frame → Mem → Prop) (fr : Frame)
    (et : ExnTable) (fr' : Frame) (et' : ExnTable) : Prop :=
  ∀ e, (catchIn fr et e = none → catchIn fr' et' e = none) ∧
    ∀ fr1, catchIn fr et e = some (.ok fr1) →
      ∃ fr1', catchIn fr' et' e = some (.ok fr1') ∧
        JR (fun x y => ∀ m, m.symbols = syms → R x y m) fr1 fr1'

/-- `TryOkM` with the handler edges of the same target `try_call`. -/
structure TryOkMU (syms : String → Option Nat) (R : Frame → Frame → Mem → Prop) : Prop where
  call : ∀ {fr fr' : Frame} {m : Mem} {fn : FnRef} {args : List ValueId} {et : ExnTable}
    {n : Nat} {base : ValueId} {bc : BlockCall} {ext : ExtFunc} {vals : List Val},
    R fr fr' m → m.symbols = syms → fr.body = [] → fr.term = .tryCall fn args et →
    tcArgs fr fn et = .ok (n, base, bc) → callArgs fr fn args = .ok (ext, vals) →
    ∃ fr2 fn' args' et' base' bc', LStar fr' m fr2 m ∧ fr2.body = [] ∧
      fr2.term = .tryCall fn' args' et' ∧ tcArgs fr2 fn' et' = .ok (n, base', bc') ∧
      callArgs fr2 fn' args' = .ok (ext, vals) ∧
      TContM syms R fr (tryRets n base) bc fr2 (tryRets n base') bc'
        (AbiParam.tys ext.sig.returns) ∧
      HContM syms R fr et fr2 et'
  ind : ∀ {fr fr' : Frame} {m : Mem} {callee : ValueId} {args : List ValueId} {et : ExnTable}
    {n : Nat} {base : ValueId} {bc : BlockCall} {d : Signature} {a : Nat} {vals : List Val},
    R fr fr' m → m.symbols = syms → fr.body = [] → fr.term = .tryCallIndirect callee args et →
    ticArgs fr et = .ok (n, base, bc) → ciArgs fr et.sig callee args = .ok (d, a, vals) →
    ∃ fr2 callee' args' et' base' bc', LStar fr' m fr2 m ∧ fr2.body = [] ∧
      fr2.term = .tryCallIndirect callee' args' et' ∧ ticArgs fr2 et' = .ok (n, base', bc') ∧
      ciArgs fr2 et'.sig callee' args' = .ok (d, a, vals) ∧
      TContM syms R fr (tryRets n base) bc fr2 (tryRets n base') bc' (AbiParam.tys d.returns) ∧
      HContM syms R fr et fr2 et'

theorem TryOkMU.toTryOkM {syms R} (h : TryOkMU syms R) : TryOkM syms R where
  call := by
    intro fr fr' m fn args et n base bc ext vals hr hm hb ht htc hca
    obtain ⟨fr2, fn', args', et', base', bc', h1, h2, h3, h4, h5, h6, -⟩ :=
      h.call hr hm hb ht htc hca
    exact ⟨fr2, fn', args', et', base', bc', h1, h2, h3, h4, h5, h6⟩
  ind := by
    intro fr fr' m callee args et n base bc d a vals hr hm hb ht htc hca
    obtain ⟨fr2, c', args', et', base', bc', h1, h2, h3, h4, h5, h6, -⟩ :=
      h.ind hr hm hb ht htc hca
    exact ⟨fr2, c', args', et', base', bc', h1, h2, h3, h4, h5, h6⟩

/-- `R` is a memory-aware simulation of frames covering `call_indirect`,
`try_call`/`try_call_indirect` and their handler edges. -/
structure IsSimMU (syms : String → Option Nat) (R : Frame → Frame → Mem → Prop) : Prop where
  toIsSimM : IsSimM syms R
  ci : CIOkM syms R
  tc : TryOkMU syms R

/-! ## Composition -/

theorem TContM.comp {syms} {R₁ R₂ : Frame → Frame → Mem → Prop} {a b c : Frame}
    {rs rs' rs'' : List ValueId} {bc bc' bc'' : BlockCall} {rtys : List Ty}
    (h1 : TContM syms R₁ a rs bc b rs' bc' rtys) (h2 : TContM syms R₂ b rs' bc' c rs'' bc'' rtys) :
    TContM syms (fun x z m => ∃ y, R₁ x y m ∧ R₂ y z m) a rs bc c rs'' bc'' rtys := by
  intro vs regs m ht hm hr
  obtain ⟨regs', hr', h1'⟩ := h1 vs regs m ht hm hr
  obtain ⟨regs'', hr'', h2'⟩ := h2 vs regs' m ht hm hr'
  refine ⟨regs'', hr'', fun fr1 he => ?_⟩
  obtain ⟨fr1', he', hR1⟩ := h1' fr1 he
  obtain ⟨fr1'', he'', hR2⟩ := h2' fr1' he'
  exact ⟨fr1'', he'', fr1', hR1, hR2⟩

theorem TContM.mono {syms} {R R' : Frame → Frame → Mem → Prop} (hR : ∀ a b m, R a b m → R' a b m)
    {a b : Frame} {rs rs' : List ValueId} {bc bc' : BlockCall} {rtys : List Ty}
    (h : TContM syms R a rs bc b rs' bc' rtys) : TContM syms R' a rs bc b rs' bc' rtys := by
  intro vs regs m ht hm hr
  obtain ⟨regs', h1, h2⟩ := h vs regs m ht hm hr
  refine ⟨regs', h1, fun fr1 he => ?_⟩
  obtain ⟨fr1', he', hr'⟩ := h2 fr1 he
  exact ⟨fr1', he', hR _ _ _ hr'⟩

theorem HContM.comp {syms} {R₁ R₂ : Frame → Frame → Mem → Prop} {a b c : Frame}
    {et et' et'' : ExnTable} (h1 : HContM syms R₁ a et b et') (h2 : HContM syms R₂ b et' c et'') :
    HContM syms (fun x z m => ∃ y, R₁ x y m ∧ R₂ y z m) a et c et'' := by
  intro e
  refine ⟨fun hn => (h2 e).1 ((h1 e).1 hn), fun fr1 hc => ?_⟩
  obtain ⟨fr1', hc', hj1⟩ := (h1 e).2 fr1 hc
  obtain ⟨fr1'', hc'', hj2⟩ := (h2 e).2 fr1' hc'
  exact ⟨fr1'', hc'', (hj1.comp hj2).mono fun x z ⟨y, hxy, hyz⟩ m hm => ⟨y, hxy m hm, hyz m hm⟩⟩

theorem HContM.mono {syms} {R R' : Frame → Frame → Mem → Prop} (hR : ∀ a b m, R a b m → R' a b m)
    {fr fr' : Frame} {et et' : ExnTable} (h : HContM syms R fr et fr' et') :
    HContM syms R' fr et fr' et' := by
  intro e
  refine ⟨(h e).1, fun fr1 hc => ?_⟩
  obtain ⟨fr1', hc', hj⟩ := (h e).2 fr1 hc
  exact ⟨fr1', hc', hj.mono fun a b h m hm => hR _ _ _ (h m hm)⟩

theorem IsSimMU.comp {syms R₁ R₂} (h1 : IsSimMU syms R₁) (h2 : IsSimMU syms R₂) :
    IsSimMU syms (fun x z m => ∃ y, R₁ x y m ∧ R₂ y z m) where
  toIsSimM := h1.toIsSimM.comp h2.toIsSimM
  ci := by
    rintro fr fr'' m st rest sig callee args d a vals ⟨fr', ha, hb⟩ hm hs hi hca
    obtain ⟨f2, st2, rest2, sig2, ce2, args2, hs1, hb2, hi2, hca2, hk1⟩ := h1.ci ha hm hs hi hca
    obtain ⟨g2, hs2, hr2⟩ := h2.toIsSimM.star hb hm hs1
    obtain ⟨g3, st3, rest3, sig3, ce3, args3, hs3, hb3, hi3, hca3, hk3⟩ :=
      h2.ci hr2 hm hb2 hi2 hca2
    exact ⟨g3, st3, rest3, sig3, ce3, args3, hs2.trans hs3, hb3, hi3, hca3, hk1.comp hk3⟩
  tc := by
    refine ⟨?_, ?_⟩
    · rintro fr fr'' m fn args et n base bc ext vals ⟨fr', ha, hb⟩ hm hs ht htc hca
      obtain ⟨f2, fn2, args2, et2, base2, bc2, hs1, hb2, ht2, htc2, hca2, hk1, hh1⟩ :=
        h1.tc.call ha hm hs ht htc hca
      obtain ⟨g2, hs2, hr2⟩ := h2.toIsSimM.star hb hm hs1
      obtain ⟨g3, fn3, args3, et3, base3, bc3, hs3, hb3, ht3, htc3, hca3, hk3, hh3⟩ :=
        h2.tc.call hr2 hm hb2 ht2 htc2 hca2
      exact ⟨g3, fn3, args3, et3, base3, bc3, hs2.trans hs3, hb3, ht3, htc3, hca3, hk1.comp hk3,
        hh1.comp hh3⟩
    · rintro fr fr'' m callee args et n base bc d a vals ⟨fr', ha, hb⟩ hm hs ht htc hca
      obtain ⟨f2, c2, args2, et2, base2, bc2, hs1, hb2, ht2, htc2, hca2, hk1, hh1⟩ :=
        h1.tc.ind ha hm hs ht htc hca
      obtain ⟨g2, hs2, hr2⟩ := h2.toIsSimM.star hb hm hs1
      obtain ⟨g3, c3, args3, et3, base3, bc3, hs3, hb3, ht3, htc3, hca3, hk3, hh3⟩ :=
        h2.tc.ind hr2 hm hb2 ht2 htc2 hca2
      exact ⟨g3, c3, args3, et3, base3, bc3, hs2.trans hs3, hb3, ht3, htc3, hca3, hk1.comp hk3,
        hh1.comp hh3⟩

/-! ## From memory-blind simulations -/

theorem Cont.toM {syms} {R : Frame → Frame → Prop} {fr rs fr' rs' rtys}
    (h : Cont R fr rs fr' rs' rtys) : ContM syms (fun a b _ => R a b) fr rs fr' rs' rtys :=
  fun vs regs _ ht _ hr => h vs regs ht hr

theorem TCont.toM {syms} {R : Frame → Frame → Prop} {fr : Frame} {rs : List ValueId}
    {bc : BlockCall} {fr' : Frame} {rs' : List ValueId} {bc' : BlockCall} {rtys : List Ty}
    (h : TCont R fr rs bc fr' rs' bc' rtys) :
    TContM syms (fun a b _ => R a b) fr rs bc fr' rs' bc' rtys :=
  fun vs regs _ ht _ hr => h vs regs ht hr

theorem HCont.toM {syms} {R : Frame → Frame → Prop} {fr : Frame} {et : ExnTable} {fr' : Frame}
    {et' : ExnTable} (h : HCont R fr et fr' et') :
    HContM syms (fun a b _ => R a b) fr et fr' et' := by
  intro e
  refine ⟨(h e).1, fun fr1 hc => ?_⟩
  obtain ⟨fr1', hc', hj⟩ := (h e).2 fr1 hc
  exact ⟨fr1', hc', hj.mono fun _ _ h _ _ => h⟩

/-- A memory-blind simulation is a memory-aware one. -/
theorem IsSimU.toMU {syms R} (h : IsSimU syms R) : IsSimMU syms (fun a b _ => R a b) where
  toIsSimM := {
    frame := fun hr => h.toIsSim.frame hr
    next := fun hr hm hs => h.toIsSim.next hr hm hs
    call := by
      intro fr fr' m ext vals rs rest hr hm hs
      obtain ⟨fr2, rs', rest', h1, h2, hk⟩ := h.toIsSim.call hr hm hs
      exact ⟨fr2, rs', rest', h1, h2, hk.toM⟩
    ret := fun hr hm hs => h.toIsSim.ret hr hm hs
    tail := fun hr hm hs => h.toIsSim.tail hr hm hs
    trap := fun hr hm hs => h.toIsSim.trap hr hm hs }
  ci := by
    intro fr fr' m st rest sig callee args d a vals hr hm hb hi hca
    obtain ⟨fr2, st', rest', sig', callee', args', h1, h2, h3, h4, hk⟩ := h.ci hr hm hb hi hca
    exact ⟨fr2, st', rest', sig', callee', args', h1, h2, h3, h4, hk.toM⟩
  tc := by
    refine ⟨?_, ?_⟩
    · intro fr fr' m fn args et n base bc ext vals hr hm hb ht htc hca
      obtain ⟨fr2, fn', args', et', base', bc', h1, h2, h3, h4, h5, hk, hh⟩ :=
        h.tc.call hr hm hb ht htc hca
      exact ⟨fr2, fn', args', et', base', bc', h1, h2, h3, h4, h5, hk.toM, hh.toM⟩
    · intro fr fr' m callee args et n base bc d a vals hr hm hb ht htc hca
      obtain ⟨fr2, c', args', et', base', bc', h1, h2, h3, h4, h5, hk, hh⟩ :=
        h.tc.ind hr hm hb ht htc hca
      exact ⟨fr2, c', args', et', base', bc', h1, h2, h3, h4, h5, hk.toM, hh.toM⟩

/-! ## Functions -/

/-- `g` simulates `f` with a memory-aware simulation, the handler edges included; the entry
frames are related at every memory with the symbols. -/
structure FunSimMU (f g : Function) : Prop where
  name : g.name = f.name
  sig : g.sig = f.sig
  slots : g.slots = f.slots
  externs : g.externs = f.externs
  sim : ∀ syms, ∃ R, IsSimMU syms R ∧ ∀ b, f.entry? = some b → ∃ b', g.entry? = some b' ∧
    b'.params = b.params ∧ ∀ args regs (slots : List (SlotId × Nat)) (m : Mem),
      args.map (·.ty) = b.params.map (·.2) →
      Regs.empty.setMany (b.params.map (·.1)) args = some regs →
      slots.map (·.1) = f.slots.map (·.1) → m.symbols = syms →
      R ⟨f, regs, slots, b.body, b.term⟩ ⟨g, regs, slots, b'.body, b'.term⟩ m

theorem FunSimU.toMU {f g : Function} (h : FunSimU f g) : FunSimMU f g where
  name := h.name
  sig := h.sig
  slots := h.slots
  externs := h.externs
  sim syms := by
    obtain ⟨R, hR, he⟩ := h.sim syms
    refine ⟨_, hR.toMU, fun b hb => ?_⟩
    obtain ⟨b', hb', hp, hr⟩ := he b hb
    exact ⟨b', hb', hp, fun args regs slots _ ht hrg hsl _ => hr args regs slots ht hrg hsl⟩

theorem FunSimMU.refl (f : Function) : FunSimMU f f := (FunSimU.refl f).toMU

theorem FunSimMU.trans {f g h : Function} (h1 : FunSimMU f g) (h2 : FunSimMU g h) :
    FunSimMU f h where
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
    refine ⟨b'', hb'', hp''.trans hp', fun args regs slots m ht hr hsl hm => ?_⟩
    refine ⟨_, hr1 args regs slots m ht hr hsl hm, ?_⟩
    rw [← hp'] at ht hr
    exact hr2 args regs slots m ht hr (hsl.trans (by rw [h1.slots])) hm

/-! ## Programs -/

/-- Pointwise `FunSimMU` between the functions of two programs. -/
inductive FunsSimMU : List Function → List Function → Prop
  | nil : FunsSimMU [] []
  | cons {f g fs gs} : FunSimMU f g → FunsSimMU fs gs → FunsSimMU (f :: fs) (g :: gs)

theorem FunsSimMU.map {fs : List Function} {T : Function → Function}
    (h : ∀ f, FunSimMU f (T f)) : FunsSimMU fs (fs.map T) := by
  induction fs with
  | nil => exact .nil
  | cons f fs ih => exact .cons (h f) ih

theorem FunsSimU.toMU {fs gs : List Function} (h : FunsSimU fs gs) : FunsSimMU fs gs := by
  induction h with
  | nil => exact .nil
  | cons hf _ ih => exact .cons hf.toMU ih

/-- Corresponding functions are found by any predicate on their names. -/
theorem FunsSimMU.findP {fs gs : List Function} (h : FunsSimMU fs gs) (P : String → Bool) :
    (∀ f, fs.find? (fun x => P x.name) = some f →
      ∃ g, gs.find? (fun x => P x.name) = some g ∧ FunSimMU f g) ∧
      (fs.find? (fun x => P x.name) = none → gs.find? (fun x => P x.name) = none) := by
  induction h with
  | nil => simp
  | @cons f g fs gs hfg _ ih =>
    simp only [List.find?_cons, hfg.name]
    split
    · exact ⟨fun f' hf => by cases hf; exact ⟨g, rfl, hfg⟩, fun h => (by cases h)⟩
    · exact ih

theorem FunsSimMU.externNames {fs gs : List Function} (h : FunsSimMU fs gs) :
    gs.flatMap (fun f => f.externs.map (·.2.name)) =
      fs.flatMap (fun f => f.externs.map (·.2.name)) := by
  induction h with
  | nil => rfl
  | cons hf _ ih => simp only [List.flatMap_cons, hf.externs, ih]

end Opt
