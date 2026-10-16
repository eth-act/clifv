import FV.Opt.Proof.SimWin
import FV.Opt.Proof.SemSimU

/-!
# Fresh-value windows with handler edges (S10f, #233)

`FV/Opt/Proof/SimWin.lean` with the handler edges of `IsSimU`: a handler of a `try_call` binds
the exception payload at the function's fresh values (`Clif.catchIn`), so frames with equal
windows (`Win`) have equal windows after resuming at handlers. `IsSimWU R` is `IsSimW R` with
`HCont` for the same target `try_call`; `IsSimWU.toU`: `W R` is then an `IsSimU`;
`FunSimU.ofWU` builds the function simulation. `tryHandler_pair`: a handler successor of a
renamed table (`TryDest.mapVals σ`) is the same block with the renamed values or the payload's
values at the other side's fresh value.
-/

namespace Opt

open Clif

/-- `TryOkW` with the handler edges of the same target `try_call`. -/
structure TryOkWU (syms : String → Option Nat) (R : Frame → Frame → Prop) : Prop where
  call : ∀ {fr fr' : Frame} {m : Mem} {fn : FnRef} {args : List ValueId} {et : ExnTable}
    {n : Nat} {base : ValueId} {bc : BlockCall} {ext : ExtFunc} {vals : List Val},
    R fr fr' → InB fr → InB fr' → Win fr fr' → m.symbols = syms → fr.body = [] →
    fr.term = .tryCall fn args et →
    tcArgs fr fn et = .ok (n, base, bc) → callArgs fr fn args = .ok (ext, vals) →
    ∃ fr2 fn' args' et' base' bc', LStar fr' m fr2 m ∧ fr2.body = [] ∧
      fr2.term = .tryCall fn' args' et' ∧ tcArgs fr2 fn' et' = .ok (n, base', bc') ∧
      callArgs fr2 fn' args' = .ok (ext, vals) ∧
      TCont R fr (tryRets n base) bc fr2 (tryRets n base') bc' (AbiParam.tys ext.sig.returns) ∧
      HCont R fr et fr2 et'
  ind : ∀ {fr fr' : Frame} {m : Mem} {callee : ValueId} {args : List ValueId} {et : ExnTable}
    {n : Nat} {base : ValueId} {bc : BlockCall} {d : Signature} {a : Nat} {vals : List Val},
    R fr fr' → InB fr → InB fr' → Win fr fr' → m.symbols = syms → fr.body = [] →
    fr.term = .tryCallIndirect callee args et →
    ticArgs fr et = .ok (n, base, bc) → ciArgs fr et.sig callee args = .ok (d, a, vals) →
    ∃ fr2 callee' args' et' base' bc', LStar fr' m fr2 m ∧ fr2.body = [] ∧
      fr2.term = .tryCallIndirect callee' args' et' ∧ ticArgs fr2 et' = .ok (n, base', bc') ∧
      ciArgs fr2 et'.sig callee' args' = .ok (d, a, vals) ∧
      TCont R fr (tryRets n base) bc fr2 (tryRets n base') bc' (AbiParam.tys d.returns) ∧
      HCont R fr et fr2 et'

/-- A pass simulation with windows and handler edges. -/
structure IsSimWU (syms : String → Option Nat) (R : Frame → Frame → Prop) : Prop where
  toIsSim : IsSim syms R
  ci : CIOkW syms R
  tc : TryOkWU syms R

/-- The windows of a frame resumed at a handler: the payload, then what the frame held. -/
theorem catchIn_win {fr fr1 : Frame} {et : ExnTable} {e : Exn}
    (h : catchIn fr et e = some (.ok fr1)) :
    fr1.func = fr.func ∧ ∀ i, fr1.regs (fr.func.freshValue + i) =
      if i < e.payload.length then e.payload[i]? else fr.regs (fr.func.freshValue + i) := by
  obtain ⟨d, bc, regs, -, -, hr, rfl⟩ := catchIn_ok h
  exact ⟨rfl, setMany_tryRets (n := e.payload.length) (W := fr.func.freshValue) hr⟩

/-- Handler edges, with program points and windows. -/
theorem HCont.win {R : Frame → Frame → Prop} {fr fr2 : Frame} {et et' : ExnTable}
    (hw : Win fr fr2) (h : HCont R fr et fr2 et') : HCont (W R) fr et fr2 et' := by
  intro e
  refine ⟨(h e).1, fun fr1 hc => ?_⟩
  obtain ⟨fr1', hc', hb, hb', bc, bc', ht, ht', hj⟩ := (h e).2 fr1 hc
  refine ⟨fr1', hc', hb, hb', bc, bc', ht, ht', fun a1 he => ?_⟩
  obtain ⟨b1, he', hr⟩ := hj a1 he
  obtain ⟨hf1, hw1⟩ := catchIn_win hc
  obtain ⟨hf1', hw1'⟩ := catchIn_win hc'
  obtain ⟨hI1, hfa, -, hwa⟩ := enterBlock_win he
  obtain ⟨hI1', hfb, -, hwb⟩ := enterBlock_win he'
  refine ⟨b1, he', hr, hI1, hI1', fun i => ?_⟩
  show a1.regs (a1.func.freshValue + i) = b1.regs (b1.func.freshValue + i)
  rw [hfa, hfb, hwa i, hwb i, hf1, hf1', hw1 i, hw1' i]
  split
  · rfl
  · exact hw i

theorem IsSimWU.toW {syms : String → Option Nat} {R : Frame → Frame → Prop} (hR : IsSimWU syms R) :
    IsSimW syms R where
  toIsSim := hR.toIsSim
  ci := hR.ci
  tc := ⟨fun h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
      obtain ⟨fr2, fn', args', et', base', bc', a1, a2, a3, a4, a5, a6, -⟩ :=
        hR.tc.call h1 h2 h3 h4 h5 h6 h7 h8 h9
      exact ⟨fr2, fn', args', et', base', bc', a1, a2, a3, a4, a5, a6⟩,
    fun h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
      obtain ⟨fr2, c', args', et', base', bc', a1, a2, a3, a4, a5, a6, -⟩ :=
        hR.tc.ind h1 h2 h3 h4 h5 h6 h7 h8 h9
      exact ⟨fr2, c', args', et', base', bc', a1, a2, a3, a4, a5, a6⟩⟩

/-- **A pass simulation with windows and handler edges is a simulation with handler edges.** -/
theorem IsSimWU.toU {syms : String → Option Nat} {R : Frame → Frame → Prop} (hR : IsSimWU syms R) :
    IsSimU syms (W R) where
  toIsSim := hR.toW.toX.toIsSim
  ci := hR.toW.toX.ci
  tc := by
    refine ⟨?_, ?_⟩
    · rintro fr fr' m fn args et n base bc ext vals ⟨h, hI, hI', hw⟩ hm hb ht htc hca
      obtain ⟨fr2, fn', args', et', base', bc', hst, hb2, ht2, htc2, hca2, hk, hh⟩ :=
        hR.tc.call h hI hI' hw hm hb ht htc hca
      obtain ⟨hI2, hf2, hw2⟩ := LStar.win hI' hst
      have hw' : Win fr fr2 := fun i => by rw [hf2, hw2 i]; exact hw i
      obtain ⟨rfl, -⟩ := tcArgs_base htc
      obtain ⟨rfl, -⟩ := tcArgs_base htc2
      exact ⟨fr2, fn', args', et', _, bc', hst, hb2, ht2, htc2, hca2, hk.win hw', hh.win hw'⟩
    · rintro fr fr' m callee args et n base bc d a vals ⟨h, hI, hI', hw⟩ hm hb ht htc hca
      obtain ⟨fr2, callee', args', et', base', bc', hst, hb2, ht2, htc2, hca2, hk, hh⟩ :=
        hR.tc.ind h hI hI' hw hm hb ht htc hca
      obtain ⟨hI2, hf2, hw2⟩ := LStar.win hI' hst
      have hw' : Win fr fr2 := fun i => by rw [hf2, hw2 i]; exact hw i
      obtain ⟨rfl, -⟩ := ticArgs_base htc
      obtain ⟨rfl, -⟩ := ticArgs_base htc2
      exact ⟨fr2, callee', args', et', _, bc', hst, hb2, ht2, htc2, hca2, hk.win hw', hh.win hw'⟩

/-- A function simulation with handler edges from a pass simulation with windows (`FunSimX.ofW`). -/
theorem FunSimU.ofWU {f g : Function} (hn : g.name = f.name) (hs : g.sig = f.sig)
    (hsl : g.slots = f.slots) (hx : g.externs = f.externs)
    (hsim : ∀ syms, ∃ R, IsSimWU syms R ∧ ∀ b, f.entry? = some b → ∃ b', g.entry? = some b' ∧
      b'.params = b.params ∧ ∀ args regs (slots : List (SlotId × Nat)),
        args.map (·.ty) = b.params.map (·.2) →
        Regs.empty.setMany (b.params.map (·.1)) args = some regs →
        slots.map (·.1) = f.slots.map (·.1) →
        R ⟨f, regs, slots, b.body, b.term⟩ ⟨g, regs, slots, b'.body, b'.term⟩) :
    FunSimU f g where
  name := hn
  sig := hs
  slots := hsl
  externs := hx
  sim syms := by
    obtain ⟨R, hR, he⟩ := hsim syms
    refine ⟨W R, hR.toU, fun b hb => ?_⟩
    obtain ⟨b', hb', hp, hr⟩ := he b hb
    refine ⟨b', hb', hp, fun args regs slots ht hset hsl' => ⟨hr args regs slots ht hset hsl',
      ⟨trivial, b, List.mem_of_mem_head? hb, List.suffix_refl _, rfl⟩,
      ⟨trivial, b', List.mem_of_mem_head? hb', List.suffix_refl _, rfl⟩, fun i => ?_⟩⟩
    have hbm : b ∈ f.blocks := List.mem_of_mem_head? hb
    have hbm' : b' ∈ g.blocks := List.mem_of_mem_head? hb'
    have h1 := setMany_above hset (fun x hx => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx; exact (lt_freshValue hbm).1 p hp) i
    have hset' := hset
    rw [← hp] at hset'
    have h2 := setMany_above hset' (fun x hx => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx; exact (lt_freshValue hbm').1 p hp) i
    show regs (f.freshValue + i) = regs (g.freshValue + i)
    rw [h1, h2]; rfl

/-! ## Handler successors of renamed tables -/

theorem resolveH_pair (σ : ValueId → ValueId) (g : TryArg → TryArg)
    (hv : ∀ v, g (.val v) = .val (σ v)) (hr : ∀ i, g (.ret i) = .ret i)
    (he : ∀ i, g (.exn i) = .exn i) (b1 b2 : ValueId) :
    ∀ (l : List TryArg) (xs : List ValueId), resolveH b1 l = .ok xs →
      ∃ ys, resolveH b2 (l.map g) = .ok ys ∧
        Pw2 (fun x y => (∃ v, TryArg.val v ∈ l ∧ x = v ∧ y = σ v) ∨ ∃ i, x = b1 + i ∧ y = b2 + i)
          xs ys
  | [], xs, h => by
    simp only [resolveH] at h
    cases h
    exact ⟨[], rfl, .nil⟩
  | a :: l, xs, h => by
    simp only [resolveH, Res.bind_eq_ok, Res.pure_eq_ok] at h
    obtain ⟨x, hx, xs', hxs, rfl⟩ := h
    obtain ⟨ys, hys, h2⟩ := resolveH_pair σ g hv hr he b1 b2 l xs' hxs
    have h2' : Pw2 (fun x y => (∃ v, TryArg.val v ∈ a :: l ∧ x = v ∧ y = σ v) ∨
        ∃ i, x = b1 + i ∧ y = b2 + i) xs' ys := h2.imp fun x y h => by
      rcases h with ⟨v, hm, h1, h2⟩ | h
      · exact Or.inl ⟨v, List.mem_cons_of_mem _ hm, h1, h2⟩
      · exact Or.inr h
    cases a with
    | val v =>
      simp only [Res.pure_eq_ok] at hx; subst hx
      refine ⟨σ v :: ys, ?_, .cons (.inl ⟨v, by simp, rfl, rfl⟩) h2'⟩
      simp only [List.map_cons, hv, resolveH, hys]; rfl
    | exn i =>
      simp only [Res.pure_eq_ok] at hx; subst hx
      refine ⟨(b2 + i) :: ys, ?_, .cons (.inr ⟨i, rfl, rfl⟩) h2'⟩
      simp only [List.map_cons, he, resolveH, hys]; rfl
    | ret i => cases hx

/-- The handler successor of a renamed destination, from other fresh values: the same block;
arguments the renamed values or the payload's values. -/
theorem tryHandler_pair (σ : ValueId → ValueId) {d : TryDest} {b1 b2 : ValueId}
    {bc1 : BlockCall} (h : tryHandler d b1 = .ok bc1) :
    ∃ bc2, tryHandler (d.mapVals σ) b2 = .ok bc2 ∧ bc2.block = bc1.block ∧
      Pw2 (fun x y => (∃ v ∈ d.vals, x = v ∧ y = σ v) ∨
        ∃ i, x = b1 + i ∧ y = b2 + i) bc1.args bc2.args := by
  rw [tryHandler_eq] at h ⊢
  simp only [Res.bind_eq_ok, Res.pure_eq_ok] at h
  obtain ⟨args1, hm1, rfl⟩ := h
  simp only [TryDest.mapVals]
  obtain ⟨ys, hys, h2⟩ := resolveH_pair σ
    (fun (a : TryArg) => match a with | TryArg.val v => TryArg.val (σ v) | a => a)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) b1 b2 _ _ hm1
  refine ⟨_, by simp only [Res.bind_eq_ok]; exact ⟨ys, hys, rfl⟩, rfl, ?_⟩
  refine h2.imp fun x y hp => ?_
  rcases hp with ⟨v, hv, hx, hy⟩ | h
  · exact .inl ⟨v, List.mem_filterMap.2 ⟨_, hv, rfl⟩, hx, hy⟩
  · exact .inr h

/-- A frame resumed at a handler with the payload bound at its fresh values: the registers
below the fresh value are kept. -/
theorem catch_regs_lo {fr : Frame} {e : Exn} {regs : Regs} {F : Nat}
    (hset : fr.regs.setMany ((List.range e.payload.length).map (fr.func.freshValue + ·)) e.payload =
      some regs) (hF : fr.func.freshValue = F) : ∀ v < F, regs v = fr.regs v := by
  intro v hv
  refine ((setMany_spec hset).2 v).1 fun hm => ?_
  obtain ⟨j, -, he⟩ := List.mem_map.1 hm
  have he' : fr.func.freshValue + j = v := he
  rw [hF] at he'
  exact no_window' he' hv

end Opt
