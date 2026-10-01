import FV.Backend.Proof.LowerContract

/-!
# CLIF frames seen by the driver

`restrict fr A`: the frame with only the values of `A` defined — the driver hands M4's contracts
the values its invariant tracks (`A`: the values available at the point, an SSA certificate), not
stale ones. `instOutcome_congr`/`evalInst_congr`: an instruction only reads its operands
(`instArgs`). Pure instructions leave memory alone and do not depend on it. `instOutcome_types`:
the results have the instruction's result types (`Inst.resultTypes`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- `fr` with only the values in `A` defined. -/
def restrict (fr : Clif.Frame) (A : List Clif.ValueId) : Clif.Frame :=
  { fr with regs := fun x => if x ∈ A then fr.regs x else none }

theorem get_congr {fr fr' : Clif.Frame} {x : Clif.ValueId} (h : fr'.regs x = fr.regs x) :
    fr'.get x = fr.get x := by
  simp only [Clif.Frame.get, h]

theorem getAs_congr {fr fr' : Clif.Frame} {x : Clif.ValueId} {ty : Clif.Ty}
    (h : fr'.regs x = fr.regs x) : fr'.getAs x ty = fr.getAs x ty := by
  simp only [Clif.Frame.getAs, get_congr h]

theorem getMany_congr {fr fr' : Clif.Frame} :
    ∀ {xs : List Clif.ValueId}, (∀ x ∈ xs, fr'.regs x = fr.regs x) →
      fr'.getMany xs = fr.getMany xs := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    simp only [Clif.Frame.getMany, get_congr (h x (by simp)),
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- An instruction only reads its operands (and the frame's function and slots). -/
theorem evalInst_congr {fr fr' : Clif.Frame} (hf : fr'.func = fr.func) (hs : fr'.slots = fr.slots)
    (cm : Clif.Mem) (i : Clif.Inst) (h : ∀ x ∈ instArgs i, fr'.regs x = fr.regs x) :
    Clif.evalInst fr' cm i = Clif.evalInst fr cm i := by
  cases i <;> simp only [instArgs, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq] at h <;>
    simp only [Clif.evalInst, Clif.Frame.getAs, Clif.Frame.get, h, hf, hs]

theorem instOutcome_congr {fr fr' : Clif.Frame} (hf : fr'.func = fr.func)
    (hs : fr'.slots = fr.slots) (env : Clif.Env) (p : Clif.Program) (cm : Clif.Mem)
    (i : Clif.Inst) (h : ∀ x ∈ instArgs i, fr'.regs x = fr.regs x) :
    instOutcome env p fr' cm i = instOutcome env p fr cm i := by
  cases i with
  | call fn args =>
    simp only [instArgs] at h
    simp only [instOutcome, hf, getMany_congr h]
  | callIndirect sig callee args =>
    simp only [instArgs, List.mem_cons] at h
    have hc : fr'.get callee = fr.get callee := by
      simp only [Clif.Frame.get, h callee (.inl rfl)]
    simp only [instOutcome, hf, hc, getMany_congr (fun x hx => h x (.inr hx))]
  | _ => simp only [instOutcome]; exact evalInst_congr hf hs cm _ h

theorem restrict_regs_of_mem {fr : Clif.Frame} {A : List Clif.ValueId} {x : Clif.ValueId}
    (h : x ∈ A) : (restrict fr A).regs x = fr.regs x := by
  simp [restrict, h]

theorem restrict_regs_isSome {fr : Clif.Frame} {A : List Clif.ValueId} {x : Clif.ValueId}
    (h : ((restrict fr A).regs x).isSome) : x ∈ A := by
  by_cases hx : x ∈ A
  · exact hx
  · simp [restrict, hx] at h

theorem Res.bind_bind {α β γ : Type} (x : Clif.Res α) (f : α → Clif.Res β) (g : β → Clif.Res γ) :
    Clif.Res.bind (x >>= f) g = x >>= fun a => Clif.Res.bind (f a) g := by
  cases x <;> rfl

/-- A pure instruction's values do not depend on memory, and it leaves memory unchanged. -/
theorem evalInst_pure_eq {fr : Clif.Frame} {cl : Clif.Inst} (hp : pureInst cl = true)
    (cm : Clif.Mem) :
    Clif.evalInst fr cm cl =
      Clif.Res.bind (Clif.evalInst fr Clif.Mem.empty cl) (fun p => .ok (p.1, cm)) := by
  cases cl <;> simp [pureInst] at hp
  case extend op _ _ => cases op <;> simp only [Clif.evalInst, Res.bind_bind] <;> rfl
  case binary op _ _ _ =>
    simp only [Clif.evalInst, Res.bind_bind]
    congr 1; funext a
    split <;> (simp only [Res.bind_bind]; rfl)
  all_goals (simp only [Clif.evalInst, Res.bind_bind]; rfl)

theorem evalInst_pure {fr : Clif.Frame} {cm cm' : Clif.Mem} {cl : Clif.Inst}
    {vals : List Clif.Val} (hp : pureInst cl = true) (h : Clif.evalInst fr cm cl = .ok (vals, cm')) :
    cm' = cm ∧ ∀ cm₂, Clif.evalInst fr cm₂ cl = .ok (vals, cm₂) := by
  rw [evalInst_pure_eq hp] at h
  cases hE : Clif.evalInst fr Clif.Mem.empty cl with
  | ok q =>
    rw [hE] at h
    simp only [Clif.Res.bind, Clif.Res.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, fun cm₂ => ?_⟩
    rw [evalInst_pure_eq hp, hE]; rfl
  | trap => rw [hE] at h; cases h
  | stuck => rw [hE] at h; cases h

/-- Filling in a terminator's data keeps DFG consistency (terminators define no values; the
value types are unchanged). -/
theorem dfgCons_termCtx {ctx : Ctx} {fr : Clif.Frame} (h : DFGCons ctx fr) (ti : Nat) (data : V) :
    DFGCons (termCtx ctx ti data) fr := by
  refine ⟨?_, h.2⟩
  intro x j info cl v hd hj hcl hp hv
  have h := h.1
  have hd' : ctx.defInst? x = some j := hd
  by_cases e : j = ti
  · subst e
    change (ctx.insts.set! j ⟨data, [], [], none⟩)[j]? = some info at hj
    rw [Array.set!_eq_setIfInBounds] at hj
    by_cases hlt : j < ctx.insts.size
    · rw [Array.getElem?_setIfInBounds_self_of_lt hlt] at hj
      simp only [Option.some.injEq] at hj; subst hj; cases hcl
    · simp only [Array.setIfInBounds, hlt, dite_false] at hj
      exact h x j info cl v hd' hj hcl hp hv
  · change (ctx.insts.set! ti ⟨data, [], [], none⟩)[j]? = some info at hj
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm e)] at hj
    exact h x j info cl v hd' hj hcl hp hv

/-! ## Typing: results have the declared result types -/

theorem res_bind_eq_ok {α β : Type} {x : Clif.Res α} {f : α → Clif.Res β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Clif.Res.bind]

theorem res_bind_eq_ok' {α β : Type} {x : Clif.Res α} {f : α → Clif.Res β} {b : β} :
    Clif.Res.bind x f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [Clif.Res.bind]

theorem res_ofOption_eq_ok {α : Type} {m : String} {o : Option α} {a : α} :
    Clif.Res.ofOption m o = .ok a ↔ o = some a := by
  cases o <;> simp [Clif.Res.ofOption]

/-- The CLIF outcome of an indirect call that returns: the call site's signature, the callee
address (an `i64` value), the extern at that address, and its results. -/
theorem instOutcome_callIndirect_ok {env : Clif.Env} {cp : Clif.Program} {fr : Clif.Frame}
    {cm : Clif.Mem} {sig callee : Nat} {args : List Clif.ValueId} {rvals : List Clif.Val}
    {cm' : Clif.Mem}
    (h : instOutcome env cp fr cm (.callIndirect sig callee args) = .ok (rvals, cm')) :
    ∃ (declared : Clif.Signature) (x : BitVec 64) (vals : List Clif.Val) (name : String)
      (g : List Clif.Val → Clif.Mem → Clif.Outcome), fr.func.sigDecls.lookup sig = some declared ∧
      fr.get callee = .ok ⟨.i64, x⟩ ∧ fr.getMany args = .ok vals ∧
      cm.symbols name = some x.toNat ∧ env.extern name = some g ∧
      vals.map (·.ty) = Clif.AbiParam.tys declared.params ∧ g vals cm = .returned rvals cm' ∧
      rvals.map (·.ty) = Clif.AbiParam.tys declared.returns := by
  simp only [instOutcome] at h
  obtain ⟨⟨declared, addr, vals⟩, h1, h2⟩ := res_bind_eq_ok'.mp h
  obtain ⟨d', hd, h1⟩ := res_bind_eq_ok.mp h1
  obtain ⟨cv, hcv, h1⟩ := res_bind_eq_ok.mp h1
  obtain ⟨cv64, hcv64, h1⟩ := res_bind_eq_ok.mp h1
  obtain ⟨vs, hvs, h1⟩ := res_bind_eq_ok.mp h1
  simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  rw [res_ofOption_eq_ok] at hd hcv64
  have hcv' := val_as_i64 hcv64
  subst hcv'
  simp only at h2
  split at h2
  · cases h2
  · simp only [Clif.callExternAt] at h2
    obtain ⟨name, hname, h2⟩ := res_bind_eq_ok.mp h2
    obtain ⟨g, hg, h2⟩ := res_bind_eq_ok.mp h2
    obtain ⟨u, hck, h2⟩ := res_bind_eq_ok.mp h2
    rw [res_ofOption_eq_ok] at hname hg
    have hsym := List.find?_some hname
    simp only [beq_iff_eq] at hsym
    have hty : vs.map (·.ty) = Clif.AbiParam.tys d'.params := by
      unfold Clif.checkTys Clif.Res.check at hck
      split at hck
      · rename_i hc; simpa using hc
      · cases hck
    split at h2
    · rename_i rv mem' hgo
      split at h2
      · rename_i hrt
        simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact ⟨d', cv64, vs, name, g, hd, hcv, hvs, hsym, hg, hty, hgo, by simpa using hrt⟩
      · cases h2
    all_goals cases h2

/-- **Typing of `evalInst`**: the results have the instruction's result types. -/
theorem evalInst_types {fr : Clif.Frame} {cm cm' : Clif.Mem} {i : Clif.Inst}
    {vals : List Clif.Val} {sigOf : Clif.FnRef → Option Clif.Signature}
    {sigDeclOf : Nat → Option Clif.Signature} {tys : List Clif.Ty}
    (h : Clif.evalInst fr cm i = .ok (vals, cm'))
    (ht : i.resultTypes sigOf sigDeclOf = some tys) :
    vals.map (·.ty) = tys := by
  cases i <;> simp only [Clif.evalInst] at h <;>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at ht
  all_goals (repeat' (first
    | (obtain ⟨_, _, h⟩ : ∃ _, _ ∧ _ := h)
    | (simp only [res_bind_eq_ok, Clif.Res.pure_eq, Clif.Res.ok.injEq,
        Prod.mk.injEq, res_ofOption_eq_ok] at h)
    | (split at h)))
  all_goals (try (first | (cases h; done) | (obtain ⟨rfl, -⟩ := h; subst ht; rfl) | (obtain ⟨rfl, -⟩ := h; simp_all)))

/-- **Typing of `instOutcome`** (calls: the extern's returns are checked against its
signature; indirect calls: against the call site's signature). -/
theorem instOutcome_types {env : Clif.Env} {p : Clif.Program} {fr : Clif.Frame}
    {cm cm' : Clif.Mem} {i : Clif.Inst} {vals : List Clif.Val} {tys : List Clif.Ty}
    (h : instOutcome env p fr cm i = .ok (vals, cm'))
    (ht : i.resultTypes (fun r => (fr.func.extern? r).map (·.sig)) (fr.func.sigDecls.lookup ·) =
      some tys) :
    vals.map (·.ty) = tys := by
  cases i with
  | call fn args =>
    simp only [Clif.Inst.resultTypes, Option.map_map] at ht
    simp only [instOutcome, res_bind_eq_ok', res_bind_eq_ok, res_ofOption_eq_ok] at h
    obtain ⟨⟨ext, vs⟩, ⟨e, he, a, -, -, -, hq⟩, h⟩ := h
    simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    rw [he] at ht
    simp only [Option.map_some, Function.comp_apply, Option.some.injEq] at ht
    subst ht
    simp only at h
    repeat' (first | (split at h) | (cases h; done))
    rename_i heq
    simp only [Clif.Res.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa [Clif.AbiParam.tys] using heq
  | callIndirect sig callee args =>
    obtain ⟨declared, x, vs, name, g, hd, -, -, -, -, -, -, hrty⟩ := instOutcome_callIndirect_ok h
    simp only [Clif.Inst.resultTypes, hd, Option.map_some, Option.some.injEq] at ht
    subst ht
    simpa [Clif.AbiParam.tys] using hrty
  | _ => simp only [instOutcome] at h; exact evalInst_types h ht

end Backend.Proof.Driver
