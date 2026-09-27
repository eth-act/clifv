import FV.Backend.Proof.LowerContract

/-!
# CLIF frames seen by the driver

`restrict fr A`: the frame with only the values of `A` defined — the driver hands M4's contracts
the values its invariant tracks (`A`: the values available at the point, an SSA certificate), not
stale ones. `instOutcome_congr`/`evalInst_congr`: an instruction only reads its operands
(`instArgs`). Pure instructions leave memory alone and do not depend on it.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- The value operands of a CLIF instruction. -/
def instArgs : Clif.Inst → List Clif.ValueId
  | .iconst .. | .stackAddr .. | .fence | .nop | .symbolValue .. => []
  | .unary _ _ x | .bmask _ x | .extend _ _ x | .ireduce _ x | .isplit _ x
  | .load _ _ _ x _ | .atomicLoad _ _ x | .bitcast _ _ x | .trapz x _ | .trapnz x _ => [x]
  | .binary _ _ x y | .div _ _ x y | .overflow _ _ x y | .icmp _ _ x y
  | .uaddOverflowTrap _ x y _ | .iconcat _ x y | .store _ _ _ x y _ | .atomicRmw _ _ _ x y
  | .atomicStore _ _ x y => [x, y]
  | .carry _ _ x y z | .select _ x y z | .selectSpectreGuard _ x y z | .bitselect _ x y z
  | .atomicCas _ _ x y z => [x, y, z]
  | .call _ args => args

/-- The value operands of a terminator. -/
def termArgs : Clif.Terminator → List Clif.ValueId
  | .jump bc => bc.args
  | .brif c t e => c :: t.args ++ e.args
  | .brTable x d tbl => x :: d.args ++ tbl.flatMap (·.args)
  | .ret xs => xs
  | .returnCall _ args => args
  | .trap _ => []

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

/-- Filling in a terminator's data keeps DFG consistency (terminators define no values). -/
theorem dfgCons_termCtx {ctx : Ctx} {fr : Clif.Frame} (h : DFGCons ctx fr) (ti : Nat) (data : V) :
    DFGCons (termCtx ctx ti data) fr := by
  intro x j info cl v hd hj hcl hp hv
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

end Backend.Proof.Driver
