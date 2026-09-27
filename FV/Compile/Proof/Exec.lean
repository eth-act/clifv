import FV.Clif.Run

/-!
# Execution framework for the M2 proof

`Reach E P Q X s`: running from `s`, the machine eventually reaches a state in `Q`, or the run
ends (return from the outermost frame, or a trap) with an outcome in `X`. Simulation lemmas are
stated with `Reach`; `Reach.runLoop` turns a `Reach` with `Q = False` into the
`∃ fuel₀, ∀ fuel ≥ fuel₀` form (fuel monotonicity).
-/

set_option autoImplicit false

namespace Compile.Proof

open Clif

section
variable (E : Env) (P : Program)

inductive Reach (Q : State → Prop) (X : Outcome → Prop) : State → Prop
  | here {s : State} : Q s → Reach Q X s
  | next {s s' : State} : step E P s = .next s' → Reach Q X s' → Reach Q X s
  | done {s : State} {vals : List Val} {mem : Mem} :
      step E P s = .done vals mem → X (.returned vals mem) → Reach Q X s
  | trap {s : State} {c : TrapCode} : step E P s = .trapped c → X (.trapped c) → Reach Q X s

end

namespace Reach

variable {E : Env} {P : Program} {Q Q' : State → Prop} {X X' : Outcome → Prop}

theorem bind {s : State} (h : Reach E P Q X s) (k : ∀ s', Q s' → Reach E P Q' X s') :
    Reach E P Q' X s := by
  induction h with
  | here hq => exact k _ hq
  | next hs _ ih => exact .next hs ih
  | done hs hx => exact .done hs hx
  | trap hs hx => exact .trap hs hx

theorem mono {s : State} (h : Reach E P Q X s) (hq : ∀ s, Q s → Q' s)
    (hx : ∀ o, X o → X' o) : Reach E P Q' X' s := by
  induction h with
  | here h => exact .here (hq _ h)
  | next hs _ ih => exact .next hs ih
  | done hs h => exact .done hs (hx _ h)
  | trap hs h => exact .trap hs (hx _ h)

theorem step1 {s s' : State} (hs : step E P s = .next s') (h : Q s') : Reach E P Q X s :=
  .next hs (.here h)

/-- Fuel monotonicity: a run that reaches an outcome does so for all larger fuel. -/
theorem runLoop {s : State} (h : Reach E P (fun _ => False) X s) :
    ∃ n o, X o ∧ ∀ fuel ≥ n, Clif.runLoop E P fuel s = o := by
  induction h with
  | here h => exact h.elim
  | @next s s' hs _ ih =>
    obtain ⟨n, o, hx, hr⟩ := ih
    refine ⟨n + 1, o, hx, fun fuel hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [runLoop_succ, hs]
    exact hr f (by omega)
  | @done s vals mem hs hx =>
    refine ⟨1, _, hx, fun fuel hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [runLoop_succ, hs]
  | @trap s c hs hx =>
    refine ⟨1, _, hx, fun fuel hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [runLoop_succ, hs]

end Reach

/-! ## Registers -/

/-- `r` holds the values `vs` at the ids `xs`. -/
def RegsHas (r : Regs) (xs : List ValueId) (vs : List Val) : Prop := xs.map r = vs.map some

/-- `r'` agrees with `r` below `n`. -/
def Agree (r r' : Regs) (n : Nat) : Prop := ∀ x, x < n → r' x = r x

theorem Agree.refl (r : Regs) (n : Nat) : Agree r r n := fun _ _ => rfl

theorem Agree.trans {r₁ r₂ r₃ : Regs} {n m : Nat} (h₁ : Agree r₁ r₂ n) (h₂ : Agree r₂ r₃ m)
    (hmn : n ≤ m) : Agree r₁ r₃ n := fun x hx => by rw [h₂ x (by omega), h₁ x hx]

theorem Agree.mono {r₁ r₂ : Regs} {n m : Nat} (h : Agree r₁ r₂ m) (hmn : n ≤ m) :
    Agree r₁ r₂ n := fun x hx => h x (by omega)

theorem Agree.set {r : Regs} {n x : Nat} (v : Val) (hx : n ≤ x) : Agree r (r.set x v) n :=
  fun y hy => Regs.set_other (x := x) (y := y) r v (Nat.ne_of_lt (Nat.lt_of_lt_of_le hy hx))

theorem RegsHas.nil (r : Regs) : RegsHas r [] [] := rfl

theorem RegsHas.append {r : Regs} {xs ys : List ValueId} {vs ws : List Val}
    (h₁ : RegsHas r xs vs) (h₂ : RegsHas r ys ws) : RegsHas r (xs ++ ys) (vs ++ ws) := by
  simp only [RegsHas, List.map_append] at *; rw [h₁, h₂]

theorem RegsHas.length {r : Regs} {xs : List ValueId} {vs : List Val} (h : RegsHas r xs vs) :
    xs.length = vs.length := by
  have := congrArg List.length h; simpa using this

theorem RegsHas.agree {r r' : Regs} {n : Nat} {xs : List ValueId} {vs : List Val}
    (h : RegsHas r xs vs) (ha : Agree r r' n) (hx : ∀ x ∈ xs, x < n) : RegsHas r' xs vs := by
  unfold RegsHas at *
  rw [← h]
  exact List.map_congr_left fun x hm => ha x (hx x hm)

theorem RegsHas.single {r : Regs} {x : ValueId} {v : Val} (h : r x = some v) :
    RegsHas r [x] [v] := by simp [RegsHas, h]

theorem RegsHas.set_same (r : Regs) (x : ValueId) (v : Val) : RegsHas (r.set x v) [x] [v] :=
  .single (Regs.set_same r x v)

theorem RegsHas.take {r : Regs} {xs : List ValueId} {vs : List Val} (h : RegsHas r xs vs)
    (n : Nat) : RegsHas r (xs.take n) (vs.take n) := by
  unfold RegsHas at *; rw [List.map_take, h, List.map_take]

theorem RegsHas.drop {r : Regs} {xs : List ValueId} {vs : List Val} (h : RegsHas r xs vs)
    (n : Nat) : RegsHas r (xs.drop n) (vs.drop n) := by
  unfold RegsHas at *; rw [List.map_drop, h, List.map_drop]

theorem getMany_of_regsHas (fr : Frame) {xs : List ValueId} {vs : List Val}
    (h : RegsHas fr.regs xs vs) : fr.getMany xs = .ok vs := by
  induction xs generalizing vs with
  | nil => cases vs <;> simp_all [RegsHas, Frame.getMany]
  | cons x xs ih =>
    cases vs with
    | nil => simp [RegsHas] at h
    | cons v vs =>
      simp only [RegsHas, List.map_cons, List.cons.injEq] at h
      simp [Frame.getMany, Frame.get, h.1, ih h.2]

theorem setMany_some (r : Regs) :
    ∀ (xs : List ValueId) (vs : List Val), xs.length = vs.length →
      ∃ r', r.setMany xs vs = some r'
  | [], [], _ => ⟨r, rfl⟩
  | x :: xs, v :: vs, h => by
    simp only [Regs.setMany_cons]
    exact setMany_some (r.set x v) xs vs (by simpa using h)
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The registers after `setMany` hold the new values at the (distinct) ids. -/
theorem setMany_has {r r' : Regs} :
    ∀ {xs : List ValueId} {vs : List Val}, xs.Nodup → r.setMany xs vs = some r' →
      RegsHas r' xs vs
  | [], [], _, _ => rfl
  | x :: xs, v :: vs, hnd, h => by
    simp only [Regs.setMany_cons] at h
    have hnd' := List.nodup_cons.1 hnd
    have ih := setMany_has hnd'.2 h
    have hx : r' x = some v := by
      rw [setMany_other h hnd'.1]; simp
    simp only [RegsHas, List.map_cons, List.cons.injEq] at ih ⊢
    exact ⟨hx, ih⟩
  | [], _ :: _, _, h => by simp [Regs.setMany] at h
  | _ :: _, [], _, h => by simp [Regs.setMany] at h
where
  setMany_other {r r' : Regs} {xs : List ValueId} {vs : List Val} {y : ValueId}
      (h : r.setMany xs vs = some r') (hy : y ∉ xs) : r' y = r y := by
    induction xs generalizing r vs with
    | nil => cases vs <;> simp_all [Regs.setMany]
    | cons x xs ih =>
      cases vs with
      | nil => simp [Regs.setMany] at h
      | cons v vs =>
        simp only [Regs.setMany_cons] at h
        rw [ih h (fun hm => hy (List.mem_cons_of_mem _ hm))]
        exact Regs.set_other r v (fun he => hy (he ▸ List.mem_cons_self))

theorem setMany_other {r r' : Regs} {xs : List ValueId} {vs : List Val} {y : ValueId}
    (h : r.setMany xs vs = some r') (hy : y ∉ xs) : r' y = r y :=
  setMany_has.setMany_other h hy

theorem setMany_agree {r r' : Regs} {xs : List ValueId} {vs : List Val} {n : Nat}
    (h : r.setMany xs vs = some r') (hx : ∀ x ∈ xs, n ≤ x) : Agree r r' n :=
  fun y hy => setMany_other h (fun hm => by have := hx y hm; omega)

/-! ## Single steps -/

section
variable {E : Env} {P : Program}

theorem step_inst1 {s : State} {st : Clif.Stmt} {rest : List Clif.Stmt} {vals : List Val}
    {mem' : Mem} {regs' : Regs} (hb : s.frame.body = st :: rest)
    (hc : ∀ fn args, st.inst ≠ .call fn args)
    (he : evalInst s.frame s.mem st.inst = .ok (vals, mem'))
    (hr : s.frame.regs.setMany st.results vals = some regs') :
    step E P s = .next { s with frame := { s.frame with regs := regs', body := rest }, mem := mem' } := by
  rw [step_inst E P s st rest hb hc, he]
  simp [continueWith, hr]

theorem step_jump {s : State} {bc : BlockCall} {fr' : Frame} (hb : s.frame.body = [])
    (ht : s.frame.term = .jump bc) (he : enterBlock s.frame bc = .ok fr') :
    step E P s = .next { s with frame := fr' } := by
  rw [step_term E P s hb, ht]; simp [stepTerm, he]

theorem step_brif {s : State} {c : ValueId} {t e : BlockCall} {cv : Val} {fr' : Frame}
    (hb : s.frame.body = []) (ht : s.frame.term = .brif c t e) (hc : s.frame.regs c = some cv)
    (he : enterBlock s.frame (if Sem.truthy cv.bits then t else e) = .ok fr') :
    step E P s = .next { s with frame := fr' } := by
  rw [step_term E P s hb, ht]; simp [stepTerm, Frame.get, hc, he]

end

theorem enterBlock_ok {fr : Frame} {bc : BlockCall} {b : Block} {vals : List Val} {regs' : Regs}
    (hb : fr.func.block? bc.block = some b) (hv : RegsHas fr.regs bc.args vals)
    (ht : vals.map (·.ty) = b.params.map (·.2))
    (hr : fr.regs.setMany (b.params.map (·.1)) vals = some regs') :
    enterBlock fr bc = .ok { fr with regs := regs', body := b.body, term := b.term } := by
  simp [enterBlock, hb, getMany_of_regsHas fr hv, checkTys, ht, hr]

end Compile.Proof
