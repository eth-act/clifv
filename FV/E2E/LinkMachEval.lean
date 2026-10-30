import FV.E2E.LinkArmProphThm

/-!
# A certified evaluator of the linked machine (SEM1 #537, witnesses)

The linked machine `LinkSys.mach` is noncomputable: `insnAt` and `linkedCall` choose classically.
So a concrete machine run cannot be evaluated, and the machine's own slot table
(`LinkSys.iniOf`) of a concrete run cannot be read off. Here:

* `insnAtC` (`insnAt` by search) and **`insnAt_eq_insnAtC`** (equal when the layout fits);
* `retOfB` (`RetOf` as a `Bool`, `retOf_iff`), `linkedCall_first` (`linkedCall` at the first
  return);
* `LinkSys.machC fuel M g`: a computable mirror of `mach M g` (callee runs searched for `fuel`
  steps), `LinkSys.okC`: a `Bool` check that the mirror's first `n` steps take the machine's
  path (no hooked instruction but a `bl` of a function of `P` whose run returns);
* **`LinkSys.runX_mach_eq`**: if `okC` holds, the machine's first `n` steps are the mirror's.

So facts about a concrete machine run reduce to `native_decide` on the mirror.
-/

namespace E2E

open Backend Backend.Proof

/-- `insnAt` by search. -/
def insnAtC (fa : FnAsm) (base pc : BitVec 64) : Option Insn :=
  (List.range fa.lines.toList.length).findSome? fun j => match fa.lines.toList[j]? with
    | some (Line.ins i _) =>
      if base + BitVec.ofNat 64 (lineOffset fa.lines.toList j) = pc then some i else none
    | _ => none

/-- **`insnAt` is computable by search** when the layout fits the address space. -/
theorem insnAt_eq_insnAtC {fa : FnAsm} {base pc : BitVec 64}
    (hsz : (fa.lines.toList.map Line.size).sum ≤ 2 ^ 64) : insnAt fa base pc = insnAtC fa base pc := by
  cases h : insnAtC fa base pc with
  | some i =>
    obtain ⟨j, -, hj⟩ := List.exists_of_findSome?_eq_some h
    split at hj
    · rename_i i' t hl
      split at hj
      · rename_i he
        cases hj
        rw [← he]
        exact insnAt_line hsz hl
      · cases hj
    · cases hj
  | none =>
    unfold insnAt
    split
    · rename_i hex
      exfalso
      obtain ⟨j, i, t, hl, he⟩ := hex
      have hjl : j < fa.lines.toList.length := by
        rcases Nat.lt_or_ge j fa.lines.toList.length with h1 | h1
        · exact h1
        · rw [List.getElem?_eq_none h1] at hl; cases hl
      have := List.findSome?_eq_none_iff.mp h j (List.mem_range.mpr hjl)
      rw [hl] at this
      simp only [he, ↓reduceIte] at this
      cases this
    · rfl

/-- Equality of loaded programs as a `Bool`. -/
def progEqB (p q : Arm.Program) : Bool := @BEq.beq (List (BitVec 64 × BitVec 32)) _ p q

theorem progEqB_iff {p q : Arm.Program} : progEqB p q = true ↔ p = q := by
  unfold progEqB; exact beq_iff_eq

/-- `RetOf` as a `Bool`. -/
def retOfB (a : Art) (s t : Arm.ArmState) : Bool :=
  Arm.r .PC t == Arm.r .PC s + 4 &&
    (match Arm.r .ERR t with | .None => true | _ => false) &&
    progEqB t.program (a.fb.program a.base) && spv t == spv s

theorem retOf_iff (a : Art) (s t : Arm.ArmState) : RetOf a s t ↔ retOfB a s t = true := by
  unfold RetOf retOfB
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    simp [h1, h2, progEqB_iff.mpr h3, h4]
  · intro h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨h1, ?_, progEqB_iff.mp h3, h4⟩
    split at h2
    · assumption
    · cases h2

/-- `runX` peeled at its last step. -/
theorem runX_succ_eval (f : Arm.ArmState → Arm.ArmState) (k : Nat) (s : Arm.ArmState) :
    runX f (k + 1) s = f (runX f k s) := by
  rw [runX_add f k 1]; rfl

/-- The first return of `h` called at `t` within `fuel` steps of the run `run`. -/
def firstRetC (run : Nat → Arm.ArmState) (h : Art) (t : Arm.ArmState) (fuel : Nat) : Option Nat :=
  (List.range fuel).find? fun k => retOfB h t (run k)

/-- `CallPc` as a `Bool`. -/
def callPcB (fa : FnAsm) (base pc : BitVec 64) : Bool :=
  (List.range fa.lines.toList.length).any fun j => match fa.lines.toList[j]? with
    | some (Line.ins (.bl _) _) | some (Line.ins (.blr _) _) =>
      decide (pc = base + BitVec.ofNat 64 (lineOffset fa.lines.toList j))
    | _ => false

theorem callPc_iff (fa : FnAsm) (base pc : BitVec 64) : CallPc fa base pc ↔ callPcB fa base pc = true := by
  unfold CallPc callPcB
  constructor
  · rintro ⟨j, i, t, hl, hi, he⟩
    have hjl : j < fa.lines.toList.length := by
      rcases Nat.lt_or_ge j fa.lines.toList.length with h1 | h1
      · exact h1
      · rw [List.getElem?_eq_none h1] at hl; cases hl
    refine List.any_eq_true.mpr ⟨j, List.mem_range.mpr hjl, ?_⟩
    rw [hl]
    rcases hi with ⟨n, rfl⟩ | ⟨r, rfl⟩ <;> simp [he]
  · intro h
    obtain ⟨j, -, hj⟩ := List.any_eq_true.mp h
    split at hj
    · rename_i n t hl
      exact ⟨j, _, t, hl, .inl ⟨n, rfl⟩, of_decide_eq_true hj⟩
    · rename_i r t hl
      exact ⟨j, _, t, hl, .inr ⟨r, rfl⟩, of_decide_eq_true hj⟩
    · cases hj

/-- **`callsBefore` by counting.** -/
theorem callsBefore_eq (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm) (base : BitVec 64)
    (s : Arm.ArmState) : ∀ i, callsBefore Mm fa base s i =
      ((List.range i).filter fun j => callPcB fa base (Arm.r .PC (runX Mm j s))).length
  | 0 => rfl
  | i + 1 => by
    rw [callsBefore, callsBefore_eq Mm fa base s i, List.range_succ, List.filter_append,
      List.length_append]
    by_cases h : CallPc fa base (Arm.r .PC (runX Mm i s))
    · simp [h, (callPc_iff _ _ _).mp h]
    · have : callPcB fa base (Arm.r .PC (runX Mm i s)) = false := by
        cases hb : callPcB fa base (Arm.r .PC (runX Mm i s))
        · rfl
        · exact absurd ((callPc_iff _ _ _).mpr hb) h
      simp [h, this]

/-- A function without `bl`/`blr` lines makes no call: `callsBefore` is `0`. -/
theorem callsBefore_noCalls {fa : FnAsm} (base : BitVec 64)
    (h : fa.lines.toList.all (fun l => match l with
      | Line.ins (.bl _) _ | Line.ins (.blr _) _ => false | _ => true) = true)
    (Mm : Arm.ArmState → Arm.ArmState) (s : Arm.ArmState) (i : Nat) :
    callsBefore Mm fa base s i = 0 := by
  rw [callsBefore_eq]
  simp only [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro j _ hc
  obtain ⟨k, -, hk⟩ := List.any_eq_true.mp hc
  split at hk
  · rename_i n t hl
    have := List.all_eq_true.mp h _ (List.mem_of_getElem? hl)
    simp at this
  · rename_i r t hl
    have := List.all_eq_true.mp h _ (List.mem_of_getElem? hl)
    simp at this
  · cases hk

namespace LinkSys

variable (L : LinkSys)

/-- One mirrored step of `g`'s machine, the program callees run by `callee`. -/
def stepWith (callee : Clif.Function → Arm.ArmState → Option Arm.ArmState) (g : Clif.Function)
    (t : Arm.ArmState) : Arm.ArmState :=
  match insnAtC (L.A g).fa (progBase t) (Arm.r .PC t) with
  | some (.bl n) => match L.P.func? n with
    | some h => (callee h t).getD t
    | none => t
  | some i => if i.hooked then t else Arm.stepi t
  | none => Arm.stepi t

/-- **The mirror of the linked machine** of depth `M` (callee runs searched for `fuel` steps). -/
def machC (fuel : Nat) : Nat → Clif.Function → Arm.ArmState → Arm.ArmState
  | 0 => L.stepWith fun _ _ => none
  | M + 1 => L.stepWith fun h t =>
      (firstRetC (fun k => runX (machC fuel M h) k (enterAt (L.A h) t)) (L.A h) t fuel).map
        fun N => Arm.set_program (runX (machC fuel M h) N (enterAt (L.A h) t)) t.program

/-- The mirrored step at `t` takes the machine's path, the program callees checked by `callee`. -/
def stepOk (callee : Clif.Function → Arm.ArmState → Bool) (g : Clif.Function) (t : Arm.ArmState) :
    Bool :=
  match insnAtC (L.A g).fa (progBase t) (Arm.r .PC t) with
  | some (.bl n) => match L.P.func? n with
    | some h => callee h t
    | none => false
  | some i => !i.hooked
  | none => true

/-- **The mirror's first `n` steps take the machine's path.** -/
def okC (fuel : Nat) : Nat → Clif.Function → Arm.ArmState → Nat → Bool
  | 0, g, s, n => (List.range n).all fun j => L.stepOk (fun _ _ => false) g (runX (L.machC fuel 0 g) j s)
  | M + 1, g, s, n => (List.range n).all fun j =>
      L.stepOk (fun h t =>
        match firstRetC (fun k => runX (L.machC fuel M h) k (enterAt (L.A h) t)) (L.A h) t fuel with
        | some N => okC fuel M h (enterAt (L.A h) t) N
        | none => false) g (runX (L.machC fuel (M + 1) g) j s)

theorem firstRetC_spec {run : Nat → Arm.ArmState} {h : Art} {t : Arm.ArmState} {fuel N : Nat}
    (hf : firstRetC run h t fuel = some N) :
    retOfB h t (run N) = true ∧ ∀ k < N, retOfB h t (run k) = false := by
  unfold firstRetC at hf
  obtain ⟨h1, h2⟩ := List.find?_eq_some_iff_append.mp hf
  refine ⟨h1, fun k hk => ?_⟩
  obtain ⟨as, bs, he, hb⟩ := h2
  have hrange : List.range fuel = List.range N ++ (N :: bs) := by
    rw [he]
    congr 1
    have hl := congrArg List.length he
    simp only [List.length_range, List.length_append, List.length_cons] at hl
    have hpre : as = (List.range fuel).take as.length := by rw [he]; simp
    rw [hpre, List.take_range]
    have hNi : (List.range fuel)[as.length]? = some N := by
      rw [he]; simp
    rw [List.getElem?_range (by omega)] at hNi
    cases hNi
    congr 1
    omega
  have hk' : k ∈ List.range N := List.mem_range.mpr hk
  have := hb k (by
    rw [he] at hrange
    have := List.append_inj_left' (hrange.symm.trans rfl) (by simp)
    exact this ▸ hk')
  simpa using this

/-- **The machine's first steps are the mirror's** (module doc). -/
theorem runX_mach_eq (fuel : Nat)
    (hsz : ∀ g ∈ L.P.funcs, ((L.A g).fa.lines.toList.map Line.size).sum ≤ 2 ^ 64) :
    ∀ (M : Nat) (g : Clif.Function) (s : Arm.ArmState) (n : Nat), g ∈ L.P.funcs →
      L.okC fuel M g s n = true → ∀ j ≤ n, runX (L.mach M g) j s = runX (L.machC fuel M g) j s := by
  intro M
  induction M with
  | zero =>
    intro g s n hg hok j hj
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [runX_succ_eval, runX_succ_eval, ih (by omega)]
      have hs := List.all_eq_true.mp hok j (List.mem_range.mpr (by omega))
      generalize runX (L.machC fuel 0 g) j s = t at hs ⊢
      simp only [mach, ArmStepX, machC, stepWith, stepOk] at hs ⊢
      rw [insnAt_eq_insnAtC (hsz g hg)]
      split at hs
      · rename_i n heq
        rw [heq]
        split at hs <;> cases hs
      · rename_i i hi heq
        rw [heq]
        simp only [Bool.not_eq_true'] at hs
        simp only [hs, Bool.false_eq_true, ↓reduceIte]
        cases i <;> simp_all [Insn.hooked]
      · rename_i heq
        rw [heq]
  | succ M ihM =>
    intro g s n hg hok j hj
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [runX_succ_eval, runX_succ_eval, ih (by omega)]
      have hs := List.all_eq_true.mp hok j (List.mem_range.mpr (by omega))
      generalize runX (L.machC fuel (M + 1) g) j s = t at hs ⊢
      simp only [mach, ArmStepX, machC, stepWith, stepOk] at hs ⊢
      rw [insnAt_eq_insnAtC (hsz g hg)]
      split at hs
      · rename_i nm heq
        rw [heq]
        split at hs
        · rename_i h hpf

          split at hs
          · rename_i N hN
            have hh : h ∈ L.P.funcs := (Clif.Program.func?_some hpf).1
            have heqs := ihM h (enterAt (L.A h) t) N hh hs
            obtain ⟨hr, hmin⟩ := firstRetC_spec hN
            simp only [hooks, callHook, hpf, hN, Option.map_some, Option.getD_some]
            have hR : RetOf (L.A h) t (runX (L.mach M h) N (enterAt (L.A h) t)) := by
              rw [heqs N (Nat.le_refl _), retOf_iff]; exact hr
            have hM : ∀ k < N, ¬ RetOf (L.A h) t (runX (L.mach M h) k (enterAt (L.A h) t)) := by
              intro k hk hR'
              rw [heqs k (by omega), retOf_iff, hmin k hk] at hR'
              cases hR'
            exact (linkedCall_first hR hM).trans (by rw [heqs N (Nat.le_refl _)])
          · cases hs
        · cases hs
      · rename_i i hi heq
        rw [heq]
        simp only [Bool.not_eq_true'] at hs
        simp only [hs, Bool.false_eq_true, ↓reduceIte]
        cases i <;> simp_all [Insn.hooked]
      · rename_i heq
        rw [heq]

end LinkSys

end E2E
