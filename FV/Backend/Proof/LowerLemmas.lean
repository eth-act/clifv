import FV.Backend.Proof.LowerShape

/-!
# Auxiliary facts for the driver simulation

Register-file updates on both sides (`Clif.Regs.setMany`, `getMany`; VCode `parCopyEnv`,
`writeV`), segment positions inside a block, the successor function of `VCode.cfg`, and small
facts about renamed instructions.
-/

namespace Backend.Proof.Driver

open Backend

/-! ## CLIF register files -/

theorem setMany_length {r r' : Clif.Regs} :
    ∀ {xs : List Clif.ValueId} {vs : List Clif.Val}, r.setMany xs vs = some r' →
      xs.length = vs.length := by
  intro xs
  induction xs generalizing r with
  | nil => intro vs h; cases vs <;> simp [Clif.Regs.setMany] at h ⊢
  | cons x xs ih =>
    intro vs h
    cases vs with
    | nil => simp [Clif.Regs.setMany] at h
    | cons v vs => simp only [Clif.Regs.setMany_cons] at h; simp [ih h]

theorem setMany_other {r r' : Clif.Regs} {y : Clif.ValueId} :
    ∀ {xs : List Clif.ValueId} {vs : List Clif.Val}, r.setMany xs vs = some r' → y ∉ xs →
      r' y = r y := by
  intro xs
  induction xs generalizing r with
  | nil => intro vs h _; cases vs <;> simp [Clif.Regs.setMany] at h; rw [h]
  | cons x xs ih =>
    intro vs h hy
    cases vs with
    | nil => simp [Clif.Regs.setMany] at h
    | cons v vs =>
      simp only [Clif.Regs.setMany_cons] at h
      rw [ih h (fun e => hy (List.mem_cons_of_mem _ e))]
      exact Clif.Regs.set_other _ _ (fun e => hy (e ▸ List.mem_cons_self))

theorem setMany_nodup {r r' : Clif.Regs} :
    ∀ {xs : List Clif.ValueId} {vs : List Clif.Val}, r.setMany xs vs = some r' → xs.Nodup →
      ∀ (m : Nat) x v, xs[m]? = some x → vs[m]? = some v → r' x = some v := by
  intro xs
  induction xs generalizing r with
  | nil => intro _ _ _ m x v hx; simp at hx
  | cons x₀ xs ih =>
    intro vs h hnd m x v hx hv
    cases vs with
    | nil => simp [Clif.Regs.setMany] at h
    | cons v₀ vs =>
      simp only [Clif.Regs.setMany_cons] at h
      have hnd' := List.nodup_cons.mp hnd
      cases m with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hv
        subst hx hv
        rw [setMany_other h hnd'.1]
        simp
      | succ m =>
        simp only [List.getElem?_cons_succ] at hx hv
        exact ih h hnd'.2 m x v hx hv

theorem setMany_mem {r r' : Clif.Regs} :
    ∀ {xs : List Clif.ValueId} {vs : List Clif.Val}, r.setMany xs vs = some r' → xs.Nodup →
      ∀ x ∈ xs, ∃ (m : Nat) (v : Clif.Val), xs[m]? = some x ∧ vs[m]? = some v ∧ r' x = some v := by
  intro xs vs h hnd x hx
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hx
  have hl := setMany_length h
  refine ⟨m, vs[m]'(by omega), by simp [hm], by simp, ?_⟩
  exact setMany_nodup h hnd m _ _ (by simp [hm]) (by simp)

theorem getMany_spec {fr : Clif.Frame} :
    ∀ {xs : List Clif.ValueId} {vals : List Clif.Val}, fr.getMany xs = .ok vals →
      xs.length = vals.length ∧
      ∀ (m : Nat) x, xs[m]? = some x → ∃ v, fr.regs x = some v ∧ vals[m]? = some v := by
  intro xs
  induction xs with
  | nil => intro vals h; simp [Clif.Frame.getMany] at h; subst h; simp
  | cons x xs ih =>
    intro vals h
    simp only [Clif.Frame.getMany, Clif.Frame.get] at h
    cases hx : fr.regs x with
    | none => rw [hx] at h; simp [Clif.Res.ofOption] at h
    | some v =>
      rw [hx] at h
      simp only [Clif.Res.ofOption_some, Clif.Res.ok_bind] at h
      cases hr : fr.getMany xs with
      | ok vs =>
        rw [hr] at h
        simp only [Clif.Res.ok_bind, Clif.Res.pure_eq, Clif.Res.ok.injEq] at h
        subst h
        obtain ⟨hl, hm⟩ := ih hr
        refine ⟨by simp [hl], fun m y hy => ?_⟩
        cases m with
        | zero => simp at hy; subst hy; exact ⟨v, hx, rfl⟩
        | succ m => simpa using hm m y (by simpa using hy)
      | trap => rw [hr] at h; cases h
      | stuck => rw [hr] at h; cases h

/-! ## VCode register files -/

section
variable {V : Type}

theorem lookup_zip_nodup :
    ∀ {ps xs : List Nat}, ps.Nodup → ps.length = xs.length →
      ∀ (m : Nat) p x, ps[m]? = some p → xs[m]? = some x → (ps.zip xs).lookup p = some x := by
  intro ps
  induction ps with
  | nil => intro _ _ _ m p x hp; simp at hp
  | cons p₀ ps ih =>
    intro xs hnd hl m p x hp hx
    cases xs with
    | nil => simp at hl
    | cons x₀ xs =>
      have hnd' := List.nodup_cons.mp hnd
      cases m with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hp hx
        subst hp hx
        simp
      | succ m =>
        simp only [List.getElem?_cons_succ] at hp hx
        have hne : p ≠ p₀ := fun e => hnd'.1 (e ▸ List.mem_of_getElem? hp)
        simp only [List.zip_cons_cons, List.lookup, beq_false_of_ne hne]
        exact ih hnd'.2 (by simpa using hl) m p x hp hx

theorem lookup_zip_not_mem {v : Nat} :
    ∀ {ps xs : List Nat}, v ∉ ps → (ps.zip xs).lookup v = none := by
  intro ps
  induction ps with
  | nil => intro xs _; simp
  | cons p ps ih =>
    intro xs hv
    cases xs with
    | nil => simp
    | cons x xs =>
      have hne : v ≠ p := fun e => hv (e ▸ List.mem_cons_self)
      simp only [List.zip_cons_cons, List.lookup, beq_false_of_ne hne]
      exact ih (fun e => hv (List.mem_cons_of_mem _ e))

theorem parCopyEnv_param {ρ : Nat → V} {ps xs : List Nat} (hnd : ps.Nodup)
    (hl : ps.length = xs.length) (m : Nat) {p x : Nat} (hp : ps[m]? = some p)
    (hx : xs[m]? = some x) : parCopyEnv ρ ps xs p = ρ x := by
  simp only [parCopyEnv, lookup_zip_nodup hnd hl m p x hp hx]

theorem parCopyEnv_other {ρ : Nat → V} {ps xs : List Nat} {v : Nat} (hv : v ∉ ps) :
    parCopyEnv ρ ps xs v = ρ v := by
  simp only [parCopyEnv, lookup_zip_not_mem hv]

end

/-! ## Positions of segments in a block -/

theorem segAt_of_toList {vb : VBlock} {L₁ ms L₂ : List MInst}
    (h : vb.insts.toList = L₁ ++ ms ++ L₂) : SegAt vb L₁.length ms := by
  intro k hk
  rw [← Array.getElem?_toList, h]
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hk, List.getElem?_eq_getElem hk]

theorem flatten_range_split (g : Nat → List MInst) {j n : Nat} (hj : j < n) :
    ((List.range n).map g).flatten =
      ((List.range j).map g).flatten ++ g j ++ (((List.range (n - (j + 1))).map fun i => g (j + 1 + i))).flatten := by
  obtain ⟨m, rfl⟩ : ∃ m, n = j + (1 + m) := ⟨n - (j + 1), by omega⟩
  rw [List.range_add, List.range_add, show j + (1 + m) - (j + 1) = m by omega]
  simp [List.map_append, List.flatten_append, List.map_map, Function.comp_def, Nat.add_assoc]

theorem length_flatten_range (g : Nat → List MInst) (j : Nat) :
    ((List.range j).map g).flatten.length = ((List.range j).map fun i => (g i).length).sum := by
  simp [List.length_flatten, List.map_map, Function.comp_def]

/-! ## Renamed instructions -/

theorem trapCode?_mapRegs (g : Reg → Reg) (i : MInst) : trapCode? (i.mapRegs g) = trapCode? i := by
  cases i <;> rfl

theorem targets_mapRegs (g : Reg → Reg) (i : MInst) : (i.mapRegs g).targets = i.targets := by
  cases i <;> rfl

/-! ## `VCode.cfg` successors -/

theorem list_mapM_ok {α β : Type} {f : α → Except String β} :
    ∀ {l : List α} {bs : List β}, l.mapM f = .ok bs →
      bs.length = l.length ∧ ∀ (i : Nat) a, l[i]? = some a → ∃ b, f a = .ok b ∧ bs[i]? = some b := by
  intro l
  induction l with
  | nil => intro bs h; simp [List.mapM_nil] at h; cases h; simp
  | cons a l ih =>
    intro bs h
    simp only [List.mapM_cons] at h
    cases ha : f a with
    | error e => rw [ha] at h; cases h
    | ok b =>
      rw [ha] at h
      cases hl : l.mapM f with
      | error e => rw [hl] at h; cases h
      | ok bs' =>
        rw [hl] at h
        cases h
        obtain ⟨h1, h2⟩ := ih hl
        refine ⟨by simp [h1], fun i a' hi => ?_⟩
        cases i with
        | zero => simp at hi; subst hi; exact ⟨b, ha, rfl⟩
        | succ i => simpa using h2 i a' (by simpa using hi)

theorem array_mapM_ok {α β : Type} {f : α → Except String β} {as : Array α} {bs : Array β}
    (h : as.mapM f = .ok bs) :
    bs.size = as.size ∧ ∀ (i : Nat) a, as[i]? = some a → ∃ b, f a = .ok b ∧ bs[i]? = some b := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : as.toList.mapM f with
  | error e => rw [hl] at h; cases h
  | ok l =>
    rw [hl] at h
    cases h
    obtain ⟨h1, h2⟩ := list_mapM_ok hl
    refine ⟨by simp [h1], fun i a hi => ?_⟩
    obtain ⟨b, hb, hbi⟩ := h2 i a (by simpa using hi)
    exact ⟨b, hb, by simpa using hbi⟩

/-- With labels = block indices, `VCode.cfg`'s successors of a block are the targets of its last
instruction. -/
theorem succOf_eq {vc : VCode} (hlab : ∀ l (vb : VBlock), vc.blocks[l]? = some vb → vb.label = l)
    {ss ps : Array (Array Nat)} (hcfg : vc.cfg = .ok (ss, ps)) {b : Nat} {vb : VBlock} {t : MInst}
    (hvb : vc.blocks[b]? = some vb) (ht : vb.insts.back? = some t) (j : Nat) :
    succOf vc b j = t.targets[j]? := by
  unfold succOf
  rw [hcfg]
  unfold VCode.cfg at hcfg
  simp only [bind, Except.bind] at hcfg
  split at hcfg
  · cases hcfg
  · rename_i succs hm
    split at hcfg
    · cases hcfg
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hcfg
      obtain ⟨rfl, -⟩ := hcfg
      obtain ⟨-, hs⟩ := array_mapM_ok hm
      obtain ⟨r, hr, hsb⟩ := hs b vb hvb
      simp only [hsb, ht, Option.bind_some] at hr ⊢
      split at hr
      · simp [throw, throwThe, MonadExceptOf.throw] at hr
      · obtain ⟨hl, hri⟩ := array_mapM_ok hr
        cases htj : t.targets[j]? with
        | none =>
          have : t.targets.length ≤ j := List.getElem?_eq_none_iff.mp htj
          simp only [List.size_toArray] at hl
          simp; omega
        | some l =>
          obtain ⟨i, hi, hri'⟩ := hri j l (by simpa using htj)
          rw [hri']
          split at hi
          · rename_i i' hfi
            simp only [pure, Except.pure, Except.ok.injEq] at hi
            subst hi
            obtain ⟨hlt, hlab', -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hfi
            have := hlab i' _ (Array.getElem?_eq_getElem hlt)
            simp only [beq_iff_eq] at hlab'
            rw [← hlab', this]
          · cases hi

end Backend.Proof.Driver
