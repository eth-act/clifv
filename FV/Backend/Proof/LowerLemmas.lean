import FV.Backend.Proof.LowerShape

/-!
# Auxiliary facts for the driver simulation

Register-file updates on both sides (`Clif.Regs.setMany`, `getMany`; VCode `parCopyEnv`,
`writeV`), segment positions inside a block, the successor function of `VCode.cfg`, and small
facts about renamed instructions.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

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

/-- Parameters bound by `setMany` to values of their declared types hold values of those
types. -/
theorem setMany_param_ty {r r' : Clif.Regs} {ps : List (Clif.ValueId × Clif.Ty)}
    {vs : List Clif.Val} (hset : r.setMany (ps.map (·.1)) vs = some r')
    (hnd : (ps.map (·.1)).Nodup) (hty : vs.map (·.ty) = ps.map (·.2)) {x : Clif.ValueId}
    (hx : x ∈ ps.map (·.1)) {v : Clif.Val} (hv : r' x = some v) :
    ∃ q ∈ ps, q.1 = x ∧ v.ty = q.2 := by
  obtain ⟨m, v', hxm, hvm, hrv⟩ := setMany_mem hset hnd x hx
  rw [hrv] at hv
  cases hv
  have hm : m < ps.length := by
    have := (List.getElem?_eq_some_iff.mp hxm).1
    simpa using this
  refine ⟨ps[m], List.getElem_mem hm, ?_, ?_⟩
  · simpa [List.getElem?_map, List.getElem?_eq_getElem hm] using hxm
  · have h2 := congrArg (·[m]?) hty
    simpa [List.getElem?_map, hvm, List.getElem?_eq_getElem hm] using h2

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

theorem lookup_zip_nodup {β : Type} :
    ∀ {ps : List Nat} {xs : List β}, ps.Nodup → ps.length = xs.length →
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

theorem lookup_zip_not_mem {β : Type} {v : Nat} :
    ∀ {ps : List Nat} {xs : List β}, v ∉ ps → (ps.zip xs).lookup v = none := by
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

theorem instOutcome_of_pure {env : Clif.Env} {p : Clif.Program} {fr : Clif.Frame} {cm : Clif.Mem}
    {i : Clif.Inst} (h : pureInst i = true) : instOutcome env p fr cm i = Clif.evalInst fr cm i := by
  cases i <;> simp [pureInst] at h <;> rfl

theorem drop_cons_split {α : Type} {l : List α} {j : Nat} {a : α} {rest : List α}
    (h : l.drop j = a :: rest) : j < l.length ∧ l[j]? = some a ∧ rest = l.drop (j + 1) := by
  have hj : j < l.length := by
    rcases Nat.lt_or_ge j l.length with hj | hj
    · exact hj
    · rw [List.drop_eq_nil_of_le hj] at h; cases h
  rw [List.drop_eq_getElem_cons hj] at h
  simp only [List.cons.injEq] at h
  exact ⟨hj, by rw [List.getElem?_eq_getElem hj, h.1], h.2.symm⟩

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

/-! ## CLIF control flow -/

theorem getMany_ne_trap {fr : Clif.Frame} :
    ∀ {xs : List Clif.ValueId} {c : Clif.TrapCode}, fr.getMany xs ≠ .trap c := by
  intro xs
  induction xs with
  | nil => intro c h; cases h
  | cons x xs ih =>
    intro c h
    simp only [Clif.Frame.getMany, Clif.Frame.get] at h
    cases hx : fr.regs x with
    | none => rw [hx] at h; cases h
    | some v =>
      rw [hx] at h
      simp only [Clif.Res.ofOption_some, Clif.Res.ok_bind] at h
      cases hr : fr.getMany xs with
      | ok vs => rw [hr] at h; cases h
      | trap c' => exact ih hr
      | stuck => rw [hr] at h; cases h

theorem checkTys_cases (what : String) (vs : List Clif.Val) (tys : List Clif.Ty) :
    Clif.checkTys what vs tys = .ok () ∧ vs.map (·.ty) = tys ∨ ∃ m, Clif.checkTys what vs tys = .stuck m := by
  unfold Clif.checkTys Clif.Res.check
  split
  · rename_i h; exact .inl ⟨rfl, by simpa using h⟩
  · exact .inr ⟨_, rfl⟩

theorem enterBlock_spec {fr fr2 : Clif.Frame} {bc : Clif.BlockCall}
    (h : Clif.enterBlock fr bc = .ok fr2) :
    ∃ TB args regs, fr.func.block? bc.block = some TB ∧ fr.getMany bc.args = .ok args ∧
      args.map (·.ty) = TB.params.map (·.2) ∧
      fr.regs.setMany (TB.params.map (·.1)) args = some regs ∧
      fr2 = { fr with regs, body := TB.body, term := TB.term } := by
  unfold Clif.enterBlock at h
  cases hb : fr.func.block? bc.block with
  | none => rw [hb] at h; cases h
  | some TB =>
    rw [hb] at h
    simp only [Clif.Res.ofOption_some, Clif.Res.ok_bind] at h
    cases ha : fr.getMany bc.args with
    | trap => rw [ha] at h; cases h
    | stuck => rw [ha] at h; cases h
    | ok args =>
      rw [ha] at h
      simp only [Clif.Res.ok_bind] at h
      rcases checkTys_cases s!"arguments of block{bc.block}" args (TB.params.map (·.2)) with
        ⟨hc, hty⟩ | ⟨m, hc⟩
      · rw [hc] at h
        simp only [Clif.Res.ok_bind] at h
        cases hs : fr.regs.setMany (TB.params.map (·.1)) args with
        | none => rw [hs] at h; cases h
        | some regs =>
          rw [hs] at h
          simp only [Clif.Res.ofOption_some, Clif.Res.ok_bind, Clif.Res.pure_eq, Clif.Res.ok.injEq] at h
          exact ⟨TB, args, regs, rfl, rfl, hty, hs, h.symm⟩
      · rw [hc] at h; cases h

theorem enterBlock_ne_trap {fr : Clif.Frame} {bc : Clif.BlockCall} {c : Clif.TrapCode} :
    Clif.enterBlock fr bc ≠ .trap c := by
  intro h
  unfold Clif.enterBlock at h
  cases hb : fr.func.block? bc.block with
  | none => rw [hb] at h; cases h
  | some TB =>
    rw [hb] at h
    simp only [Clif.Res.ofOption_some, Clif.Res.ok_bind] at h
    cases ha : fr.getMany bc.args with
    | trap c' => exact getMany_ne_trap ha
    | stuck => rw [ha] at h; cases h
    | ok args =>
      rw [ha] at h
      simp only [Clif.Res.ok_bind] at h
      rcases checkTys_cases s!"arguments of block{bc.block}" args (TB.params.map (·.2)) with
        ⟨hc, -⟩ | ⟨m, hc⟩
      · rw [hc] at h
        simp only [Clif.Res.ok_bind] at h
        cases hs : fr.regs.setMany (TB.params.map (·.1)) args with
        | none => rw [hs] at h; cases h
        | some regs => rw [hs] at h; cases h
      · rw [hc] at h; cases h

theorem find?_of_findIdx? {α : Type} {P : α → Bool} :
    ∀ {l : List α} {i : Nat} {a : α}, l.findIdx? P = some i → l.find? P = some a → l[i]? = some a := by
  intro l
  induction l with
  | nil => intro i a h; simp at h
  | cons x l ih =>
    intro i a hi ha
    rw [List.findIdx?_cons] at hi
    rw [List.find?_cons] at ha
    cases hp : P x with
    | true =>
      simp only [hp, ite_true, Option.some.injEq] at hi ha
      subst hi ha; rfl
    | false =>
      simp only [hp, Bool.false_eq_true, ite_false] at hi ha
      cases hj : l.findIdx? P with
      | none => rw [hj] at hi; cases hi
      | some j =>
        rw [hj] at hi
        simp only [Option.map_some, Option.some.injEq] at hi
        subst hi
        simpa using ih hj ha

theorem blockIdx_block {f : Clif.Function} {b tl : Nat} {TB : Clif.Block}
    (h : blockIdx? f b = some tl) (hb : f.block? b = some TB) : f.blocks[tl]? = some TB :=
  find?_of_findIdx? h hb

theorem seqRun_stop_mem {V W : Type} {sem : ISem V W} :
    ∀ {ms : List MInst} {ρ : Nat → V} {w : W} {k : Nat} {i : MInst} {ops : Array Operand}
      {ρ₁ : Nat → V} {w₁ : W} {outs : List V} {w₂ : W} {ctl : Ctl},
    seqRun sem ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ ctl) →
    ms[k]? = some i ∧ i.operands = .ok ops := by
  intro ms
  induction ms with
  | nil => intro _ _ _ _ _ _ _ _ _ _ h; simp [seqRun] at h
  | cons i₀ ms ih =>
    intro ρ w k i ops ρ₁ w₁ outs w₂ ctl h
    rcases seqRun_cons_stop h with
      ⟨rfl, rfl, hops, -⟩ | ⟨k', _, _, _, rfl, _, _, _, hrest⟩
    · exact ⟨rfl, hops⟩
    · simpa using ih hrest

theorem vregNum_mapM (ns : List Nat) :
    (ns.map (fun n => Reg.vreg n .int)).mapM vregNum = .ok ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp [List.mapM_cons, vregNum, ih] <;> rfl

/-! ## The entry `Args` -/

/-- `(vreg n, p)` pairs of an `Args`. -/
def argPairs (ns : List (Nat × Reg)) : List (Reg × Reg) := ns.map fun q => (Reg.vreg q.1 .int, q.2)

/-- The operands of `Args (argPairs ns)`: fixed late defs. -/
def argOps (ns : List (Nat × Reg)) : List Operand :=
  ns.map fun q => (⟨q.1, .int, .def, .late, .fixed q.2⟩ : Operand)

theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f : Except ε β) = f a := rfl

theorem except_pure {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

theorem mapM_fixedDef (ns : List (Nat × Reg)) : ∀ (s : Array Operand),
    ((argPairs ns).mapM
      (fun (x : Reg × Reg) => do let r ← collectOp (OpSpec.fixedDef x.2) x.1; pure (r, x.2))).run s =
      .ok (argPairs ns, s ++ (argOps ns).toArray) := by
  induction ns with
  | nil => intro s; simp [argPairs, argOps] <;> rfl
  | cons q ns ih =>
    intro s
    simp only [argPairs, argOps, List.map_cons, List.mapM_cons, StateT.run_bind] at ih ⊢
    have h1 : (collectOp (OpSpec.fixedDef q.2) (Reg.vreg q.1 .int)).run s =
        .ok (Reg.vreg q.1 .int, s.push ⟨q.1, .int, .def, .late, .fixed q.2⟩) := rfl
    rw [h1, except_ok_bind, StateT.run_pure, except_pure, except_ok_bind, ih, except_ok_bind,
      StateT.run_pure, except_pure]
    simp

theorem operands_args (ns : List (Nat × Reg)) :
    (MInst.args (argPairs ns)).operands = .ok (argOps ns).toArray := by
  rw [operands_eq]
  simp only [MInst.visitOperands, StateT.run_bind, mapM_fixedDef]
  simp [bind, Except.bind, StateT.run, pure, StateT.pure, Except.pure]

end Backend.Proof.Driver
