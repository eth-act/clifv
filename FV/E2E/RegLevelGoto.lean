import FV.E2E.RegLevelBranch

/-!
# Block-ending branches on the machine (M6)

`jump`/`condBr`/`testBitAndBranch` at the end of a block: their lines, after `fallthrough`
(`ft_b`: a `b` to the next line's label is dropped; `ft_cb`: `b.c T; b E; T:` becomes
`b.!c E; T:`), take the machine to the label of the successor the VCode semantics picks
(`reach_b`, `reach_cb`), where `q_entry` relates it to the successor's items.
-/

namespace Backend.Proof

open Backend E2E


theorem list_mapM_ok {ε α β : Type} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → l'.length = l.length ∧
      ∀ (i : Nat) x, l[i]? = some x → ∃ y, f x = .ok y ∧ l'[i]? = some y
  | [], l', h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i y hy
    split at h
    · cases h
    rename_i ys hys
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hl, hi⟩ := list_mapM_ok hys
    refine ⟨by simp [hl], fun i x hx => ?_⟩
    cases i with
    | zero => simp at hx; subst hx; exact ⟨y, hy, rfl⟩
    | succ i =>
      simp at hx
      obtain ⟨y', h1, h2⟩ := hi i x hx
      exact ⟨y', h1, by simpa using h2⟩

theorem array_mapM_ok {ε α β : Type} {f : α → Except ε β} {as : Array α} {bs : Array β}
    (h : as.mapM f = .ok bs) : bs.size = as.size ∧
      ∀ (i : Nat) x, as[i]? = some x → ∃ y, f x = .ok y ∧ bs[i]? = some y := by
  have e := Array.toList_mapM (xs := as) (f := f)
  rw [h] at e
  simp only [Functor.map, Except.map] at e
  obtain ⟨hl, hi⟩ := list_mapM_ok e.symm
  refine ⟨by simpa using hl, fun i x hx => ?_⟩
  obtain ⟨y, h1, h2⟩ := hi i x (by simpa using hx)
  exact ⟨y, h1, by rw [← Array.getElem?_toList]; exact h2⟩

theorem cfg_block {vc : VCode} {ss ps : Array (Array Nat)} (h : vc.cfg = .ok (ss, ps)) {b : Nat}
    {vb : VBlock} (hvb : vc.blocks[b]? = some vb) :
    ∃ t ts, vb.insts.back? = some t ∧ ss[b]? = some ts ∧
      ∀ (j s : Nat), ts[j]? = some s → ∃ vs : VBlock, vc.blocks[s]? = some vs ∧
        t.targets[j]? = some vs.label := by
  unfold VCode.cfg at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i succs hsuccs
  have hss : ss = succs := by
    split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm
  subst hss
  obtain ⟨-, hel⟩ := array_mapM_ok hsuccs
  obtain ⟨ts, hts, hb⟩ := hel b vb hvb
  split at hts
  · rename_i t ht
    have hts' : ∃ F : Label → Except String Nat, t.targets.toArray.mapM F = .ok ts ∧
        ∀ l y, F l = .ok y → ∃ vs : VBlock, vc.blocks[y]? = some vs ∧ l = vs.label := by
      split at hts
      · simp [throw, throwThe, MonadExceptOf.throw] at hts
      · refine ⟨_, hts, fun l y hy => ?_⟩
        split at hy
        · rename_i i hi
          simp only [pure, Except.pure, Except.ok.injEq] at hy
          subst hy
          obtain ⟨hlt, heq, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hi
          exact ⟨_, Array.getElem?_eq_getElem hlt, by simp at heq; exact heq.symm⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at hy
    obtain ⟨F, hF, hFl⟩ := hts'
    obtain ⟨hsz, hel'⟩ := array_mapM_ok hF
    refine ⟨t, ts, ht, hb, fun j s hs => ?_⟩
    have hj : j < ts.size := (Array.getElem?_eq_some_iff.mp hs).1
    obtain ⟨l, hl⟩ : ∃ l, t.targets.toArray[j]? = some l :=
      ⟨_, Array.getElem?_eq_getElem (by rw [← hsz]; exact hj)⟩
    obtain ⟨y, hy, hy'⟩ := hel' j l hl
    rw [hs] at hy'
    cases hy'
    obtain ⟨vs, hvs, rfl⟩ := hFl l s hy
    exact ⟨vs, hvs, by simpa using hl⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at hts

theorem condHolds_invert (c : Cond) (hal : c ≠ .al) (hnv : c ≠ .nv) (s : Arm.ArmState) :
    Arm.ConditionHolds c.invert.bits s = !Arm.ConditionHolds c.bits s := by
  cases c <;> simp_all [Arm.ConditionHolds, Cond.invert, Cond.bits, Arm.BitVec.lsb] <;> decide

theorem ft_label (l : Lbl) (Z : List Line) : ftList (.label l :: Z) = .label l :: ftList Z := by
  rw [ftList_cons]
  simp [ftStep]

theorem ft_b (x : Lbl) (Z : List Line) :
    (∃ Z', Z = .label x :: Z' ∧ ftList (.ins (.b x) none :: Z) = ftList Z) ∨
      ftList (.ins (.b x) none :: Z) = .ins (.b x) none :: ftList Z := by
  rw [ftList_cons]
  unfold ftStep
  cases Z with
  | nil => right; simp
  | cons z Z =>
    cases z with
    | label l =>
      by_cases h : x = l
      · subst h; left; cases Z <;> simp [Insn.condTarget?]
      · right; cases Z <;> simp [Insn.condTarget?, h]
    | ins i t =>
      right
      cases Z with
      | nil => simp
      | cons z2 Z =>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ]
        split
        · rename_i c0 c e l heq1 heq2
          simp only [Line.ins.injEq] at l
          obtain ⟨rfl, -⟩ := l
          simp [Insn.condTarget?]
        · simp
    | word a b => right; cases Z <;> simp
theorem ft_cb (bc : Insn) (e : Lbl) (Z : List Line) (hnb : ∀ x, bc ≠ .b x) :
    (∃ L Z', Z = .label L :: Z' ∧ bc.condTarget? = some L ∧
      ftList (.ins bc none :: .ins (.b e) none :: Z) = .ins (bc.invertTo e) none :: ftList Z) ∨
    ftList (.ins bc none :: .ins (.b e) none :: Z) = .ins bc none :: ftList (.ins (.b e) none :: Z) := by
  rw [ftList_cons]
  unfold ftStep
  have hd : ∀ n1 : Option Line, (match Line.ins bc none, n1 with
      | .ins (.b x) none, some (.label l) => if x == l then (([] : List Line), 1) else ([Line.ins bc none], 1)
      | _, _ => ([Line.ins bc none], 1)) = ([Line.ins bc none], 1) := by
    intro n1
    split
    · rename_i _ _ l _ h2
      simp only [Line.ins.injEq] at h2
      exact absurd h2.1 (hnb l)
    · rfl
  cases Z with
  | nil => right; simp [hd]
  | cons z Z =>
    cases z with
    | label L =>
      by_cases h : bc.condTarget? = some L
      · left; exact ⟨L, Z, rfl, h, by simp [h]⟩
      · right; simp [h, hd]
    | _ => right; simp [hd]

theorem brCond_b {env : Env} {l : Lbl} {a : Arm.ArmInst} (h : (Insn.b l).toArmInst env = .ok a)
    (s : Arm.ArmState) : brCond a s = true := by
  simp only [Insn.toArmInst, Backend.map_eq_ok] at h
  obtain ⟨b, hb, rfl⟩ := h
  simp only [Insn.armFields, Backend.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at hb
  obtain ⟨v, hv, rfl⟩ := hb
  rfl

theorem drop_get {L T : List Line} {j : Nat} {ln : Line} {Z : List Line}
    (h : L.drop j = ln :: Z ++ T) : L[j]? = some ln := by
  have := congrArg (·[0]?) h
  simpa [List.getElem?_drop] using this

theorem drop_succ {L T : List Line} {j : Nat} {ln : Line} {Z : List Line}
    (h : L.drop j = ln :: Z ++ T) : L.drop (j + 1) = Z ++ T := by
  rw [← List.drop_drop, h]; rfl

/-- **`b x` after `fallthrough`**: the machine reaches a line defining `x` (0 steps when the
branch was dropped, 1 otherwise), changing only the pc. -/
theorem reach_b {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j0 : Nat} {x : Lbl} {Z T : List Line}
    (hdrop : R.L.drop j0 = ftList (.ins (.b x) none :: Z) ++ T)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) :
    ∃ n jl, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧ R.L[jl]? = some (.label x) := by
  rcases ft_b x Z with ⟨Z', rfl, he⟩ | he
  · rw [he, ft_label] at hdrop
    refine ⟨0, j0, ?_, drop_get hdrop⟩
    simp only [iterN]; rw [← hpc, Arm.w_irrelevant]
  · rw [he] at hdrop
    obtain ⟨a, jl, ha, hjl, hstep⟩ := step_branch hR (drop_get hdrop) (.inl rfl) hprog hpc herr
    refine ⟨1, jl, ?_, hjl⟩
    simp only [iterN]; rw [hstep, brCond_b ha]; rfl

theorem invertTo_form {bc : Insn} {t e : Lbl}
    (hbc : (∃ c, bc = .bcond c t) ∨ (∃ nz w r, bc = .cbz nz w r t) ∨ (∃ nz r bit, bc = .tbz nz r bit t)) :
    (∃ c, bc.invertTo e = .bcond c e) ∨ (∃ nz w r, bc.invertTo e = .cbz nz w r e) ∨
      (∃ nz r bit, bc.invertTo e = .tbz nz r bit e) := by
  rcases hbc with ⟨c, rfl⟩ | ⟨nz, w, r, rfl⟩ | ⟨nz, r, bit, rfl⟩
  · exact .inl ⟨_, rfl⟩
  · exact .inr (.inl ⟨_, _, _, rfl⟩)
  · exact .inr (.inr ⟨_, _, _, rfl⟩)

/-- **`b.c T; b E` after `fallthrough`**: the machine reaches a line defining `T` if the
condition holds, else one defining `E`, changing only the pc. -/
theorem reach_cb {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j0 : Nat} {bc : Insn} {t e : Lbl}
    {Z T : List Line} (hdrop : R.L.drop j0 = ftList (.ins bc none :: .ins (.b e) none :: Z) ++ T)
    (hbc : (∃ c, bc = .bcond c t) ∨ (∃ nz w r, bc = .cbz nz w r t) ∨ (∃ nz r bit, bc = .tbz nz r bit t))
    (cond : Bool) (hc : ∀ env a, bc.toArmInst env = .ok a → brCond a s = cond)
    (hc' : ∀ env a, (bc.invertTo e).toArmInst env = .ok a → brCond a s = !cond)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) :
    ∃ n jl, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      R.L[jl]? = some (.label (if cond then t else e)) := by
  have hnb : ∀ x, bc ≠ .b x := by
    rcases hbc with ⟨c, rfl⟩ | ⟨nz, w, r, rfl⟩ | ⟨nz, r, bit, rfl⟩ <;> intro x h <;> cases h
  rcases ft_cb bc e Z hnb with ⟨L, Z', rfl, hct, he⟩ | he
  · have hLt : L = t := by
      rcases hbc with ⟨c, rfl⟩ | ⟨nz, w, r, rfl⟩ | ⟨nz, r, bit, rfl⟩ <;>
        simp only [Insn.condTarget?] at hct
      · split at hct <;> simp_all
      · simp_all
      · simp_all
    subst hLt
    rw [he, ft_label] at hdrop
    have hj0 := drop_get hdrop
    have hj1 := drop_get (drop_succ hdrop)
    have hform := invertTo_form (e := e) hbc
    obtain ⟨a, jl, ha, hjl, hstep⟩ := step_branch hR hj0
      (by rcases hform with h | h | h
          · exact .inr (.inl h)
          · exact .inr (.inr (.inl h))
          · exact .inr (.inr (.inr h))) hprog hpc herr
    rw [hc' _ _ ha] at hstep
    cases cond
    · exact ⟨1, jl, by simp only [iterN]; rw [hstep]; rfl, hjl⟩
    · exact ⟨1, j0 + 1, by simp only [iterN]; rw [hstep]; rfl, hj1⟩
  · rw [he] at hdrop
    obtain ⟨a, jl, ha, hjl, hstep⟩ := step_branch hR (drop_get hdrop)
      (by rcases hbc with h | h | h
          · exact .inr (.inl h)
          · exact .inr (.inr (.inl h))
          · exact .inr (.inr (.inr h))) hprog hpc herr
    rw [hc _ _ ha] at hstep
    cases cond
    · simp only [Bool.false_eq_true, ite_false] at hstep
      have hd1 := drop_succ hdrop
      obtain ⟨n, jl', hn, hjl'⟩ := reach_b hR (s := Arm.w .PC (R.pcOf (j0 + 1)) s) hd1
        (by rw [Arm.w_program, hprog]) (Arm.r_of_w_same ..) (by rw [Arm.r_of_w_different (by simp), herr])
      refine ⟨n + 1, jl', ?_, hjl'⟩
      simp only [iterN]
      rw [hstep, hn, Arm.w_of_w_shadow]
    · exact ⟨1, jl, by simp only [iterN]; rw [hstep]; rfl, hjl⟩

end Backend.Proof
