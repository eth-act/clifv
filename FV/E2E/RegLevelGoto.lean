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

/-- **`b x` after `fallthrough` and relaxation**: the machine reaches a line defining `x` (0 steps
when the branch was dropped, 1 otherwise), changing only the pc. -/
theorem reach_b {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j0 : Nat} {x : Lbl} {Z T : List Line}
    (hdrop : R.L.drop j0 = relaxLines R.far (ftList (.ins (.b x) none :: Z)) ++ T) (hx : x ≠ .skip)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) :
    ∃ n jl, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧ R.L[jl]? = some (.label x) ∧
      ∀ i < n, spOf (iterN R.step i s) = spOf s := by
  rcases ft_b x Z with ⟨Z', rfl, he⟩ | he
  · rw [he, ft_label, relaxLines_cons, relaxLine_label, List.singleton_append] at hdrop
    refine ⟨0, j0, ?_, drop_get hdrop, fun i hi => by omega⟩
    simp only [iterN]; rw [← hpc, Arm.w_irrelevant]
  · rw [he, relaxLines_cons, relaxLine_of_none rfl, List.singleton_append] at hdrop
    obtain ⟨a, jl, ha, hjl, hstep⟩ := step_branch hR (drop_get hdrop) (.inl rfl) hx hprog hpc herr
    refine ⟨1, jl, ?_, hjl, fun i hi => by obtain rfl : i = 0 := by omega
                                           rfl⟩
    simp only [iterN]; rw [hstep, brCond_b ha]; rfl

theorem invertTo_form {bc : Insn} {t e : Lbl}
    (hbc : (∃ c, bc = .bcond c t) ∨ (∃ nz w r, bc = .cbz nz w r t) ∨ (∃ nz r bit, bc = .tbz nz r bit t)) :
    (∃ c, bc.invertTo e = .bcond c e) ∨ (∃ nz w r, bc.invertTo e = .cbz nz w r e) ∨
      (∃ nz r bit, bc.invertTo e = .tbz nz r bit e) := by
  rcases hbc with ⟨c, rfl⟩ | ⟨nz, w, r, rfl⟩ | ⟨nz, r, bit, rfl⟩
  · exact .inl ⟨_, rfl⟩
  · exact .inr (.inl ⟨_, _, _, rfl⟩)
  · exact .inr (.inr ⟨_, _, _, rfl⟩)

theorem Cond.invert_invert (c : Cond) : c.invert.invert = c := by cases c <;> rfl

/-- Inverting a kind's branch twice retargets it. -/
theorem CondBrKind.insn_invertTo_invertTo (k : CondBrKind) (t e l : Lbl) :
    ((k.insn t).invertTo e).invertTo l = k.insn l := by
  cases k <;> simp [CondBrKind.insn, Insn.invertTo, Cond.invert_invert]

theorem drop_succ2 {L T : List Line} {j : Nat} {a b : Line} (h : L.drop j = [a, b] ++ T) :
    L[j + 1]? = some b := by
  have := congrArg (·[1]?) h
  simpa [List.getElem?_drop] using this

/-- **A conditional branch after relaxation** (`relaxLine`: the branch, or `b.!c .+8; b t`): the
machine reaches a line defining `t` if the condition holds, else the line after the relaxed
lines, changing only the pc. -/
theorem reach_rcb {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j0 : Nat} {bc : Insn} {t : Lbl}
    {T : List Line} (hdrop : R.L.drop j0 = relaxLine R.far (.ins bc none) ++ T)
    (hbc : (∃ c, bc = .bcond c t) ∨ (∃ nz w r, bc = .cbz nz w r t) ∨ (∃ nz r bit, bc = .tbz nz r bit t))
    (ht : t ≠ .skip) (cond : Bool) (hc : ∀ env a, bc.toArmInst env = .ok a → brCond a s = cond)
    (hcs : bc.condTarget? = some t → ∀ env a, (bc.invertTo .skip).toArmInst env = .ok a →
      brCond a s = !cond)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) :
    ∃ n jl, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      (cond = true → R.L[jl]? = some (.label t)) ∧
      (cond = false → jl = j0 + (relaxLine R.far (.ins bc none)).length) ∧
      (∀ i < n, spOf (iterN R.step i s) = spOf s) ∧ (cond = false → n = 1) := by
  have h1 : ∀ i < 1, spOf (iterN R.step i s) = spOf s := fun i hi => by
    obtain rfl : i = 0 := by omega
    rfl
  have hform : bc = .b t ∨ (∃ c, bc = .bcond c t) ∨ (∃ nz w r, bc = .cbz nz w r t) ∨
      (∃ nz r bit, bc = .tbz nz r bit t) := .inr hbc
  rcases relaxLine_cases R.far bc with h | ⟨t', ht', h⟩
  · rw [h] at hdrop
    obtain ⟨a, jl, ha, hjl, hstep⟩ := step_branch hR (drop_get (Z := []) (by simpa using hdrop))
      hform ht hprog hpc herr
    rw [hc _ _ ha] at hstep
    cases cond
    · exact ⟨1, j0 + 1, by simp only [iterN]; rw [hstep]; rfl, by simp, by simp [h], h1, fun _ => rfl⟩
    · exact ⟨1, jl, by simp only [iterN]; rw [hstep]; rfl, fun _ => hjl, by simp, h1, by simp⟩
  · have hct := relaxTarget_condTarget ht'
    obtain rfl : t' = t := by
      rcases hbc with ⟨c, rfl⟩ | ⟨nz, w, r, rfl⟩ | ⟨nz, r, bit, rfl⟩ <;>
        simp only [Insn.condTarget?] at hct
      · split at hct <;> simp_all
      · simp_all
      · simp_all
    rw [h] at hdrop
    have hj0 := drop_get (Z := [_]) (by simpa using hdrop)
    have hj1 := drop_succ2 hdrop
    obtain ⟨a, ha, hstep⟩ := step_skip hR hj0 hj1 (invertTo_form hbc) hprog hpc herr
    rw [hcs hct _ _ ha] at hstep
    cases cond
    · exact ⟨1, j0 + 2, by simp only [iterN]; rw [hstep]; rfl, by simp, by simp [h], h1, fun _ => rfl⟩
    · have hprog1 : (Arm.w .PC (R.pcOf (j0 + 1)) s).program = R.fb.program R.base := by
        rw [Arm.w_program, hprog]
      obtain ⟨a', jl, ha', hjl, hstep'⟩ := step_branch hR hj1 (.inl rfl) ht hprog1
        (Arm.r_of_w_same ..) (by rw [Arm.r_of_w_different (by simp), herr])
      rw [brCond_b ha'] at hstep'
      refine ⟨2, jl, ?_, fun _ => hjl, by simp, fun i hi => ?_, by simp⟩
      · simp only [iterN]
        rw [hstep]
        simp only [Bool.not_true, Bool.false_eq_true, ite_false]
        rw [hstep', Arm.w_of_w_shadow]
        rfl
      · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · rfl
        · simp only [iterN]
          rw [hstep]
          exact Arm.r_of_w_different (by simp)

/-- **`b.c T; b E` after `fallthrough` and relaxation**: the machine reaches a line defining `T`
if the condition holds, else one defining `E`, changing only the pc. -/
theorem reach_cb {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j0 : Nat} {bc : Insn} {t e : Lbl}
    {Z T : List Line}
    (hdrop : R.L.drop j0 = relaxLines R.far (ftList (.ins bc none :: .ins (.b e) none :: Z)) ++ T)
    (hbc : (∃ c, bc = .bcond c t) ∨ (∃ nz w r, bc = .cbz nz w r t) ∨ (∃ nz r bit, bc = .tbz nz r bit t))
    (ht : t ≠ .skip) (he : e ≠ .skip)
    (cond : Bool) (hc : ∀ env a, bc.toArmInst env = .ok a → brCond a s = cond)
    (hc' : bc.condTarget? = some t → ∀ e' env a, (bc.invertTo e').toArmInst env = .ok a →
      brCond a s = !cond)
    (hcc : bc.condTarget? = some t → ∀ env a, ((bc.invertTo e).invertTo .skip).toArmInst env = .ok a →
      brCond a s = cond)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) :
    ∃ n jl, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      R.L[jl]? = some (.label (if cond then t else e)) ∧
      ∀ i < n, spOf (iterN R.step i s) = spOf s := by
  have hnb : ∀ x, bc ≠ .b x := by
    rcases hbc with ⟨c, rfl⟩ | ⟨nz, w, r, rfl⟩ | ⟨nz, r, bit, rfl⟩ <;> intro x h <;> cases h
  rcases ft_cb bc e Z hnb with ⟨L, Z', rfl, hct, hft⟩ | hft
  · have hLt : L = t := by
      rcases hbc with ⟨c, rfl⟩ | ⟨nz, w, r, rfl⟩ | ⟨nz, r, bit, rfl⟩ <;>
        simp only [Insn.condTarget?] at hct
      · split at hct <;> simp_all
      · simp_all
      · simp_all
    subst hLt
    rw [hft, ft_label, relaxLines_cons, relaxLines_cons, relaxLine_label, List.append_assoc] at hdrop
    have hform := invertTo_form (e := e) hbc
    have hct' : (bc.invertTo e).condTarget? = some e := by
      rcases hbc with ⟨c, rfl⟩ | ⟨nz, w, r, rfl⟩ | ⟨nz, r, bit, rfl⟩ <;>
        simp only [Insn.condTarget?] at hct ⊢
      · split at hct
        · cases hct
        · rename_i hc0
          simp only [Insn.invertTo, Insn.condTarget?]
          rcases c <;> simp_all [Cond.invert]
      · simp [Insn.invertTo, Insn.condTarget?]
      · simp [Insn.invertTo, Insn.condTarget?]
    obtain ⟨n, jl, hn, hjt, hjf, hsp, -⟩ := reach_rcb hR hdrop hform he (!cond) (hc' hct e)
      (fun _ env a ha => by rw [hcc hct env a ha, Bool.not_not]) hprog hpc herr
    refine ⟨n, jl, hn, ?_, hsp⟩
    cases cond
    · simpa using hjt rfl
    · have hd' : R.L.drop jl = [Line.label L] ++ relaxLines R.far (ftList Z') ++ T := by
        rw [hjf rfl, ← List.drop_drop, hdrop, List.drop_left, List.append_assoc]
      simpa using drop_get (by simpa using hd')
  · rw [hft, relaxLines_cons, List.append_assoc] at hdrop
    obtain ⟨n, jl, hn, hjt, hjf, hsp, -⟩ := reach_rcb hR hdrop hbc ht cond hc
      (fun hct' => hc' hct' .skip) hprog hpc herr
    cases cond
    · have hd1 : R.L.drop jl = relaxLines R.far (ftList (.ins (.b e) none :: Z)) ++ T := by
        rw [hjf rfl, ← List.drop_drop, hdrop, List.drop_left]
      have hs1 : (iterN R.step n s).program = R.fb.program R.base := by rw [hn, Arm.w_program, hprog]
      obtain ⟨n', jl', hn', hjl', hsp'⟩ := reach_b hR hd1 he hs1 (by rw [hn]; exact Arm.r_of_w_same ..)
        (by rw [hn, Arm.r_of_w_different (by simp), herr])
      refine ⟨n + n', jl', ?_, by simpa using hjl', fun i hi => ?_⟩
      · rw [iterN_add, hn', hn, Arm.w_of_w_shadow]
      · rcases Nat.lt_or_ge i n with h | h
        · exact hsp i h
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
          rw [iterN_add, hsp' k (by omega), hn]
          exact Arm.r_of_w_different (by simp)
    · exact ⟨n, jl, hn, by simpa using hjt rfl, hsp⟩


/-! ## Conditions -/

theorem condHolds_congr {s w : Arm.ArmState} (h : ∀ f, Arm.r (.FLAG f) s = Arm.r (.FLAG f) w)
    (c : BitVec 4) : Arm.ConditionHolds c s = Arm.ConditionHolds c w := by
  unfold Arm.ConditionHolds Arm.read_flag
  rw [h, h, h, h]

theorem flags_of_world {F : BitVec 64 → Prop} {s w : Arm.ArmState} (h : SameWorld F s w) :
    ∀ f, Arm.r (.FLAG f) s = Arm.r (.FLAG f) w := fun f => h.1 _ (by simp [Masked])

theorem lo64_regX (x : BitVec 64) : lo64 (x.setWidth 128) = x := by
  simp only [lo64]; rw [BitVec.setWidth_setWidth_of_le _ (by omega)]; simp

/-- A condition kind `k` (VCode) and its allocated form `k'` with the use values `us` it reads
from the store `m`. -/
def KindRel (m : Loc → CV) : CondBrKind → CondBrKind → List CV → Prop
  | .cond c, .cond c', us => c' = c ∧ us = []
  | .zero _ sz, .zero r' sz', us =>
    sz' = sz ∧ ∃ n, r' = .x n ∧ (Reg.x n).allocatable = true ∧ us = [m (.reg (.x n))]
  | .notZero _ sz, .notZero r' sz', us =>
    sz' = sz ∧ ∃ n, r' = .x n ∧ (Reg.x n).allocatable = true ∧ us = [m (.reg (.x n))]
  | _, _, _ => False

/-- The decoded branch of `k'` tests `k`'s condition on the uses. -/
theorem kind_brCond {R : RL} {s : Arm.ArmState} {m : Loc → CV} {w : Arm.ArmState}
    (hst : StRel R s m w) {k k' : CondBrKind} {us : List CV} (hk : KindRel m k k' us) (l : Lbl)
    {env : Env} {a : Arm.ArmInst} (ha : (k'.insn l).toArmInst env = .ok a) :
    brCond a s = k.holds us w := by
  have hm : ∀ n, (Reg.x n).allocatable = true →
      m (.reg (.x n)) = (Arm.r (.GPR (rnum n)) s).setWidth 128 := by
    intro n hn
    rw [hst.store (.reg (.x n)) (fun r e => by cases e; exact hn) trivial]; rfl
  have h30 : ∀ n, (Reg.x n).allocatable = true → n ≤ 30 := by
    intro n hn
    rcases allocatable_cases hn with ⟨n', e, h1, -⟩ | ⟨n', e, -⟩ <;> cases e; omega
  cases k <;> cases k' <;> simp only [KindRel] at hk
  · obtain ⟨rfl, n, rfl, hn, rfl⟩ := hk
    rw [brCond_cbz (h30 n hn) ha, hm n hn]
    simp only [CondBrKind.holds, lo64_regX]
    split <;> simp [bne]
  · obtain ⟨rfl, n, rfl, hn, rfl⟩ := hk
    rw [brCond_cbz (h30 n hn) ha, hm n hn]
    simp only [CondBrKind.holds, lo64_regX]
    split <;> simp [bne]
  · obtain ⟨rfl, rfl⟩ := hk
    rw [brCond_bcond ha, condHolds_congr (flags_of_world hst.world)]
    rfl

theorem kind_brCond_inv {R : RL} {s : Arm.ArmState} {m : Loc → CV} {w : Arm.ArmState}
    (hst : StRel R s m w) {k k' : CondBrKind} {us : List CV} (hk : KindRel m k k' us) (l e : Lbl)
    (hct : (k'.insn l).condTarget? = some l)
    {env : Env} {a : Arm.ArmInst} (ha : ((k'.insn l).invertTo e).toArmInst env = .ok a) :
    brCond a s = !k.holds us w := by
  have hm : ∀ n, (Reg.x n).allocatable = true →
      m (.reg (.x n)) = (Arm.r (.GPR (rnum n)) s).setWidth 128 := by
    intro n hn
    rw [hst.store (.reg (.x n)) (fun r e => by cases e; exact hn) trivial]; rfl
  have h30 : ∀ n, (Reg.x n).allocatable = true → n ≤ 30 := by
    intro n hn
    rcases allocatable_cases hn with ⟨n', e, h1, -⟩ | ⟨n', e, -⟩ <;> cases e; omega
  cases k <;> cases k' <;> simp only [KindRel] at hk
  · obtain ⟨rfl, n, rfl, hn, rfl⟩ := hk
    simp only [CondBrKind.insn, Insn.invertTo] at ha
    rw [brCond_cbz (h30 n hn) ha, hm n hn]
    simp only [CondBrKind.holds, lo64_regX]
    split <;> simp [bne]
  · obtain ⟨rfl, n, rfl, hn, rfl⟩ := hk
    simp only [CondBrKind.insn, Insn.invertTo] at ha
    rw [brCond_cbz (h30 n hn) ha, hm n hn]
    simp only [CondBrKind.holds, lo64_regX]
    split <;> simp [bne]
  · obtain ⟨rfl, rfl⟩ := hk
    rename_i c
    simp only [CondBrKind.insn, Insn.condTarget?] at hct
    have hc : c ≠ .al ∧ c ≠ .nv := by
      constructor <;> intro h <;> subst h <;> simp at hct
    simp only [CondBrKind.insn, Insn.invertTo] at ha
    rw [brCond_bcond ha, condHolds_invert c hc.1 hc.2, condHolds_congr (flags_of_world hst.world)]
    rfl

/-! ## Operands of the conditional forms -/

theorem assign_one {i : MInst} {mk : Reg → MInst} {n : Nat} {sp : OpSpec}
    (hv : ∀ (f : OpSpec → Reg → StateT Nat (Except String) Reg), MInst.visitOperands f i = do
      let r ← f sp (.vreg n .int); pure (mk r))
    {regs : Array Reg} {i' : MInst} (h : i.assign regs = .ok i') : ∃ r, regs = #[r] ∧ i' = mk r := by
  unfold MInst.assign at h
  dsimp only at h
  rw [hv] at h
  cases hr : regs[0]? with
  | none =>
    simp [hr, StateT.run, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
      set, StateT.set, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      StateT.lift, MonadLift.monadLift, Except.tryCatch] at h
  | some r =>
    simp [hr, StateT.run, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
      set, StateT.set, pure, StateT.pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      StateT.lift, MonadLift.monadLift] at h
    split at h
    · rename_i hs
      simp only [Except.ok.injEq] at h
      refine ⟨r, ?_, h.symm⟩
      apply Array.ext
      · simp [← hs]
      · intro k h1 h2
        have : k = 0 := by simp at h2; omega
        subst this
        simp [Array.getElem?_eq_some_iff] at hr
        simpa using hr.2
    · cases h

theorem assign_none {i : MInst}
    (hv : ∀ (f : OpSpec → Reg → StateT Nat (Except String) Reg), MInst.visitOperands f i = pure i)
    {regs : Array Reg} {i' : MInst} (h : i.assign regs = .ok i') : regs = #[] ∧ i' = i := by
  unfold MInst.assign at h
  dsimp only at h
  rw [hv] at h
  simp [StateT.run, pure, StateT.pure, Except.pure, bind, Except.bind] at h
  split at h
  · rename_i hs
    simp only [Except.ok.injEq] at h
    exact ⟨Array.eq_empty_of_size_eq_zero hs.symm, h.symm⟩
  · cases h

/-- The allocated form of a condition-kind instruction (`condBr`/`trapIf`, visited as
`CondBrKind.visit`) and the use values `MStep` passes. -/
theorem kind_alloc {k : CondBrKind} (hck : ∀ r sz, k = .zero r sz ∨ k = .notZero r sz → r.isVregInt = true)
    {i : MInst} {mk : CondBrKind → MInst} (hmk : i = mk k)
    (hv : ∀ (f : OpSpec → Reg → StateT Nat (Except String) Reg), MInst.visitOperands f i = do
      let k' ← CondBrKind.visit f k; pure (mk k'))
    (hvo : ∀ (f : OpSpec → Reg → StateT (Array Operand) (Except String) Reg),
      MInst.visitOperands f i = do let k' ← CondBrKind.visit f k; pure (mk k'))
    {ops : Array Operand} (hops : i.operands = .ok ops) {c : CheckCtx} {wh : String}
    {regs : Array Reg} (hst : c.checkStatic wh ops (regs.map Loc.reg) i.clobbers = .ok ())
    {i' : MInst} (hasg : i.assign regs = .ok i') (m : Loc → CV) :
    ∃ k', i' = mk k' ∧
      KindRel m k k' (((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isUse)).map (m ·.2)) := by
  have hao := allocOk_of_checkStatic hst
  cases k with
  | cond cc =>
    obtain ⟨rfl, rfl⟩ := assign_none (fun f => by rw [hv]; simp [CondBrKind.visit, hmk]) hasg
    have : ops = #[] := by
      have e := hops
      rw [MInst.operands] at e
      simp only [hvo, CondBrKind.visit] at e
      simp [StateT.run, pure, StateT.pure, Except.pure, bind, StateT.bind, Except.bind] at e
      exact e
    subst this
    exact ⟨.cond cc, hmk, rfl, by simp⟩
  | zero r sz =>
    obtain ⟨n, rfl⟩ := isVregInt_iff (hck r sz (.inl rfl))
    obtain ⟨r', rfl, rfl⟩ := assign_one (n := n) (sp := OpSpec.use) (mk := fun r => mk (.zero r sz))
      (fun f => by rw [hv]; simp only [CondBrKind.visit, bind_assoc, pure_bind]) hasg
    have hops' : ops = #[⟨n, .int, .use, .early, .reg⟩] := by
      have e := hops
      rw [MInst.operands] at e
      simp only [hvo, CondBrKind.visit] at e
      simp [StateT.run, pure, StateT.pure, Except.pure, bind, StateT.bind, Except.bind, modify,
        modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at e
      exact e.symm
    subst hops'
    have hf := hao.fits (⟨n, .int, .use, .early, .reg⟩, r') (by simp)
    obtain ⟨⟨n', rfl, -⟩, -⟩ := hf
    have hal := ((checkStatic_facts hst).2.1 (⟨n, .int, .use, .early, .reg⟩, .reg (.x n'))
      (by simp)).1
    simp only [CheckCtx.locOk, Bool.and_eq_true] at hal
    exact ⟨_, rfl, rfl, n', rfl, hal.2, by simp [Operand.isUse]⟩
  | notZero r sz =>
    obtain ⟨n, rfl⟩ := isVregInt_iff (hck r sz (.inr rfl))
    obtain ⟨r', rfl, rfl⟩ := assign_one (n := n) (sp := OpSpec.use) (mk := fun r => mk (.notZero r sz))
      (fun f => by rw [hv]; simp only [CondBrKind.visit, bind_assoc, pure_bind]) hasg
    have hops' : ops = #[⟨n, .int, .use, .early, .reg⟩] := by
      have e := hops
      rw [MInst.operands] at e
      simp only [hvo, CondBrKind.visit] at e
      simp [StateT.run, pure, StateT.pure, Except.pure, bind, StateT.bind, Except.bind, modify,
        modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at e
      exact e.symm
    subst hops'
    have hf := hao.fits (⟨n, .int, .use, .early, .reg⟩, r') (by simp)
    obtain ⟨⟨n', rfl, -⟩, -⟩ := hf
    have hal := ((checkStatic_facts hst).2.1 (⟨n, .int, .use, .early, .reg⟩, .reg (.x n'))
      (by simp)).1
    simp only [CheckCtx.locOk, Bool.and_eq_true] at hal
    exact ⟨_, rfl, rfl, n', rfl, hal.2, by simp [Operand.isUse]⟩

theorem codeLinesE_single {c : FnCtx} {af : AFunc} {i : MInst} {ps ps' : PState} {ls : List Line}
    (h : codeLinesE c af [.inst i] ps = .ok (ls, ps')) : i.lines c ps = .ok (ls, ps') := by
  simp only [codeLinesE, ainstLines, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i r hr
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, List.append_nil] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hr

theorem beq_not_right (a b : Bool) : (a == !b) = !(a == b) := by cases a <;> cases b <;> rfl

/-- **Block-ending branches on the machine**: from `Q` at a `jump`/`condBr`/`testBitAndBranch`
item, the machine reaches `Q` at the `MStep` successor (the chosen successor's items). -/
theorem realizes_goto {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {c' : MConf CV Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {i : MInst}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    (hbr : (∃ l, i = .jump l) ∨ (∃ t e kk, i = .condBr t e kk) ∨
      (∃ kd t e rn bit, i = .testBitAndBranch kd t e rn bit))
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c') :
    ∃ n, Q R (iterN R.step n s) c' ∧ ∀ i < n, R.Good (iterN R.step i s) := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  obtain ⟨j0, vb0, items, pre, code, ls, ps1, ps2, T, hvb0, hit, hsplit, hchk, hcode, hls, htr, hdrop,
    hpc, hst⟩ := hq
  rw [hvb] at hvb0; cases hvb0
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
  rw [hi] at hi0; cases hi0
  obtain ⟨cc, wh, i2, ops2, hi2, hops2, hstat, -⟩ := op_checked hchk
  rw [hi] at hi2; cases hi2
  obtain ⟨ls1, ls2, psm, h1, h2, rfl⟩ := codeLinesE_append _ _ _ _ _ hls
  obtain ⟨c, ins, _, hc, -⟩ := hR.check
  obtain ⟨preds, hcfg⟩ := hc.cfg
  obtain ⟨t0, ts, hback, hss, hlab⟩ := cfg_block hcfg hvb
  cases h with
  | @op b k allocs its m w vb' i ops outs outs' w' ctl m2 c' hvb' hi' hops' hsz hsem hlen hho hcl hn =>
  rw [hvb] at hvb'; cases hvb'
  rw [hi] at hi'; cases hi'
  rw [hops2] at hops'; cases hops'
  -- the semantics: no defs, same world, `goto j`
  generalize hU : (((ops2.zip (regs.map Loc.reg)).toList.filter (·.1.isUse)).map (m ·.2)) = U at hsem
  have hsem' : outs = [] ∧ w' = w ∧ ∃ j, ctl = .goto j ∧ (∀ l, i = .jump l → j = 0) ∧
      (∀ t e kk, i = .condBr t e kk → j = if kk.holds U w then 0 else 1) ∧
      (∀ kd t e rn bit, i = .testBitAndBranch kd t e rn bit →
        ∃ a, U = [a] ∧ j = if ((lo64 a).getLsbD bit == (kd == .nz)) then 0 else 1) := by
    rcases hbr with ⟨l, rfl⟩ | ⟨t, e, kk, rfl⟩ | ⟨kd, t, e, rn, bit, rfl⟩
    · simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
      obtain ⟨rfl, rfl, rfl⟩ := hsem
      refine ⟨rfl, rfl, 0, rfl, fun _ _ => rfl, ?_, ?_⟩
      · intro _ _ _ h; cases h
      · intro _ _ _ _ _ h; cases h
    · simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
      obtain ⟨rfl, rfl, rfl⟩ := hsem
      refine ⟨rfl, rfl, _, rfl, ?_, ?_, ?_⟩
      · intro _ h; cases h
      · intro t' e' kk' h; cases h; rfl
      · intro _ _ _ _ _ h; cases h
    · simp only [RL.sem, csemV, csem] at hsem
      split at hsem
      · rename_i a
        simp only [Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        refine ⟨rfl, rfl, _, rfl, ?_, ?_, ?_⟩
        · intro _ h; cases h
        · intro _ _ _ h; cases h
        intro kd' t' e' rn' bit' h
        cases h
        exact ⟨a, rfl, rfl⟩
      · cases hsem
  obtain ⟨rfl, hw', j, rfl, hj0, hjc, hjt⟩ := hsem'
  obtain rfl : outs' = [] := List.eq_nil_of_length_eq_zero hho.1
  subst w'
  -- the store is unchanged
  have hm2 : m2 = m := by
    funext l
    refine (hcl.1 l ?_).trans ?_
    · rcases hbr with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ <;> simp [MInst.clobbers]
    · simp [writeM]
  subst m2
  cases hn with
  | @goto _ st items' hk1 hsucc hitems =>
  have hwm : writeM m ((((ops2.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip
      ([] : List CV)).filter (·.1.1.isLate)) = m := by simp [writeM]
  rw [hwm]
  -- the successor's label
  have hti : t0 = i := by
    rw [Array.back?_eq_getElem?, show vb.insts.size - 1 = k by omega, hi] at hback
    cases hback; rfl
  subst hti
  have hsucc' := hsucc
  simp only [succOf, hcfg, hss, Option.bind_some] at hsucc'
  obtain ⟨vs, hvs, hlj⟩ := hlab j st hsucc'
  have hst0 : st ≠ 0 := ctlCheck_succ hck hsucc
  -- the machine reaches the successor's label
  have hreach : ∃ n jl, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      R.L[jl]? = some (.label (.block vs.label)) ∧ ∀ i < n, spOf (iterN R.step i s) = spOf s := by
    rw [List.append_assoc] at hdrop
    rcases hbr with ⟨l, rfl⟩ | ⟨t, e, kk, rfl⟩ | ⟨kd, t, e, rn, bit, rfl⟩
    · obtain ⟨rfl, rfl⟩ := assign_none (fun f => rfl) hasg
      obtain rfl : c1 = [.inst _] := by
        rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
        · exact h
        · cases h
        · cases h
      have hl1 := codeLinesE_single h1
      simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
      obtain ⟨rfl, -⟩ := hl1
      rw [hj0 l rfl] at hlj
      simp only [MInst.targets, List.getElem?_cons_zero, Option.some.injEq] at hlj
      rw [← hlj]
      exact reach_b hR (by simpa using hdrop) (by simp) (by rw [hst.prog]) hpc hst.err
    · have hkk : ∀ r sz, kk = .zero r sz ∨ kk = .notZero r sz → r.isVregInt = true := by
        intro r sz hr
        have := ctlCheck_inst hck hvb hi
        rcases hr with rfl | rfl <;> simpa [ctlInstOk] using this
      obtain ⟨k', rfl, hkr⟩ := kind_alloc hkk (mk := fun k => MInst.condBr t e k) rfl
        (fun f => rfl) (fun f => rfl) hops2 hstat hasg m
      obtain rfl : c1 = [.inst _] := by
        rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
        · exact h
        · cases h
        · cases h
      have hl1 := codeLinesE_single h1
      simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
      obtain ⟨rfl, -⟩ := hl1
      have hbc : (∃ c, k'.insn (.block t) = .bcond c (.block t)) ∨
          (∃ nz w r, k'.insn (.block t) = .cbz nz w r (.block t)) ∨
          (∃ nz r bit, k'.insn (.block t) = .tbz nz r bit (.block t)) := by
        cases k' <;> simp [CondBrKind.insn]
      obtain ⟨n, jl, hn, hjl, hsp⟩ := reach_cb hR (by simpa using hdrop) hbc (by simp) (by simp) (kk.holds _ w)
        (fun env a ha => kind_brCond hst hkr _ ha)
        (fun hct e' env a ha => kind_brCond_inv hst hkr _ _ hct ha)
        (fun _ env a ha => kind_brCond hst hkr _ (by rwa [CondBrKind.insn_invertTo_invertTo] at ha))
        (by rw [hst.prog]) hpc hst.err
      refine ⟨n, jl, hn, ?_, hsp⟩
      rw [hjl, hU]
      rw [hjc t e kk rfl] at hlj
      simp only [MInst.targets] at hlj
      cases hcond : kk.holds U w <;> simp only [hcond] at hlj ⊢ <;> simp at hlj <;> rw [hlj] <;> simp
    · obtain ⟨nr, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
      obtain ⟨r', rfl, rfl⟩ := assign_one (n := nr) (sp := OpSpec.use) (mk := fun r => MInst.testBitAndBranch kd t e r bit)
        (fun f => by simp [MInst.visitOperands]) hasg
      have hops' : ops2 = #[⟨nr, .int, .use, .early, .reg⟩] := by
        have e : (MInst.testBitAndBranch kd t e (.vreg nr .int) bit).operands =
            .ok #[⟨nr, .int, .use, .early, .reg⟩] := rfl
        rw [e] at hops2
        injection hops2 with h
        exact h.symm
      subst hops'
      obtain ⟨⟨n', rfl, hn', -⟩, -⟩ := (allocOk_of_checkStatic hstat).fits
        (⟨nr, .int, .use, .early, .reg⟩, r') (by simp)
      obtain rfl : c1 = [.inst _] := by
        rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
        · exact h
        · cases h
        · cases h
      have hl1 := codeLinesE_single h1
      simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
      obtain ⟨rfl, -⟩ := hl1
      have hal := ((checkStatic_facts hstat).2.1 (⟨nr, .int, .use, .early, .reg⟩, .reg (.x n'))
        (by simp)).1
      simp only [CheckCtx.locOk, Bool.and_eq_true] at hal
      have hm : m (.reg (.x n')) = (Arm.r (.GPR (rnum n')) s).setWidth 128 := by
        rw [hst.store (.reg (.x n')) (fun r e => by cases e; exact hal.2) trivial]; rfl
      obtain ⟨n, jl, hn, hjl, hsp⟩ := reach_cb hR (by simpa using hdrop)
        (bc := .tbz (kd == .nz) (.x n') bit (.block t)) (.inr (.inr ⟨_, _, _, rfl⟩)) (by simp) (by simp)
        ((Arm.r (.GPR (rnum n')) s).getLsbD bit == (kd == .nz))
        (fun env a ha => brCond_tbz (by omega) ha s)
        (fun _ e' env a ha => by
          simp only [Insn.invertTo] at ha
          rw [brCond_tbz (by omega) ha s, beq_not_right])
        (fun _ env a ha => by
          simp only [Insn.invertTo, Bool.not_not] at ha
          exact brCond_tbz (by omega) ha s)
        (by rw [hst.prog]) hpc hst.err
      refine ⟨n, jl, hn, ?_, hsp⟩
      rw [hjl]
      obtain ⟨a, hUa, hja⟩ := hjt kd t e _ bit rfl
      have ha : a = m (.reg (.x n')) := by
        rw [← hU] at hUa
        simp [Operand.isUse] at hUa
        exact hUa.symm
      subst ha
      rw [hja] at hlj
      simp only [MInst.targets, hm, lo64_regX] at hlj
      cases hcond : ((Arm.r (.GPR (rnum n')) s).getLsbD bit == (kd == .nz)) <;>
        simp only [hcond] at hlj ⊢ <;> simp at hlj <;> rw [hlj] <;> simp
  obtain ⟨n, jl, hn, hjl, hsp⟩ := hreach
  refine ⟨n, ?_, fun i hi => RL.good_of_sp ((hsp i hi).trans hst.sp)⟩
  rw [hn]
  exact q_entry hR hst0 hvs hitems hjl (Arm.r_of_w_same ..) (hst.pc _)

end Backend.Proof
