import FV.E2E.RegLevelArgs

/-!
# Block labels and forwarding blocks (M6)

Block labels are defined once in the laid-out lines (`labelOffsets_uniq`), so the blocks of the
allocated code have different labels (`af_label_inj`, `RL.label_inj`). A forwarding block
(`AFunc.fwd?`, a block `MachBuffer` may alias to its target) is a block other than the entry
whose items are one `op` of its only instruction, a `jump` to its successor (`RL.fwd_block`).
-/

namespace Backend.Proof

open Backend E2E

/-! ## Labels are defined once -/

theorem labelOffsets_go_fresh : ∀ {L : List Line} {off : Nat} {m m' : Std.HashMap Lbl Nat},
    labelOffsets.go L off m = .ok m' → ∀ {j : Nat} {l : Lbl}, L[j]? = some (.label l) →
      m.contains l = false
  | [], _, _, _, _, j, _, hj => by simp at hj
  | ln :: L, off, m, m', h, j, l, hj => by
    cases ln with
    | label l0 =>
      simp only [labelOffsets.go] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · rename_i hc
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Line.label.injEq] at hj
          subst hj
          simpa using hc
        | succ j =>
          have := labelOffsets_go_fresh h (j := j) (by simpa using hj)
          rw [Std.HashMap.contains_insert] at this
          simp only [Bool.or_eq_false_iff] at this
          exact this.2
    | ins i t =>
      simp only [labelOffsets.go] at h
      cases j with
      | zero => simp at hj
      | succ j => exact labelOffsets_go_fresh h (by simpa using hj)
    | word a b =>
      simp only [labelOffsets.go] at h
      cases j with
      | zero => simp at hj
      | succ j => exact labelOffsets_go_fresh h (by simpa using hj)

theorem labelOffsets_go_uniq : ∀ {L : List Line} {off : Nat} {m m' : Std.HashMap Lbl Nat},
    labelOffsets.go L off m = .ok m' → ∀ {j1 j2 : Nat} {l : Lbl}, L[j1]? = some (.label l) →
      L[j2]? = some (.label l) → j1 = j2
  | [], _, _, _, _, _, _, _, h1, _ => by simp at h1
  | ln :: L, off, m, m', h, j1, j2, l, h1, h2 => by
    have hrest : ∃ off' m'', labelOffsets.go L off' m'' = .ok m' ∧
        ∀ l0, ln = .label l0 → m''.contains l0 = true := by
      cases ln with
      | label l0 =>
        simp only [labelOffsets.go] at h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · exact ⟨_, _, h, fun l1 e => by cases e; simp⟩
      | ins i t =>
        simp only [labelOffsets.go] at h
        exact ⟨_, _, h, fun _ e => by cases e⟩
      | word a b =>
        simp only [labelOffsets.go] at h
        exact ⟨_, _, h, fun _ e => by cases e⟩
    obtain ⟨off', m'', hg, hc⟩ := hrest
    cases j1 with
    | zero =>
      cases j2 with
      | zero => rfl
      | succ k =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h1
        have := labelOffsets_go_fresh hg (j := k) (by simpa using h2)
        rw [hc l h1] at this
        cases this
    | succ k =>
      cases j2 with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h2
        have := labelOffsets_go_fresh hg (j := k) (by simpa using h1)
        rw [hc l h2] at this
        cases this
      | succ k' =>
        exact congrArg (· + 1) (labelOffsets_go_uniq hg (by simpa using h1) (by simpa using h2))

/-- A label line of a laid-out function is its label's only one. -/
theorem labelOffsets_uniq {lines : Array Line} {lm : Std.HashMap Lbl Nat}
    (h : labelOffsets lines = .ok lm) {j1 j2 : Nat} {l : Lbl}
    (h1 : lines.toList[j1]? = some (.label l)) (h2 : lines.toList[j2]? = some (.label l)) :
    j1 = j2 :=
  labelOffsets_go_uniq h h1 h2

theorem rix_mono (F : Lbl → Bool) (L : List Line) {j j' : Nat} (h : j ≤ j') :
    rix F L j ≤ rix F L j' := by
  unfold rix
  rw [relax_split F (L.take j') j, List.take_take, Nat.min_eq_left h, List.length_append]
  omega

theorem getElem?_mid {α : Type} (X : List α) (a : α) (Y : List α) : (X ++ a :: Y)[X.length]? = some a := by
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- **The segments of an emission plan have different labels** (`labelOffsets` of the final
lines defines every label once). -/
theorem plan_seg_label_inj {k : Nat} {af : AFunc} {fa : FnAsm} (h : emitFunc k af = .ok fa)
    {lm : Std.HashMap Lbl Nat} (hlm : labelOffsets fa.lines = .ok lm) {p : Plan}
    (hp : emitPlan k af = .ok p) :
    ∀ {i1 i2 : Nat} {s1 s2 : Seg}, p.segs[i1]? = some s1 → p.segs[i2]? = some s2 →
      s1.label = s2.label → i1 = i2 := by
  have key : ∀ {i1 i2 : Nat} {s1 s2 : Seg}, p.segs[i1]? = some s1 → p.segs[i2]? = some s2 →
      s1.label = s2.label → i1 < i2 → False := by
    intro i1 i2 s1 s2 h1 h2 he hlt
    obtain ⟨-, hlen, -⟩ := emitPlan_spec hp
    have hl1 := (List.getElem?_eq_some_iff.mp h1).1
    have hl2 := (List.getElem?_eq_some_iff.mp h2).1
    obtain ⟨o1, ho1⟩ : ∃ o, p.outs[i1]? = some o :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlen]; exact hl1)⟩
    obtain ⟨o2, ho2⟩ : ∃ o, p.outs[i2]? = some o :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlen]; exact hl2)⟩
    obtain ⟨A, hA, -⟩ := segLines_at h1 ho1
    have h2' : (p.segs.drop (i1 + 1))[i2 - (i1 + 1)]? = some s2 := by
      rw [List.getElem?_drop, show i1 + 1 + (i2 - (i1 + 1)) = i2 by omega]; exact h2
    have ho2' : (p.outs.drop (i1 + 1))[i2 - (i1 + 1)]? = some o2 := by
      rw [List.getElem?_drop, show i1 + 1 + (i2 - (i1 + 1)) = i2 by omega]; exact ho2
    obtain ⟨A', hA', -⟩ := segLines_at h2' ho2'
    have hlines : p.lines = A ++ Line.label (.block s1.label) ::
        ((s1.body ++ o1) ++ (A' ++ Line.label (.block s2.label) ::
          ((s2.body ++ o2) ++ segLines ((p.segs.drop (i1 + 1)).drop (i2 - (i1 + 1) + 1))
            ((p.outs.drop (i1 + 1)).drop (i2 - (i1 + 1) + 1)) ++ trapLines p.ps))) := by
      rw [Plan.lines, hA, hA']
      simp
    generalize hP1 : A.length = P1
    have e1 : p.lines[P1]? = some (.label (.block s1.label)) := by
      rw [hlines, ← hP1]; exact getElem?_mid _ _ _
    have e2 : p.lines[P1 + 1 + (s1.body ++ o1).length + A'.length]? =
        some (.label (.block s1.label)) := by
      rw [hlines, he, ← hP1]
      rw [List.getElem?_append_right (by simp <;> omega)]
      simp only [List.length_append, List.length_cons]
      rw [show A.length + 1 + (s1.body.length + o1.length) + A'.length - A.length =
        (s1.body.length + o1.length + A'.length) + 1 by omega, List.getElem?_cons_succ]
      rw [List.getElem?_append_right (by simp <;> omega)]
      simp only [List.length_append]
      rw [show s1.body.length + o1.length + A'.length - (s1.body.length + o1.length) = A'.length
        by omega]
      exact getElem?_mid _ _ _
    obtain ⟨p', hp', hL, -⟩ := emit_seg h
    rw [hp] at hp'
    cases hp'
    have r1 := (relax_label (F := emitFar ⟨k, af.slotBase⟩ af) e1)
    have r2 := (relax_label (F := emitFar ⟨k, af.slotBase⟩ af) e2)
    rw [← hL] at r1 r2
    have := labelOffsets_uniq hlm r1.1 r2.1
    have hm := rix_mono (emitFar ⟨k, af.slotBase⟩ af) p.lines
      (show P1 + 1 ≤ P1 + 1 + (s1.body ++ o1).length + A'.length by omega)
    rw [r1.2] at hm
    omega
  intro i1 i2 s1 s2 h1 h2 he
  rcases Nat.lt_trichotomy i1 i2 with hlt | heq | hgt
  · exact (key h1 h2 he hlt).elim
  · exact heq
  · exact (key h2 h1 he.symm hgt).elim

/-- **Block labels of the allocated code are unique.** -/
theorem af_label_inj {k : Nat} {af : AFunc} {fa : FnAsm} (h : emitFunc k af = .ok fa)
    {lm : Std.HashMap Lbl Nat} (hlm : labelOffsets fa.lines = .ok lm) {b1 b2 : Nat} {l : Label}
    {c1 c2 : Array AInst} (h1 : af.blocks[b1]? = some (l, c1)) (h2 : af.blocks[b2]? = some (l, c2)) :
    b1 = b2 := by
  obtain ⟨p, hp, -, hb⟩ := emit_seg h
  obtain ⟨i1, s1, -, -, -, -, -, hs1, -, hx1, hl1, -⟩ := hb _ _ _ h1
  obtain ⟨i2, s2, -, -, -, -, -, hs2, -, hx2, hl2, -⟩ := hb _ _ _ h2
  have := plan_seg_label_inj h hlm hp hs1 hs2 (hl1.trans hl2.symm)
  subst this
  rw [hs1] at hs2
  cases hs2
  rw [← hx1, ← hx2]

/-- **Block labels of an activation's VCode are unique** (among its allocated blocks). -/
theorem RL.label_inj {R : RL} (hR : R.Wf) {b1 b2 : Nat} {vb1 vb2 : VBlock}
    {it1 it2 : Array RItem} (hv1 : R.vc.blocks[b1]? = some vb1) (hi1 : R.rf.blocks[b1]? = some it1)
    (hv2 : R.vc.blocks[b2]? = some vb2) (hi2 : R.rf.blocks[b2]? = some it2)
    (he : vb1.label = vb2.label) : b1 = b2 := by
  obtain ⟨⟨-, -, -, hbl⟩, -⟩ := lowerRFunc_ok hR.alloc
  obtain ⟨c1, -, ha1⟩ := hbl b1 vb1 it1 hv1 hi1
  obtain ⟨c2, -, ha2⟩ := hbl b2 vb2 it2 hv2 hi2
  rw [he] at ha1
  exact af_label_inj hR.emit hR.lm ha1 ha2

/-! ## Forwarding blocks -/

theorem fwd?_spec {af : AFunc} {s x : Label} (h : af.fwd? s = some x) :
    ∃ i code, af.blocks[i]? = some (s, code) ∧ i ≠ 0 ∧ code.toList = [.inst (.jump x)] := by
  unfold AFunc.fwd? at h
  split at h
  · rename_i l code i hf
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [beq_iff_eq] at hp
    subst hp
    rw [List.mem_zipIdx_iff_getElem?] at hm
    have hi : (i == 0) = false := by
      cases e : (i == 0)
      · rfl
      · simp [e] at h
    simp only [hi, Bool.false_eq_true, ite_false] at h
    split at h
    · rename_i y hc
      split at h
      · cases h
      · cases h
        exact ⟨i, code, by simpa using hm, by simpa using hi, hc⟩
    · cases h
  · cases h

/-- A move's code is not empty and branches nowhere. -/
theorem moveInsts_shape {fr : RAFrame} {src dst : Loc} {l : List AInst}
    (h : fr.moveInsts src dst = .ok l) : l ≠ [] ∧ ∀ m, AInst.inst m ∈ l → m.targets = [] := by
  have hst : ∀ cls r off, ∀ m ∈ slotStoreAt cls r off, m.targets = [] := by
    intro cls r off m hm
    unfold slotStoreAt spAddrX16 at hm
    cases cls <;> split at hm <;> simp [slotStore] at hm <;>
      (try rcases hm with rfl | ⟨_, _, -, rfl⟩ | rfl | rfl) <;> (try subst hm) <;> rfl
  have hld : ∀ cls r off, ∀ m ∈ slotLoadAt cls r off, m.targets = [] := by
    intro cls r off m hm
    unfold slotLoadAt spAddrX16 at hm
    cases cls <;> split at hm <;> simp [slotLoad] at hm <;>
      (try rcases hm with rfl | ⟨_, _, -, rfl⟩ | rfl | rfl) <;> (try subst hm) <;> rfl
  have hst0 : ∀ cls r off, slotStoreAt cls r off ≠ [] := by
    intro cls r off; unfold slotStoreAt; split <;> simp
  have hld0 : ∀ cls r off, slotLoadAt cls r off ≠ [] := by
    intro cls r off; unfold slotLoadAt; split <;> simp
  unfold RAFrame.moveInsts at h
  split at h
  · split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine ⟨by simp, fun m hm => ?_⟩
      simp only [List.mem_singleton, AInst.inst.injEq] at hm
      subst hm; rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine ⟨by simp [hst0], fun m hm => ?_⟩
      simp only [List.mem_map, List.mem_append, AInst.inst.injEq] at hm
      obtain ⟨m', hm', rfl⟩ := hm
      rcases hm' with hm' | hm'
      · exact hst _ _ _ _ hm'
      · exact hld _ _ _ _ hm'
  all_goals (try simp only [bind, Except.bind] at h)
  all_goals first
    | cases h
    | (split at h
       · cases h
       · simp only [pure, Except.pure, Except.ok.injEq] at h
         subst h
         refine ⟨by simp [hst0, hld0], fun m hm => ?_⟩
         simp only [List.mem_map, AInst.inst.injEq] at hm
         obtain ⟨m', hm', rfl⟩ := hm
         first | exact hst _ _ _ _ hm' | exact hld _ _ _ _ hm')

/-- An item's code in a block without `Args`: not empty; a `jump` comes only from an `op` whose
instruction branches to the same block. -/
theorem itemCode_jump {fr : RAFrame} {vb : VBlock} {it : RItem} {c : List AInst}
    (hna : ∀ (k : Nat) (ds : List (Reg × Reg)), vb.insts[k]? ≠ some (MInst.args ds))
    (h : itemCode fr vb it = .ok c) :
    c ≠ [] ∧ ∀ x, AInst.inst (.jump x) ∈ c → ∃ k allocs regs i, it = .op k allocs ∧
      allocs = regs.map Loc.reg ∧ vb.insts[k]? = some i ∧ i.assign regs = .ok (.jump x) ∧
      i.targets = [x] ∧ c = [.inst (.jump x)] := by
  cases it with
  | move src dst =>
    have hm : fr.moveInsts src dst = .ok c := by
      simp only [itemCode, itemStep] at h
      cases hm : fr.moveInsts src dst with
      | error e => rw [hm] at h; cases h
      | ok l =>
        rw [hm] at h
        simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map,
          Except.ok.injEq] at h
        rw [← h]; simp
    obtain ⟨hne, htg⟩ := moveInsts_shape hm
    exact ⟨hne, fun x hx => by have := htg _ hx; simp [MInst.targets] at this⟩
  | op k allocs =>
    obtain ⟨regs, i, i', hal, hi, hasg, hc⟩ := itemCode_op h
    rcases hc with ⟨rfl, -, -⟩ | ⟨ds, rfl, rfl⟩ | ⟨us, rfl, rfl⟩
    · refine ⟨by simp, fun x hx => ?_⟩
      simp only [List.mem_singleton, AInst.inst.injEq] at hx
      subst hx
      have ht := (assign_shape hasg).1
      exact ⟨k, allocs, regs, i, rfl, hal, hi, hasg, by rw [← ht]; rfl, rfl⟩
    · obtain ⟨ds', rfl⟩ := (assign_shape hasg).2 ⟨ds, rfl⟩
      exact absurd hi (hna k ds')
    · exact ⟨by simp, fun x hx => by simp at hx⟩

theorem itemsCode_nil_of {fr : RAFrame} {vb : VBlock}
    (hna : ∀ (k : Nat) (ds : List (Reg × Reg)), vb.insts[k]? ≠ some (MInst.args ds)) :
    ∀ {its : List RItem}, itemsCode fr vb its = .ok [] → its = []
  | [], _ => rfl
  | it :: its, h => by
    obtain ⟨c1, c2, h1, -, he⟩ := itemsCode_cons h
    have := (itemCode_jump hna h1).1
    simp_all

/-- **The items of a block whose code is one `jump`** (a block without `Args`): one `op` of its
last instruction, which branches to the jump's target. -/
theorem items_jump {fr : RAFrame} {vb : VBlock} {cc : CheckCtx} {out : AState} {x : Label}
    (hna : ∀ (k : Nat) (ds : List (Reg × Reg)), vb.insts[k]? ≠ some (MInst.args ds))
    {its : List RItem} {n : Nat} {a : AState}
    (hrun : cc.runItems vb n its a = .ok out) (hc : itemsCode fr vb its = .ok [.inst (.jump x)]) :
    ∃ allocs regs i, its = [.op n allocs] ∧ allocs = regs.map Loc.reg ∧ vb.insts[n]? = some i ∧
      i.assign regs = .ok (.jump x) ∧ i.targets = [x] ∧ vb.insts.size = n + 1 := by
  cases its with
  | nil => simp [itemsCode, pure, Except.pure] at hc
  | cons it rest =>
    obtain ⟨c1, c2, h1, h2, he⟩ := itemsCode_cons hc
    obtain ⟨hne, hj⟩ := itemCode_jump hna h1
    obtain ⟨rfl, rfl⟩ : c1 = [.inst (.jump x)] ∧ c2 = [] := by
      obtain ⟨a0, c1', rfl⟩ := List.exists_cons_of_ne_nil hne
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp he.symm
      exact ⟨rfl, rfl⟩
    obtain ⟨k, allocs, regs, i, rfl, hal, hi, hasg, htg, -⟩ := hj x (by simp)
    obtain rfl := itemsCode_nil_of hna h2
    have hk : k = n ∧ vb.insts.size = n + 1 := by
      obtain ⟨-, hkn, _, _, _, _, _, _, h'⟩ := runItems_op hrun
      exact ⟨hkn, (runItems_nil h').1.symm⟩
    obtain ⟨rfl, hsz⟩ := hk
    exact ⟨allocs, regs, i, rfl, hal, hi, hasg, htg, hsz⟩

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

theorem cfg_target {vc : VCode} {ss ps : Array (Array Nat)} (h : vc.cfg = .ok (ss, ps)) {b : Nat}
    {vb : VBlock} (hvb : vc.blocks[b]? = some vb) {t : MInst} (ht : vb.insts.back? = some t)
    {j : Nat} {l : Label} (hl : t.targets[j]? = some l) :
    ∃ s vs, succOf vc b j = some s ∧ vc.blocks[s]? = some vs ∧ vs.label = l := by
  have h' := h
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
  · rename_i t0 ht0
    rw [ht] at ht0
    cases ht0
    split at hts
    · simp [throw, throwThe, MonadExceptOf.throw] at hts
    obtain ⟨-, hel'⟩ := array_mapM_ok hts
    obtain ⟨y, hy, hy'⟩ := hel' j l (by simpa using hl)
    split at hy
    · rename_i i hi
      simp only [pure, Except.pure, Except.ok.injEq] at hy
      subst hy
      obtain ⟨hlt, heq, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hi
      refine ⟨_, _, ?_, Array.getElem?_eq_getElem hlt, by simpa using heq⟩
      simp [succOf, h', hb, hy']
    · simp [throw, throwThe, MonadExceptOf.throw] at hy
  · simp [throw, throwThe, MonadExceptOf.throw] at hts

/-- **A forwarding block** (`fwd? s = some x`): a block other than the entry labelled `s`, whose
items are one `op` of its only instruction, a branch to its successor `bx` (other than the
entry, labelled `x`). -/
theorem RL.fwd_block {R : RL} (hR : R.Wf) {s x : Label} (h : R.af.fwd? s = some x) :
    ∃ b vb items allocs regs i bx vbx itx, R.vc.blocks[b]? = some vb ∧ vb.label = s ∧
      R.rf.blocks[b]? = some items ∧ b ≠ 0 ∧ items.toList = [.op 0 allocs] ∧
      allocs = regs.map Loc.reg ∧ vb.insts = #[i] ∧ i.assign regs = .ok (.jump x) ∧
      succOf R.vc b 0 = some bx ∧ R.vc.blocks[bx]? = some vbx ∧ vbx.label = x ∧
      R.rf.blocks[bx]? = some itx ∧ bx ≠ 0 := by
  obtain ⟨b, code, hab, hb0, hcode⟩ := fwd?_spec h
  obtain ⟨⟨-, -, hsz, hbl⟩, -, hck⟩ := lowerRFunc_ok hR.alloc
  obtain ⟨cc, ins, _, hcc, -⟩ := hR.check
  have hlt : b < R.af.blocks.size := (Array.getElem?_eq_some_iff.mp hab).1
  rw [hsz, Array.size_zip, hcc.size, Nat.min_self] at hlt
  obtain ⟨vb, hvb⟩ : ∃ vb, R.vc.blocks[b]? = some vb := ⟨_, Array.getElem?_eq_getElem hlt⟩
  obtain ⟨items, hit⟩ : ∃ it, R.rf.blocks[b]? = some it :=
    ⟨_, Array.getElem?_eq_getElem (by rw [hcc.size]; exact hlt)⟩
  obtain ⟨c, hc, ha⟩ := hbl b vb items hvb hit
  rw [hab] at ha
  simp only [hb0, ite_false, List.nil_append, Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨hl, rfl⟩ := ha
  simp only [List.toList_toArray] at hcode
  subst hcode
  have hna : ∀ (k : Nat) (ds : List (Reg × Reg)), vb.insts[k]? ≠ some (MInst.args ds) := fun k ds e =>
    hb0 (ctlCheck_args hck hvb e).1
  have hrunOf : ∀ (t : Nat) (vt : VBlock), R.vc.blocks[t]? = some vt →
      ∃ (its : Array RItem) (a out : AState),
      R.rf.blocks[t]? = some its ∧
      cc.runItems vt 0 its.toList a = .ok out := by
    intro t vt hvt
    obtain ⟨a, out, -, hrb, -⟩ :=
      verifyBlock_ok (hcc.blocks t (Array.getElem?_eq_some_iff.mp hvt).1)
    obtain ⟨vb', items', hvb', hit', hrun⟩ := runBlock_ok hrb
    rw [hcc.vc_eq, hvt] at hvb'
    cases hvb'
    rw [hcc.rf_eq] at hit'
    exact ⟨items', a, out, hit', hrun⟩
  obtain ⟨items', a, out, hit', hrun⟩ := hrunOf b vb hvb
  rw [hit] at hit'
  cases hit'
  obtain ⟨allocs, regs, i, hits, hal, hi, hasg, htg, hsz1⟩ := items_jump hna hrun hc
  have hins : vb.insts = #[i] := by
    apply Array.ext
    · simpa using hsz1
    · intro n h1 h2
      obtain rfl : n = 0 := by simp at h2; omega
      simpa using (Array.getElem?_eq_some_iff.mp hi).2
  obtain ⟨preds, hcfg⟩ := hcc.cfg
  have hback : vb.insts.back? = some i := by rw [hins]; rfl
  obtain ⟨bx, vbx, hsucc, hvbx, hlx⟩ := cfg_target hcfg hvb hback (j := 0) (by rw [htg]; rfl)
  obtain ⟨itx, -, -, hitx, -⟩ := hrunOf bx vbx hvbx
  exact ⟨b, vb, items, allocs, regs, i, bx, vbx, itx, hvb, hl.symm, hit, hb0, hits, hal, hins, hasg,
    hsucc, hvbx, hlx, hitx, ctlCheck_succ hck hsucc⟩

end Backend.Proof
