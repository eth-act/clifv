import FV.Backend.Proof.LSFacts
import FV.Backend.Proof.SpillLocal

/-!
# The all-spill plan: every instruction finds its scratch registers (V4b-4, #276)

With no vreg in a register (`Fn.spillPlan`: `regOf` is `none`, `occ` is empty), the builder's
step `Ctx.inst` succeeds (`spillPlan_inst_ok`): a register of `scratchOrder` is free as soon as
no entry of `taken` uses it, and the registers taken are the instruction's fixed registers and
clobbers plus at most one chosen register per scratch operand served so far. The invariant
`Inv` counts both (`cntT`: chosen registers of a class outside the fixed registers and clobbers,
`cntR`: scratch operands of the class not served yet) against `nScratch`; `OpsOk.enough` then
leaves a register of `freeRegs` unused whenever an operand is still to be served.
-/

namespace Backend.Proof.LS

open Backend Backend.LinearScan Backend.Proof Backend.Proof.Spill

/-! ## The all-spill plan -/

theorem spillPlan_regOf (fn : Fn) (v : Nat) : fn.spillPlan.regOf v = none := by
  simp only [Plan.regOf, Fn.spillPlan, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

private theorem foldl_id {α β : Type} (l : List α) (b : β) : l.foldl (fun acc _ => acc) b = b := by
  induction l generalizing b with
  | nil => rfl
  | cons _ _ ih => exact ih b

theorem spillPlan_occ (fn : Fn) (i : Nat) : fn.spillPlan.occ.getD i #[] = #[] := by
  simp only [Plan.occ, spillPlan_regOf, Option.bind_none, foldl_id, Array.getD_eq_getD_getElem?,
    Array.getElem?_map, Array.getElem?_replicate]
  split <;> simp [sortSegs]

theorem spillPlan_segFree_nil (s e : Nat) : segFree #[] s e = true := by
  simp [segFree, firstEndGe, firstEndGeIn]

/-- A register of `scratchOrder` that no entry of `taken` uses is free. -/
private theorem regFree_of {occ : Array (Array LinearScan.Seg)} (hocc : ∀ i, occ.getD i #[] = #[])
    {taken : List (Reg × Nat × Nat)} {r : Reg} {cl : RegClass} (hr : r ∈ scratchOrder cl)
    (hn : ∀ y ∈ taken, y.1 ≠ r) (s e : Nat) : regFree occ taken r s e = true := by
  obtain ⟨-, -, hi⟩ := scratchOrder_ok hr
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hi
  simp only [regFree, hi, hocc, spillPlan_segFree_nil, Bool.true_and, Bool.not_eq_true', List.any_eq_false]
  intro y hy
  obtain ⟨r', s', e'⟩ := y
  have := hn _ hy
  simp only [ne_eq] at this
  simp [this]

/-- `scratchReg` finds a register when one of `scratchOrder` is unused. -/
theorem spillPlan_scratch_some {occ : Array (Array LinearScan.Seg)} (hocc : ∀ i, occ.getD i #[] = #[])
    {taken : List (Reg × Nat × Nat)} {cl : RegClass} (h : ∃ r ∈ scratchOrder cl, ∀ y ∈ taken, y.1 ≠ r)
    (s e : Nat) : ∃ r, scratchReg occ taken cl s e [] = some r ∧ r ∈ scratchOrder cl := by
  obtain ⟨r, hr, hn⟩ := h
  unfold scratchReg
  cases hf : (scratchOrder cl).find? (fun r => !([] : List Reg).contains r && regFree occ taken r s e) with
  | none =>
    have := List.find?_eq_none.mp hf r hr
    simp [regFree_of hocc hr hn] at this
  | some r' => exact ⟨r', rfl, List.mem_of_find?_eq_some hf⟩

/-! ## Registers -/

private theorem spillPool_sub : ∀ {cl : RegClass} {r : Reg}, r ∈ spillPool cl → r ∈ scratchOrder cl := by
  intro cl
  cases cl <;> decide

private theorem spillPool_nodup : ∀ cl : RegClass, (spillPool cl).Nodup := by
  intro cl
  cases cl <;> decide

private theorem scratchOrder_disj : ∀ {cl cl' : RegClass} {r : Reg}, r ∈ scratchOrder cl →
    r ∈ scratchOrder cl' → cl = cl' := by
  have h : ∀ r ∈ scratchOrder .int, r ∉ scratchOrder .float := by decide
  intro cl cl' r h1 h2
  cases cl <;> cases cl'
  · rfl
  · exact absurd h2 (h r h1)
  · exact absurd h1 (h r h2)
  · rfl

/-! ## Counting -/

/-- The entries of `t` with a register of `scratchOrder cl` outside `F`. -/
private def cntT (F : List Reg) (t : List (Reg × Nat × Nat)) (cl : RegClass) : Nat :=
  (t.filter fun y => !F.contains y.1 && (scratchOrder cl).contains y.1).length

/-- The scratch operands of class `cl` without a register yet. -/
private def cntR (os : Array Operand) (R : Array (Option Reg)) (cl : RegClass) : Nat :=
  (os.toList.zipIdx.filter fun x => scratch x.1.con && x.1.cls == cl && (R.getD x.2 none).isNone).length

/-- **The counting invariant** of the passes (`F`: fixed registers and clobbers). -/
private def Inv (os : Array Operand) (F : List Reg) (R : Array (Option Reg))
    (t : List (Reg × Nat × Nat)) : Prop :=
  R.size = os.size ∧ ∀ cl, cntT F t cl + cntR os R cl ≤ nScratch cl os.toList

private theorem len_filter_le {α : Type} {p q : α → Bool} : ∀ (l : List α),
    (∀ x ∈ l, p x = true → q x = true) → (l.filter p).length ≤ (l.filter q).length
  | [], _ => Nat.le_refl _
  | y :: l, h => by
    have ih := len_filter_le l fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [List.filter_cons, List.filter_cons]
    by_cases hp : p y = true
    · simp only [hp, h y List.mem_cons_self hp, ite_true, List.length_cons]; omega
    · by_cases hq : q y = true
      · simp only [hp, hq, ite_true, Bool.false_eq_true, ite_false, List.length_cons]; omega
      · simp only [hp, hq, Bool.false_eq_true, ite_false]; omega

private theorem len_filter_lt {α : Type} {p q : α → Bool} {z : α} : ∀ (l : List α),
    (∀ x ∈ l, p x = true → q x = true) → z ∈ l → q z = true → p z = false →
    (l.filter p).length < (l.filter q).length
  | [], _, hz, _, _ => absurd hz List.not_mem_nil
  | y :: l, h, hz, hqz, hpz => by
    have hle := len_filter_le l fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [List.filter_cons, List.filter_cons]
    rcases List.mem_cons.mp hz with rfl | hz
    · simp only [hpz, hqz, ite_true, Bool.false_eq_true, ite_false, List.length_cons]; omega
    · have ih := len_filter_lt l (fun x hx => h x (List.mem_cons_of_mem _ hx)) hz hqz hpz
      by_cases hp : p y = true
      · simp only [hp, h y List.mem_cons_self hp, ite_true, List.length_cons]; omega
      · by_cases hq : q y = true
        · simp only [hp, hq, ite_true, Bool.false_eq_true, ite_false, List.length_cons]; omega
        · simp only [hp, hq, Bool.false_eq_true, ite_false]; omega

private theorem getD_set (R : Array (Option Reg)) (j k : Nat) (x : Reg) :
    (R.set! j (some x)).getD k none = if j = k ∧ j < R.size then some x else R.getD k none := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
  by_cases hjk : j = k
  · subst hjk
    by_cases hj : j < R.size
    · simp [hj]
    · simp [hj]
  · simp [hjk]

private theorem size_set (R : Array (Option Reg)) (j : Nat) (x : Option Reg) :
    (R.set! j x).size = R.size := by
  simp [Array.set!_eq_setIfInBounds]

private theorem isSome_set {R : Array (Option Reg)} {j k : Nat} {x : Reg}
    (h : (R.getD k none).isSome = true) : ((R.set! j (some x)).getD k none).isSome = true := by
  rw [getD_set]; split <;> simp_all

private theorem cntR_set_le (os : Array Operand) (R : Array (Option Reg)) (j : Nat) (x : Reg)
    (cl : RegClass) : cntR os (R.set! j (some x)) cl ≤ cntR os R cl := by
  refine len_filter_le _ fun y _ h => ?_
  simp only [Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  rw [getD_set] at h2
  split at h2
  · simp at h2
  · exact h2

private theorem cntR_set_lt {os : Array Operand} {R : Array (Option Reg)} {j : Nat} {o : Operand}
    (x : Reg) (hz : (o, j) ∈ os.toList.zipIdx) (hsc : scratch o.con = true)
    (hn : R.getD j none = none) (hj : j < R.size) :
    cntR os (R.set! j (some x)) o.cls < cntR os R o.cls := by
  refine len_filter_lt _ (fun y _ h => ?_) hz (by simp [hsc, hn]) (by simp [hj])
  simp only [Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  rw [getD_set] at h2
  split at h2
  · simp at h2
  · exact h2

private theorem cntT_cons_le (F : List Reg) (t : List (Reg × Nat × Nat)) (y : Reg × Nat × Nat)
    (cl : RegClass) : cntT F (y :: t) cl ≤ cntT F t cl + 1 := by
  unfold cntT; rw [List.filter_cons]; split <;> simp

private theorem cntT_cons_eq {F : List Reg} {t : List (Reg × Nat × Nat)} {y : Reg × Nat × Nat}
    {cl : RegClass} (h : (!F.contains y.1 && (scratchOrder cl).contains y.1) = false) :
    cntT F (y :: t) cl = cntT F t cl := by
  unfold cntT; simp only [List.filter_cons, h, Bool.false_eq_true, ite_false]

private theorem cntT_append_eq {F : List Reg} {t t' : List (Reg × Nat × Nat)}
    (h : ∀ y ∈ t', y.1 ∈ F) (cl : RegClass) : cntT F (t' ++ t) cl = cntT F t cl := by
  unfold cntT
  rw [List.filter_append, List.length_append]
  have : t'.filter (fun y => !F.contains y.1 && (scratchOrder cl).contains y.1) = [] :=
    List.filter_eq_nil_iff.mpr fun y hy => by simp [h y hy]
  rw [this, List.length_nil, Nat.zero_add]

private theorem Inv.set {os : Array Operand} {F : List Reg} {R : Array (Option Reg)}
    {t : List (Reg × Nat × Nat)} (hI : Inv os F R t) (j : Nat) (x : Reg) :
    Inv os F (R.set! j (some x)) t :=
  ⟨by rw [size_set]; exact hI.1, fun cl =>
    Nat.le_trans (Nat.add_le_add_left (cntR_set_le os R j x cl) _) (hI.2 cl)⟩

private theorem Inv.cons_fixed {os : Array Operand} {F : List Reg} {R : Array (Option Reg)}
    {t : List (Reg × Nat × Nat)} (hI : Inv os F R t) {y : Reg × Nat × Nat} (hy : y.1 ∈ F) :
    Inv os F R (y :: t) :=
  ⟨hI.1, fun cl => by rw [cntT_cons_eq (by simp [hy])]; exact hI.2 cl⟩

private theorem mem_zipIdx {os : Array Operand} {o : Operand} {j : Nat}
    (hz : (o, j) ∈ os.toList.zipIdx) : os[j]? = some o := by
  rw [← Array.getElem?_toList]; exact List.mem_zipIdx_iff_getElem?.mp hz

private theorem lt_of_zipIdx {os : Array Operand} {o : Operand} {j : Nat}
    (hz : (o, j) ∈ os.toList.zipIdx) : j < os.size :=
  (Array.getElem?_eq_some_iff.mp (mem_zipIdx hz)).1

private theorem mem_of_zipIdx {os : Array Operand} {o : Operand} {j : Nat}
    (hz : (o, j) ∈ os.toList.zipIdx) : o ∈ os.toList :=
  List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hz)

/-- Serving the scratch operand `j` with a register `r` of its class keeps the invariant. -/
private theorem Inv.scr {os : Array Operand} {F : List Reg} {R : Array (Option Reg)}
    {t : List (Reg × Nat × Nat)} (hI : Inv os F R t) {o : Operand} {j : Nat}
    (hz : (o, j) ∈ os.toList.zipIdx) (hsc : scratch o.con = true) (hn : R.getD j none = none)
    (x : Reg) {y : Reg × Nat × Nat} (hy : y.1 ∈ scratchOrder o.cls) :
    Inv os F (R.set! j (some x)) (y :: t) := by
  have hj : j < R.size := hI.1 ▸ lt_of_zipIdx hz
  refine ⟨by rw [size_set]; exact hI.1, fun cl => ?_⟩
  by_cases hcl : o.cls = cl
  · subst hcl
    have := cntT_cons_le F t y o.cls
    have := cntR_set_lt x hz hsc hn hj
    have := hI.2 o.cls
    omega
  · have he : cntT F (y :: t) cl = cntT F t cl := by
      refine cntT_cons_eq ?_
      have : (scratchOrder cl).contains y.1 = false := by
        rw [Bool.eq_false_iff]
        intro hc
        exact hcl (scratchOrder_disj hy (List.contains_iff_mem.mp hc))
      simp only [this, Bool.and_false]
    rw [he]
    exact Nat.le_trans (Nat.add_le_add_left (cntR_set_le os R j x cl) _) (hI.2 cl)

/-- **A register is left**: while a scratch operand is unserved, some register of its class's
`scratchOrder` is used by no entry of `taken`. -/
private theorem free_exists {os : Array Operand} {clob : List Reg} {R : Array (Option Reg)}
    {t : List (Reg × Nat × Nat)} (hok : OpsOk os clob) (hI : Inv os (fixedRegs os ++ clob) R t)
    {o : Operand} {j : Nat} (hz : (o, j) ∈ os.toList.zipIdx) (hsc : scratch o.con = true)
    (hn : R.getD j none = none) : ∃ r ∈ scratchOrder o.cls, ∀ y ∈ t, y.1 ≠ r := by
  have hpos : 0 < cntR os R o.cls :=
    List.length_pos_of_mem (List.mem_filter.mpr ⟨hz, by simp [hsc, hn]⟩)
  have hb := hI.2 o.cls
  have he := hok.enough o.cls
  cases hf : (freeRegs os clob o.cls).find? (fun r => !(t.any fun y => y.1 == r)) with
  | some r =>
    have hp := List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    refine ⟨r, spillPool_sub (List.mem_filter.mp hm).1, fun y hy hyr => ?_⟩
    have h1 : (t.any fun y => y.1 == r) = false := by simpa using hp
    have h2 := List.any_eq_false.mp h1 y hy
    simp [hyr] at h2
  | none =>
    exfalso
    have hsub : freeRegs os clob o.cls ⊆ (t.filter fun y =>
        !(fixedRegs os ++ clob).contains y.1 && (scratchOrder o.cls).contains y.1).map (·.1) := by
      intro r hr
      have hp := List.find?_eq_none.mp hf r hr
      have h1 : (t.any fun y => y.1 == r) = true := by simpa using hp
      obtain ⟨y, hy, hyr⟩ := List.any_eq_true.mp h1
      have hyr' : y.1 = r := beq_iff_eq.mp hyr
      subst hyr' 
      obtain ⟨hpool, hnf⟩ := List.mem_filter.mp hr
      refine List.mem_map_of_mem (List.mem_filter.mpr ⟨hy, ?_⟩)
      simp only [Bool.and_eq_true]
      exact ⟨hnf, List.contains_iff_mem.mpr (spillPool_sub hpool)⟩
    have hnd : (freeRegs os clob o.cls).Nodup := (spillPool_nodup o.cls).filter _
    have hlen := hnd.length_le_of_subset hsub
    simp only [List.length_map] at hlen
    unfold cntT at hb
    omega

/-! ## The passes on the all-spill plan -/

section
variable {c : LinearScan.Ctx}

private theorem loc_spill (hreg : ∀ v, c.pl.regOf v = none) (v : Nat) :
    c.loc v = .stack (c.pl.home.getD v 0) (c.fn.clsOf v) := by
  simp [LinearScan.Ctx.loc, Fn.loc, hreg]

private theorem fixedPass_fixed {g : Nat} {st : Nat → Operand → Bool} {o : Operand} {j : Nat}
    {rest : List (Operand × Nat)} {s : IS} {p : Reg} (hp : o.con = .fixed p) :
    ∃ s2 : IS, s2.R = s.R.set! j (some p) ∧
      s2.taken = (p, (opRange g o true).1, (opRange g o true).2) :: s.taken ∧
      c.fixedPass g st ((o, j) :: rest) s = c.fixedPass g st rest s2 := by
  simp only [LinearScan.Ctx.fixedPass, hp]
  refine ⟨_, ?_, ?_, rfl⟩ <;> split <;> (try split) <;> rfl

private theorem fixedPass_other {g : Nat} {st : Nat → Operand → Bool} {o : Operand} {j : Nat}
    {rest : List (Operand × Nat)} {s : IS} (hf : ∀ p, o.con ≠ .fixed p) (hs : o.con ≠ .stack) :
    c.fixedPass g st ((o, j) :: rest) s = c.fixedPass g st rest s := by
  simp only [LinearScan.Ctx.fixedPass]

/-- **The fixed pass** succeeds and keeps the invariant; it serves exactly the fixed operands. -/
private theorem fixed_ok {os : Array Operand} {clob : List Reg} (hok : OpsOk os clob)
    (g : Nat) (st : Nat → Operand → Bool) :
    ∀ (l : List (Operand × Nat)) (s : IS), (∀ x ∈ l, x ∈ os.toList.zipIdx) →
    Inv os (fixedRegs os ++ clob) s.R s.taken →
    ∃ s', c.fixedPass g st l s = .ok s' ∧ Inv os (fixedRegs os ++ clob) s'.R s'.taken ∧
      (∀ k, (s.R.getD k none).isSome = true → (s'.R.getD k none).isSome = true) ∧
      (∀ x ∈ l, ∀ p, x.1.con = .fixed p → (s'.R.getD x.2 none).isSome = true) ∧
      (∀ k, (s'.R.getD k none).isSome = true →
        (s.R.getD k none).isSome = true ∨ ∃ o p, os[k]? = some o ∧ o.con = .fixed p)
  | [], s, _, hI => ⟨s, rfl, hI, fun _ h => h, by simp, fun _ h => .inl h⟩
  | (o, j) :: rest, s, hl, hI => by
    have hz := hl _ List.mem_cons_self
    have hl' : ∀ x ∈ rest, x ∈ os.toList.zipIdx := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    cases hcon : o.con
    case fixed p =>
      obtain ⟨s2, hR2, ht2, he⟩ := fixedPass_fixed (c := c) (g := g) (st := st) (j := j)
        (rest := rest) (s := s) hcon
      have hpF : p ∈ fixedRegs os ++ clob := by
        refine List.mem_append_left _ (List.mem_filterMap.mpr ⟨o, mem_of_zipIdx hz, ?_⟩)
        simp [hcon]
      have hI2 : Inv os (fixedRegs os ++ clob) s2.R s2.taken := by
        rw [hR2, ht2]; exact (hI.set j p).cons_fixed hpF
      obtain ⟨s', h1, h2, h3, h4, h5⟩ := fixed_ok hok g st rest s2 hl' hI2
      have hj : j < s.R.size := hI.1 ▸ lt_of_zipIdx hz
      refine ⟨s', he.trans h1, h2, fun k hk => h3 k (hR2 ▸ isSome_set hk), fun x hx p' hp' => ?_,
        fun k hk => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact h3 _ (by rw [hR2, getD_set]; simp [hj])
        · exact h4 x hx p' hp'
      · rcases h5 k hk with hk | hk
        · rw [hR2, getD_set] at hk
          split at hk
          · rename_i hjk
            obtain ⟨rfl, -⟩ := hjk
            exact .inr ⟨o, p, mem_zipIdx hz, hcon⟩
          · exact .inl hk
        · exact .inr hk
    case stack => exact absurd hcon (hok.noStack o (mem_of_zipIdx hz))
    all_goals
      rw [fixedPass_other (by simp [hcon]) (by simp [hcon])]
      obtain ⟨s', h1, h2, h3, h4, h5⟩ := fixed_ok hok g st rest s hl' hI
      refine ⟨s', h1, h2, h3, fun x hx p hp => ?_, h5⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [hcon] at hp
      · exact h4 x hx p hp

private theorem reuseReg_spill (hreg : ∀ v, c.pl.regOf v = none) (g : Nat)
    (taken : List (Reg × Nat × Nat)) (cl : RegClass) (a b : Nat) :
    c.reuseReg g taken cl (c.loc a) (c.loc b) =
      match scratchReg c.occ taken cl (pos g 1) (pos g 4) [] with
      | some x => pure (x, true, true)
      | none => throw "no scratch register" := by
  simp only [LinearScan.Ctx.reuseReg, loc_spill hreg, locReg?]
  cases scratchReg c.occ taken cl (pos g 1) (pos g 4) [] <;> rfl

private theorem reusePass_reuse (hreg : ∀ v, c.pl.regOf v = none) {g : Nat}
    {st : Nat → Operand → Bool} {os : Array Operand} {o u : Operand} {j ui : Nat}
    {rest : List (Operand × Nat)} {s : IS} (hr : o.con = .reuse ui) (hu : os[ui]? = some u) {x : Reg}
    (hx : scratchReg c.occ s.taken o.cls (pos g 1) (pos g 4) [] = some x) :
    ∃ s2 : IS, s2.R = (s.R.set! j (some x)).set! ui (some x) ∧
      s2.taken = (x, pos g 1, pos g 4) :: s.taken ∧
      c.reusePass g st os ((o, j) :: rest) s = c.reusePass g st os rest s2 := by
  simp only [LinearScan.Ctx.reusePass, hr, hu, reuseReg_spill hreg, hx]
  exact ⟨_, rfl, rfl, rfl⟩

private theorem reusePass_other {g : Nat} {st : Nat → Operand → Bool} {os : Array Operand}
    {o : Operand} {j : Nat} {rest : List (Operand × Nat)} {s : IS} (hr : ∀ ui, o.con ≠ .reuse ui) :
    c.reusePass g st os ((o, j) :: rest) s = c.reusePass g st os rest s := by
  simp only [LinearScan.Ctx.reusePass]

/-- **The reuse pass** succeeds and keeps the invariant: the use a reuse def reuses is still
unserved when the def comes (it is reused once, and no other pass touched it). -/
private theorem reuse_ok (hreg : ∀ v, c.pl.regOf v = none) (hocc : ∀ i, c.occ.getD i #[] = #[])
    {os : Array Operand} {clob : List Reg} (hok : OpsOk os clob)
    (g : Nat) (st : Nat → Operand → Bool) :
    ∀ (l : List (Operand × Nat)) (s : IS), l.Sublist os.toList.zipIdx →
    Inv os (fixedRegs os ++ clob) s.R s.taken →
    (∀ x ∈ l, ∀ ui, x.1.con = .reuse ui → s.R.getD ui none = none) →
    ∃ s', c.reusePass g st os l s = .ok s' ∧ Inv os (fixedRegs os ++ clob) s'.R s'.taken ∧
      (∀ k, (s.R.getD k none).isSome = true → (s'.R.getD k none).isSome = true) ∧
      (∀ x ∈ l, ∀ ui, x.1.con = .reuse ui → (s'.R.getD x.2 none).isSome = true)
  | [], s, _, hI, _ => ⟨s, rfl, hI, fun _ h => h, by simp⟩
  | (o, j) :: rest, s, hl, hI, hU => by
    have hZnd : (os.toList.zipIdx).Nodup := by
      refine List.Pairwise.of_map (S := fun x y : Nat => x ≠ y) Prod.snd
        (fun a b h hab => h (hab ▸ rfl)) ?_
      rw [List.zipIdx_map_snd]; exact List.nodup_range'
    have hnd := List.nodup_cons.mp (hZnd.sublist hl)
    have hz : (o, j) ∈ os.toList.zipIdx := hl.subset List.mem_cons_self
    have hl' : rest.Sublist os.toList.zipIdx := (List.sublist_cons_self _ _).trans hl
    cases hcon : o.con
    case reuse ui =>
      have hj := List.mem_zipIdx_iff_getElem?.mp hz
      obtain ⟨hkd, -, oi, hoi, hik, hisc, hicl, huniq⟩ := hok.reuse j o ui hj hcon
      have hzi : (oi, ui) ∈ os.toList.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hoi
      have hn : s.R.getD ui none = none := hU (o, j) List.mem_cons_self ui hcon
      have hju : j ≠ ui := by
        rintro rfl
        rw [hj] at hoi; cases hoi
        rw [hkd] at hik; cases hik
      have hfree := free_exists hok hI hzi hisc hn
      rw [hicl] at hfree
      obtain ⟨x, hx, hxs⟩ := spillPlan_scratch_some hocc hfree (pos g 1) (pos g 4)
      obtain ⟨s2, hR2, ht2, he⟩ := reusePass_reuse (st := st) (j := j) (rest := rest) hreg hcon
        (mem_zipIdx hzi) hx
      have hj' : j < s.R.size := hI.1 ▸ lt_of_zipIdx hz
      have hn' : (s.R.set! j (some x)).getD ui none = none := by
        rw [getD_set]; simp [hju, hn]
      have hI2 : Inv os (fixedRegs os ++ clob) s2.R s2.taken := by
        rw [hR2, ht2]
        exact (hI.set j x).scr hzi hisc hn' x (y := (x, pos g 1, pos g 4)) (by rw [hicl]; exact hxs)
      have hU2 : ∀ x' ∈ rest, ∀ ui', x'.1.con = .reuse ui' → s2.R.getD ui' none = none := by
        rintro ⟨o', j'⟩ hx' ui' hr'
        have hj'' := List.mem_zipIdx_iff_getElem?.mp (hl'.subset hx')
        obtain ⟨-, -, oi', hoi', hik', -⟩ := hok.reuse j' o' ui' hj'' hr'
        have hne1 : ui ≠ ui' := by
          rintro rfl
          have := huniq j' o' hj'' hr'
          subst this
          rw [hj] at hj''; cases hj''
          exact hnd.1 hx'
        have hne2 : j ≠ ui' := by
          rintro rfl
          rw [hj] at hoi'; cases hoi'
          rw [hkd] at hik'; cases hik'
        rw [hR2, getD_set, getD_set]
        simp only [hne1, hne2, false_and, ite_false]
        exact hU _ (List.mem_cons_of_mem _ hx') ui' hr'
      obtain ⟨s', h1, h2, h3, h4⟩ := reuse_ok hreg hocc hok g st rest s2 hl' hI2 hU2
      refine ⟨s', he.trans h1, h2, fun k hk => h3 k (hR2 ▸ isSome_set (isSome_set hk)),
        fun x' hx' ui' hr' => ?_⟩
      rcases List.mem_cons.mp hx' with rfl | hx'
      · exact h3 _ (by rw [hR2, getD_set, getD_set]; simp [hj'])
      · exact h4 x' hx' ui' hr'
    all_goals
      rw [reusePass_other (by simp [hcon])]
      obtain ⟨s', h1, h2, h3, h4⟩ := reuse_ok hreg hocc hok g st rest s hl' hI
        (fun x hx => hU x (List.mem_cons_of_mem _ hx))
      refine ⟨s', h1, h2, h3, fun x hx ui hr => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [hcon] at hr
      · exact h4 x hx ui hr

private theorem scratchReg_mem {occ : Array (Array LinearScan.Seg)} {taken : List (Reg × Nat × Nat)}
    {cl : RegClass} {a b : Nat} {avoid : List Reg} {r : Reg}
    (h : scratchReg occ taken cl a b avoid = some r) : r ∈ scratchOrder cl :=
  List.mem_of_find?_eq_some h

private theorem usePass_skip {g : Nat} {os : Array Operand} {o : Operand} {j : Nat}
    {rest : List (Operand × Nat)} {s : IS}
    (h : ((s.R.getD j none).isSome || o.kind != .use) = true) :
    c.usePass g os ((o, j) :: rest) s = c.usePass g os rest s := by
  simp only [LinearScan.Ctx.usePass, h, ite_true]

private theorem usePass_lookup (hreg : ∀ v, c.pl.regOf v = none) {g : Nat} {os : Array Operand}
    {o : Operand} {j : Nat} {rest : List (Operand × Nat)} {s : IS}
    (h : ((s.R.getD j none).isSome || o.kind != .use) = false) {r : Reg}
    (hl : s.useScr.lookup o.vreg = some r) :
    ∃ s2 : IS, s2.R = s.R.set! j (some r) ∧ s2.taken = s.taken ∧
      c.usePass g os ((o, j) :: rest) s = c.usePass g os rest s2 := by
  simp only [LinearScan.Ctx.usePass, h, Bool.false_eq_true, ite_false, hreg, hl]
  refine ⟨_, ?_, ?_, rfl⟩ <;> rfl

private theorem usePass_scr (hreg : ∀ v, c.pl.regOf v = none) {g : Nat} {os : Array Operand}
    {o : Operand} {j : Nat} {rest : List (Operand × Nat)} {s : IS}
    (h : ((s.R.getD j none).isSome || o.kind != .use) = false)
    (hl : s.useScr.lookup o.vreg = none)
    (hne : ∀ a b, scratchReg c.occ s.taken o.cls a b [] ≠ none) :
    ∃ (s2 : IS) (r : Reg), r ∈ scratchOrder o.cls ∧ s2.R = s.R.set! j (some r) ∧
      (∃ y : Reg × Nat × Nat, y.1 = r ∧ s2.taken = y :: s.taken) ∧
      c.usePass g os ((o, j) :: rest) s = c.usePass g os rest s2 := by
  simp only [LinearScan.Ctx.usePass, h, Bool.false_eq_true, ite_false, hreg, hl]
  split
  · rename_i r hr
    exact ⟨_, r, scratchReg_mem hr, rfl, ⟨_, rfl, rfl⟩, rfl⟩
  · rename_i hr
    exact absurd hr (hne _ _)

private theorem defPass_skip {g : Nat} {st : Nat → Operand → Bool} {o : Operand} {j : Nat}
    {rest : List (Operand × Nat)} {s : IS} (h : (s.R.getD j none).isSome = true) :
    c.defPass g st ((o, j) :: rest) s = c.defPass g st rest s := by
  simp only [LinearScan.Ctx.defPass, h, ite_true]

private theorem defPass_scr (hreg : ∀ v, c.pl.regOf v = none) {g : Nat}
    {st : Nat → Operand → Bool} {o : Operand} {j : Nat} {rest : List (Operand × Nat)} {s : IS}
    (h : (s.R.getD j none).isSome = false)
    (hne : ∀ a b, scratchReg c.occ s.taken o.cls a b [] ≠ none) :
    ∃ (s2 : IS) (r : Reg), r ∈ scratchOrder o.cls ∧ s2.R = s.R.set! j (some r) ∧
      (∃ y : Reg × Nat × Nat, y.1 = r ∧ s2.taken = y :: s.taken) ∧
      c.defPass g st ((o, j) :: rest) s = c.defPass g st rest s2 := by
  simp only [LinearScan.Ctx.defPass, h, Bool.false_eq_true, ite_false, hreg]
  split
  · rename_i r hr
    exact ⟨_, r, scratchReg_mem hr, rfl, ⟨_, rfl, rfl⟩, rfl⟩
  · rename_i hr
    exact absurd hr (hne _ _)

/-- An unserved operand that is neither fixed nor a reuse def is a scratch operand. -/
private theorem scratch_of {o : Operand} (hf : ∀ p, o.con ≠ .fixed p) (hr : ∀ ui, o.con ≠ .reuse ui) :
    scratch o.con = true := by
  unfold scratch
  split
  · rename_i p hp; exact absurd hp (hf p)
  · rename_i ui hu; exact absurd hu (hr ui)
  · rfl

private theorem scratch_ne (hocc : ∀ i, c.occ.getD i #[] = #[]) {os : Array Operand}
    {clob : List Reg} (hok : OpsOk os clob) {R : Array (Option Reg)} {t : List (Reg × Nat × Nat)}
    (hI : Inv os (fixedRegs os ++ clob) R t) {o : Operand} {j : Nat}
    (hz : (o, j) ∈ os.toList.zipIdx) (hsc : scratch o.con = true) (hn : R.getD j none = none) :
    ∀ a b, scratchReg c.occ t o.cls a b [] ≠ none := fun a b h => by
  obtain ⟨r, hr, -⟩ := spillPlan_scratch_some hocc (free_exists hok hI hz hsc hn) a b
  rw [hr] at h; cases h

private theorem none_of {R : Array (Option Reg)} {j : Nat} (h : (R.getD j none).isSome = false) :
    R.getD j none = none := by
  cases h' : R.getD j none <;> simp_all

/-- **The use pass** succeeds and keeps the invariant. -/
private theorem use_ok (hreg : ∀ v, c.pl.regOf v = none) (hocc : ∀ i, c.occ.getD i #[] = #[])
    {os : Array Operand} {clob : List Reg} (hok : OpsOk os clob) (g : Nat) :
    ∀ (l : List (Operand × Nat)) (s : IS), (∀ x ∈ l, x ∈ os.toList.zipIdx) →
    Inv os (fixedRegs os ++ clob) s.R s.taken →
    (∀ x ∈ os.toList.zipIdx, ∀ p, x.1.con = .fixed p → (s.R.getD x.2 none).isSome = true) →
    ∃ s', c.usePass g os l s = .ok s' ∧ Inv os (fixedRegs os ++ clob) s'.R s'.taken ∧
      (∀ k, (s.R.getD k none).isSome = true → (s'.R.getD k none).isSome = true)
  | [], s, _, hI, _ => ⟨s, rfl, hI, fun _ h => h⟩
  | (o, j) :: rest, s, hl, hI, hfx => by
    have hz := hl _ List.mem_cons_self
    have hl' : ∀ x ∈ rest, x ∈ os.toList.zipIdx := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    cases hsk : ((s.R.getD j none).isSome || o.kind != .use)
    case true =>
      rw [usePass_skip hsk]
      exact use_ok hreg hocc hok g rest s hl' hI hfx
    case false =>
      simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hsk
      have hn := none_of hsk.1
      cases hlk : s.useScr.lookup o.vreg
      case some r =>
        obtain ⟨s2, hR2, ht2, he⟩ := usePass_lookup (g := g) (os := os) (o := o) (j := j) (rest := rest) hreg
          (by rw [hsk.1, hsk.2]; decide) hlk
        have hI2 : Inv os (fixedRegs os ++ clob) s2.R s2.taken := by
          rw [hR2, ht2]; exact hI.set j r
        obtain ⟨s', h1, h2, h3⟩ := use_ok hreg hocc hok g rest s2 hl' hI2
          (fun x hx p hp => hR2 ▸ isSome_set (hfx x hx p hp))
        exact ⟨s', he.trans h1, h2, fun k hk => h3 k (hR2 ▸ isSome_set hk)⟩
      case none =>
        have hsc : scratch o.con = true := scratch_of
          (fun p hp => by have := hfx _ hz p hp; rw [hn] at this; cases this)
          (fun ui hu => by
            have := (hok.reuse j o ui (List.mem_zipIdx_iff_getElem?.mp hz) hu).1
            rw [hsk.2] at this; cases this)
        obtain ⟨s2, r, hr, hR2, ⟨y, hy, ht2⟩, he⟩ := usePass_scr (g := g) (os := os) (o := o) (j := j) (rest := rest)
          hreg (by rw [hsk.1, hsk.2]; decide) hlk (scratch_ne hocc hok hI hz hsc hn)
        have hI2 : Inv os (fixedRegs os ++ clob) s2.R s2.taken := by
          rw [hR2, ht2]; exact hI.scr hz hsc hn r (hy ▸ hr)
        obtain ⟨s', h1, h2, h3⟩ := use_ok hreg hocc hok g rest s2 hl' hI2
          (fun x hx p hp => hR2 ▸ isSome_set (hfx x hx p hp))
        exact ⟨s', he.trans h1, h2, fun k hk => h3 k (hR2 ▸ isSome_set hk)⟩

/-- **The def pass** succeeds and keeps the invariant. -/
private theorem def_ok (hreg : ∀ v, c.pl.regOf v = none) (hocc : ∀ i, c.occ.getD i #[] = #[])
    {os : Array Operand} {clob : List Reg} (hok : OpsOk os clob) (g : Nat)
    (st : Nat → Operand → Bool) :
    ∀ (l : List (Operand × Nat)) (s : IS), (∀ x ∈ l, x ∈ os.toList.zipIdx) →
    Inv os (fixedRegs os ++ clob) s.R s.taken →
    (∀ x ∈ os.toList.zipIdx, ∀ p, x.1.con = .fixed p → (s.R.getD x.2 none).isSome = true) →
    (∀ x ∈ os.toList.zipIdx, ∀ ui, x.1.con = .reuse ui → (s.R.getD x.2 none).isSome = true) →
    ∃ s', c.defPass g st l s = .ok s'
  | [], s, _, _, _, _ => ⟨s, rfl⟩
  | (o, j) :: rest, s, hl, hI, hfx, hre => by
    have hz := hl _ List.mem_cons_self
    have hl' : ∀ x ∈ rest, x ∈ os.toList.zipIdx := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    cases hsk : (s.R.getD j none).isSome
    case true =>
      rw [defPass_skip hsk]
      exact def_ok hreg hocc hok g st rest s hl' hI hfx hre
    case false =>
      have hn := none_of hsk
      have hsc : scratch o.con = true := scratch_of
        (fun p hp => by have := hfx _ hz p hp; rw [hn] at this; cases this)
        (fun ui hu => by have := hre _ hz ui hu; rw [hn] at this; cases this)
      obtain ⟨s2, r, hr, hR2, ⟨y, hy, ht2⟩, he⟩ := defPass_scr (g := g) (st := st) (rest := rest)
        hreg hsk (scratch_ne hocc hok hI hz hsc hn)
      have hI2 : Inv os (fixedRegs os ++ clob) s2.R s2.taken := by
        rw [hR2, ht2]; exact hI.scr hz hsc hn r (hy ▸ hr)
      rw [he]
      exact def_ok hreg hocc hok g st rest s2 hl' hI2
        (fun x hx p hp => hR2 ▸ isSome_set (hfx x hx p hp))
        (fun x hx ui hu => hR2 ▸ isSome_set (hre x hx ui hu))

private theorem cntR_le (os : Array Operand) (R : Array (Option Reg)) (cl : RegClass) :
    cntR os R cl ≤ nScratch cl os.toList := by
  have h1 : cntR os R cl ≤ (os.toList.zipIdx.filter fun x => scratch x.1.con && x.1.cls == cl).length :=
    len_filter_le _ fun x _ h => by simp only [Bool.and_eq_true] at h ⊢; exact h.1
  have h2 : (os.toList.zipIdx.filter fun x => scratch x.1.con && x.1.cls == cl).length =
      nScratch cl os.toList := by
    unfold nScratch
    conv => rhs; rw [← List.zipIdx_map_fst 0 os.toList]
    rw [List.filter_map, List.length_map]; rfl
  omega

/-- **Every instruction builds** on a plan without registers. -/
theorem spillPlan_inst_ok (hreg : ∀ v, c.pl.regOf v = none) (hocc : ∀ i, c.occ.getD i #[] = #[])
    {g : Nat} (hok : OpsOk (c.fn.ops.getD g #[]) (c.fn.insts.getD g default).clobbers) :
    ∃ io, c.inst g = .ok io := by
  unfold LinearScan.Ctx.inst
  dsimp only
  generalize c.fn.ops.getD g #[] = os at hok ⊢
  generalize c.fn.insts.getD g default = i at hok ⊢
  generalize c.store g i.isTerminator (keptIdx i os) = st
  have hZ : ∀ x ∈ os.toList.zipIdx, x ∈ os.toList.zipIdx := fun _ hx => hx
  have hI0 : Inv os (fixedRegs os ++ i.clobbers) (Array.replicate os.size none) [] := by
    refine ⟨Array.size_replicate, fun cl => ?_⟩
    have : cntT (fixedRegs os ++ i.clobbers) [] cl = 0 := rfl
    rw [this, Nat.zero_add]
    exact cntR_le os _ cl
  obtain ⟨s1, h1, hI1, -, hfx1, hrf1⟩ := fixed_ok (c := c) hok g st os.toList.zipIdx
    { R := Array.replicate os.size none, taken := [], pre := [], post := [], useScr := [] } hZ hI0
  rw [h1]
  simp only [bind, Except.bind]
  have hI1' : Inv os (fixedRegs os ++ i.clobbers) s1.R
      (i.clobbers.map (fun r => (r, pos g 3, pos g 3)) ++ s1.taken) := by
    refine ⟨hI1.1, fun cl => ?_⟩
    rw [cntT_append_eq (fun y hy => ?_)]
    · exact hI1.2 cl
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
      exact List.mem_append_right _ hr
  have hU : ∀ x ∈ os.toList.zipIdx, ∀ ui, x.1.con = .reuse ui → s1.R.getD ui none = none := by
    rintro ⟨o, j⟩ hx ui hu
    obtain ⟨-, -, oi, hoi, -, hisc, -⟩ := hok.reuse j o ui (List.mem_zipIdx_iff_getElem?.mp hx) hu
    cases h : s1.R.getD ui none
    · rfl
    · rcases hrf1 ui (by simp [h]) with h' | ⟨o', p, ho', hp⟩
      · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at h'
        split at h' <;> simp at h'
      · rw [← Array.getElem?_toList, hoi] at ho'
        cases ho'
        rw [hp] at hisc
        cases hisc
  obtain ⟨s2, h2, hI2, hm2, hre2⟩ := reuse_ok (c := c) hreg hocc hok g st os.toList.zipIdx
    { s1 with taken := i.clobbers.map (fun r => (r, pos g 3, pos g 3)) ++ s1.taken }
    (List.Sublist.refl _) hI1' hU
  rw [h2]
  simp only
  have hfx2 : ∀ x ∈ os.toList.zipIdx, ∀ p, x.1.con = .fixed p → (s2.R.getD x.2 none).isSome = true :=
    fun x hx p hp => hm2 _ (hfx1 x hx p hp)
  obtain ⟨s3, h3, hI3, hm3⟩ := use_ok (c := c) hreg hocc hok g os.toList.zipIdx s2 hZ hI2 hfx2
  rw [h3]
  simp only
  obtain ⟨s4, h4⟩ := def_ok (c := c) hreg hocc hok g st os.toList.zipIdx s3 hZ hI3
    (fun x hx p hp => hm3 _ (hfx2 x hx p hp)) (fun x hx ui hu => hm3 _ (hre2 x hx ui hu))
  rw [h4]
  exact ⟨_, rfl⟩

end

end Backend.Proof.LS
