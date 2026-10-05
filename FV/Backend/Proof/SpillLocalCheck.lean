import FV.Backend.Proof.SpillLocal

/-!
# The checker's static checks accept the spill allocation of one instruction

`checkStatic_spill`: under `OpsOk`, `CheckCtx.checkStatic` accepts the locations `spillLocs`
computes. The locations are characterized first (`spillLocs_get`): a fixed operand's is its
register, a scratch operand's the next free register of its class (`scratchLoc`), a reuse
operand's that of the operand it reuses; two operands share a location only if both are fixed
to one register or one reuses the other (`loc_eq_cases`).
-/

namespace Backend.Proof.Spill

open Backend

/-! ## The fold -/

theorem nScratch_cons (c : RegClass) (o : Operand) (l : List Operand) :
    nScratch c (o :: l) = (if (scratch o.con && o.cls == c) = true then 1 else 0) + nScratch c l := by
  unfold nScratch
  rw [List.filter_cons]
  split <;> simp [Nat.add_comm]

theorem nScratch_append (c : RegClass) (l l' : List Operand) :
    nScratch c (l ++ l') = nScratch c l + nScratch c l' := by
  simp [nScratch, List.filter_append]

theorem byCls_drop (is fs : List Reg) (o : Operand) (c : RegClass) :
    byCls (is.drop (nScratch .int [o])) (fs.drop (nScratch .float [o])) c =
      (byCls is fs c).drop (nScratch c [o]) := by
  cases c <;> rfl

theorem sstep_eq (acc : Array Loc) (is fs : List Reg) (o : Operand) :
    sstep (acc, is, fs) o =
      (acc.push (baseLoc is fs [] o), is.drop (nScratch .int [o]), fs.drop (nScratch .float [o])) := by
  unfold sstep baseLoc
  rcases o with ⟨v, c, k, p, con⟩
  cases con <;> cases c <;> (try rfl) <;> (cases is <;> cases fs <;> rfl)

theorem fold_sstep : ∀ (L : List Operand) (acc : Array Loc) (is fs : List Reg),
    L.foldl sstep (acc, is, fs) =
      (acc ++ (L.mapIdx fun j o => baseLoc is fs (L.take j) o).toArray,
        is.drop (nScratch .int L), fs.drop (nScratch .float L))
  | [], acc, is, fs => by simp [nScratch]
  | o :: L, acc, is, fs => by
    rw [List.foldl_cons, sstep_eq, fold_sstep L]
    have hb : ∀ (j : Nat) (o' : Operand),
        baseLoc (is.drop (nScratch .int [o])) (fs.drop (nScratch .float [o])) (L.take j) o' =
          baseLoc is fs (o :: L.take j) o' := by
      intro j o'
      unfold baseLoc
      rw [byCls_drop, List.getElem?_drop, ← nScratch_append]
      rfl
    simp only [hb, List.mapIdx_cons, List.take_succ_cons, List.take_zero, List.drop_drop,
      ← nScratch_append, List.singleton_append]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp
    · simp only
    · simp only

/-- The base locations, by index. -/
theorem baseLocs_get (ops : Array Operand) (clob : List Reg) (j : Nat) :
    (baseLocs ops clob).toList[j]? = ops.toList[j]?.map fun o =>
      baseLoc (freeRegs ops clob .int) (freeRegs ops clob .float) (ops.toList.take j) o := by
  unfold baseLocs
  rw [← Array.foldl_toList, fold_sstep]
  simp [List.getElem?_mapIdx]

theorem baseLocs_get' (ops : Array Operand) (clob : List Reg) (j : Nat) :
    (baseLocs ops clob)[j]? = ops.toList[j]?.map fun o =>
      baseLoc (freeRegs ops clob .int) (freeRegs ops clob .float) (ops.toList.take j) o := by
  rw [← Array.getElem?_toList, baseLocs_get]

/-- The location `spillLocs` gives operand `j` (`o`). -/
def locOf (ops : Array Operand) (clob : List Reg) (j : Nat) (o : Operand) : Loc :=
  match o.con with
  | .reuse i => (ops.toList[i]?.map fun oi =>
      baseLoc (freeRegs ops clob .int) (freeRegs ops clob .float) (ops.toList.take i) oi).getD (.reg .sp)
  | _ => baseLoc (freeRegs ops clob .int) (freeRegs ops clob .float) (ops.toList.take j) o

theorem spillLocs_get (ops : Array Operand) (clob : List Reg) (j : Nat) :
    (spillLocs ops clob)[j]? = ops.toList[j]?.map (locOf ops clob j) := by
  rw [spillLocs_eq, Array.getElem?_map, Array.zip_eq_zipWith, Array.getElem?_zipWith', baseLocs_get',
    ← Array.getElem?_toList]
  cases h : ops.toList[j]? with
  | none => simp
  | some o =>
    simp only [Option.map_some, Option.bind_some]
    unfold locOf
    split <;> simp_all [baseLocs_get']

theorem spillLocs_size (ops : Array Operand) (clob : List Reg) :
    (spillLocs ops clob).size = ops.size := by
  have h := spillLocs_get ops clob
  rcases Nat.lt_trichotomy (spillLocs ops clob).size ops.size with hlt | heq | hlt
  · have := h (spillLocs ops clob).size
    rw [Array.getElem?_eq_none (Nat.le_refl _), List.getElem?_eq_getElem (by simpa using hlt)] at this
    simp at this
  · exact heq
  · have := h ops.size
    rw [Array.getElem?_eq_getElem hlt, List.getElem?_eq_none (by simp)] at this
    simp at this

/-! ## Registers -/

theorem pool_ok : ∀ (c : RegClass), ∀ r ∈ spillPool c, r.allocatable = true ∧ r.realClass? = some c
  | .int => by decide
  | .float => by decide

theorem pool_nodup : ∀ (c : RegClass), (spillPool c).Nodup
  | .int => by decide
  | .float => by decide

theorem mem_freeRegs {ops : Array Operand} {clob : List Reg} {c : RegClass} {r : Reg} :
    r ∈ freeRegs ops clob c ↔ r ∈ spillPool c ∧ r ∉ fixedRegs ops ∧ r ∉ clob := by
  simp [freeRegs, List.mem_filter, Bool.eq_false_iff]

theorem freeRegs_nodup (ops : Array Operand) (clob : List Reg) (c : RegClass) :
    (freeRegs ops clob c).Nodup := (pool_nodup c).filter _

theorem byCls_free (ops : Array Operand) (clob : List Reg) (c : RegClass) :
    byCls (freeRegs ops clob .int) (freeRegs ops clob .float) c = freeRegs ops clob c := by
  cases c <;> rfl

theorem mem_fixedRegs {ops : Array Operand} {o : Operand} {p : Reg} (ho : o ∈ ops.toList)
    (hp : o.con = .fixed p) : p ∈ fixedRegs ops := by
  unfold fixedRegs
  rw [List.mem_filterMap]
  exact ⟨o, ho, by rw [hp]⟩

/-! ## Scratch counts -/

theorem nScratch_take_succ {L : List Operand} {j : Nat} {o : Operand} (hj : L[j]? = some o) (c : RegClass) :
    nScratch c (L.take (j + 1)) =
      nScratch c (L.take j) + (if (scratch o.con && o.cls == c) = true then 1 else 0) := by
  rw [List.take_add_one, hj, nScratch_append]
  unfold nScratch
  rw [Option.toList_some, List.filter_cons]
  split <;> simp_all

theorem nScratch_take_mono {L : List Operand} {j j' : Nat} (h : j ≤ j') (c : RegClass) :
    nScratch c (L.take j) ≤ nScratch c (L.take j') := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← List.take_append_drop j (L.take (j + d)), List.take_take, Nat.min_eq_left (by omega),
    nScratch_append]
  omega

/-- A scratch operand at `j` counts before every later index. -/
theorem nScratch_lt {L : List Operand} {j j' : Nat} {o : Operand} (hj : L[j]? = some o)
    (hs : scratch o.con = true) (hlt : j < j') :
    nScratch o.cls (L.take j) < nScratch o.cls (L.take j') := by
  have h1 := nScratch_take_succ hj o.cls
  have h2 := nScratch_take_mono (L := L) (Nat.succ_le_of_lt hlt) o.cls
  simp only [hs, beq_self_eq_true, Bool.and_self, ite_true] at h1
  rw [Nat.succ_eq_add_one] at h2
  omega

theorem nScratch_take_le (L : List Operand) (j : Nat) (c : RegClass) :
    nScratch c (L.take j) ≤ nScratch c L := by
  conv => rhs; rw [← List.take_append_drop j L]
  rw [nScratch_append]; omega

/-! ## The location of each operand -/

variable {ops : Array Operand} {clob : List Reg}

theorem locOf_fixed {j : Nat} {o : Operand} {p : Reg} (hp : o.con = .fixed p) :
    locOf ops clob j o = .reg p := by
  unfold locOf baseLoc; rw [hp]

/-- A scratch operand's location: the next free register of its class. -/
theorem locOf_scratch (h : OpsOk ops clob) {j : Nat} {o : Operand} (hj : ops.toList[j]? = some o)
    (hs : scratch o.con = true) : ∃ r, (freeRegs ops clob o.cls)[nScratch o.cls (ops.toList.take j)]? =
      some r ∧ locOf ops clob j o = .reg r := by
  have hlt : nScratch o.cls (ops.toList.take j) < (freeRegs ops clob o.cls).length := by
    have := nScratch_lt hj hs (Nat.lt_succ_self j); rw [Nat.succ_eq_add_one] at this
    have h2 := nScratch_take_le ops.toList (j + 1) o.cls
    have h3 := h.enough o.cls
    omega
  refine ⟨_, List.getElem?_eq_getElem hlt, ?_⟩
  unfold locOf baseLoc
  rw [byCls_free, List.getElem?_eq_getElem hlt]
  rcases hc : o.con <;> simp_all [scratch]

/-- A reuse operand's location is that of the scratch use it reuses. -/
theorem locOf_reuse (h : OpsOk ops clob) {j : Nat} {o : Operand} {i : Nat}
    (hj : ops.toList[j]? = some o) (hr : o.con = .reuse i) :
    ∃ oi, ops.toList[i]? = some oi ∧ oi.kind = .use ∧ scratch oi.con = true ∧ oi.cls = o.cls ∧
      locOf ops clob j o = locOf ops clob i oi := by
  obtain ⟨-, -, oi, hi, hk, hs, hc, -⟩ := h.reuse j o i hj hr
  refine ⟨oi, hi, hk, hs, hc, ?_⟩
  have : locOf ops clob i oi = baseLoc (freeRegs ops clob .int) (freeRegs ops clob .float)
      (ops.toList.take i) oi := by
    unfold locOf; rcases hc' : oi.con <;> simp_all [scratch]
  rw [this]
  unfold locOf; rw [hr]; simp [hi]

/-- Every operand's location is an allocatable register of its class. -/
theorem locOf_reg (h : OpsOk ops clob) {j : Nat} {o : Operand} (hj : ops.toList[j]? = some o) :
    ∃ r, locOf ops clob j o = .reg r ∧ r.allocatable = true ∧ r.realClass? = some o.cls := by
  have hmem : o ∈ ops.toList := List.mem_of_getElem? hj
  have scr : ∀ {j : Nat} {o : Operand}, ops.toList[j]? = some o → scratch o.con = true →
      ∃ r, locOf ops clob j o = .reg r ∧ r.allocatable = true ∧ r.realClass? = some o.cls := by
    intro j o hj hs
    obtain ⟨r, hr, hl⟩ := locOf_scratch h hj hs
    have := (mem_freeRegs.mp (List.mem_of_getElem? hr)).1
    exact ⟨r, hl, pool_ok _ r this⟩
  rcases hc : o.con with _ | _ | _ | p | i
  · exact scr hj (by rw [hc]; rfl)
  · exact scr hj (by rw [hc]; rfl)
  · exact scr hj (by rw [hc]; rfl)
  · exact ⟨p, locOf_fixed hc, h.fixedReg o hmem p hc⟩
  · obtain ⟨oi, hi, -, hs, hcl, he⟩ := locOf_reuse h hj hc
    rw [he, ← hcl]
    exact scr hi hs

/-- Two scratch operands have distinct locations. -/
theorem scratch_ne (h : OpsOk ops clob) {j j' : Nat} {o o' : Operand} (hj : ops.toList[j]? = some o)
    (hj' : ops.toList[j']? = some o') (hs : scratch o.con = true) (hs' : scratch o'.con = true)
    (hne : j ≠ j') : locOf ops clob j o ≠ locOf ops clob j' o' := by
  intro he
  obtain ⟨r, hr, hl⟩ := locOf_scratch h hj hs
  obtain ⟨r', hr', hl'⟩ := locOf_scratch h hj' hs'
  rw [hl, hl'] at he
  cases he
  have hc := (pool_ok _ r (mem_freeRegs.mp (List.mem_of_getElem? hr)).1).2
  have hc' := (pool_ok _ r (mem_freeRegs.mp (List.mem_of_getElem? hr')).1).2
  have hcl : o.cls = o'.cls := Option.some.inj (hc.symm.trans hc')
  rw [← hcl] at hr'
  have hlt := (List.getElem?_eq_some_iff.mp hr).1
  have := ((freeRegs_nodup ops clob o.cls).getElem?_inj hlt).mp (hr.trans hr'.symm)
  rcases Nat.lt_or_gt_of_ne hne with hlt' | hlt'
  · have := nScratch_lt hj hs hlt'; omega
  · have := nScratch_lt hj' hs' hlt'; rw [← hcl] at this; omega

/-- A scratch operand's location is not a fixed register of the instruction. -/
theorem scratch_ne_fixed (h : OpsOk ops clob) {j j' : Nat} {o o' : Operand} {p : Reg}
    (hj : ops.toList[j]? = some o) (hj' : ops.toList[j']? = some o') (hs : scratch o.con = true)
    (hp : o'.con = .fixed p) : locOf ops clob j o ≠ locOf ops clob j' o' := by
  intro he
  obtain ⟨r, hr, hl⟩ := locOf_scratch h hj hs
  rw [hl, locOf_fixed hp] at he
  cases he
  exact (mem_freeRegs.mp (List.mem_of_getElem? hr)).2.1 (mem_fixedRegs (List.mem_of_getElem? hj') hp)

/-- A scratch operand's location is not clobbered. -/
theorem scratch_ne_clob (h : OpsOk ops clob) {j : Nat} {o : Operand} (hj : ops.toList[j]? = some o)
    (hs : scratch o.con = true) : ∀ r, locOf ops clob j o = .reg r → r ∉ clob := by
  intro r' he
  obtain ⟨r, hr, hl⟩ := locOf_scratch h hj hs
  rw [hl] at he; cases he
  exact (mem_freeRegs.mp (List.mem_of_getElem? hr)).2.2

/-- Every operand's location is a fixed register, a scratch operand's, or (a reuse operand's)
that of the scratch operand it reuses. -/
theorem loc_root (h : OpsOk ops clob) {j : Nat} {o : Operand} (hj : ops.toList[j]? = some o) :
    (∃ p, o.con = .fixed p) ∨ (scratch o.con = true) ∨
      ∃ i oi, o.con = .reuse i ∧ ops.toList[i]? = some oi ∧ scratch oi.con = true ∧
        oi.kind = .use ∧ locOf ops clob j o = locOf ops clob i oi := by
  rcases hc : o.con with _ | _ | _ | p | i
  any_goals exact .inr (.inl rfl)
  · exact .inl ⟨p, rfl⟩
  · obtain ⟨oi, hi, hk, hs, -, hl⟩ := locOf_reuse h hj hc
    exact .inr (.inr ⟨i, oi, rfl, hi, hs, hk, hl⟩)

/-- **Shared locations**: two operands share a location only if both are fixed to one register
or one reuses the other. -/
theorem loc_eq_cases (h : OpsOk ops clob) {j j' : Nat} {o o' : Operand}
    (hj : ops.toList[j]? = some o) (hj' : ops.toList[j']? = some o') (hne : j ≠ j')
    (he : locOf ops clob j o = locOf ops clob j' o') :
    (∃ p, o.con = .fixed p ∧ o'.con = .fixed p) ∨ o.con = .reuse j' ∨ o'.con = .reuse j := by
  rcases loc_root h hj with ⟨p, hp⟩ | hs | ⟨i, oi, hr, hi, hs, -, hl⟩ <;>
    rcases loc_root h hj' with ⟨p', hp'⟩ | hs' | ⟨i', oi', hr', hi', hs', -, hl'⟩
  · rw [locOf_fixed hp, locOf_fixed hp'] at he; cases he; exact .inl ⟨p, hp, hp'⟩
  · exact absurd he.symm (scratch_ne_fixed h hj' hj hs' hp)
  · rw [hl'] at he
    exact absurd he.symm (scratch_ne_fixed h hi' hj hs' hp)
  · exact absurd he (scratch_ne_fixed h hj hj' hs hp')
  · exact absurd he (scratch_ne h hj hj' hs hs' hne)
  · rw [hl'] at he
    by_cases hij : j = i'
    · subst hij; exact .inr (.inr hr')
    · exact absurd he (scratch_ne h hj hi' hs hs' hij)
  · rw [hl] at he
    exact absurd he (scratch_ne_fixed h hi hj' hs hp')
  · rw [hl] at he
    by_cases hij : i = j'
    · subst hij; exact .inr (.inl hr)
    · exact absurd he (scratch_ne h hi hj' hs hs' hij)
  · rw [hl, hl'] at he
    by_cases hii : i = i'
    · subst hii
      obtain ⟨-, -, -, -, -, -, -, hu⟩ := h.reuse j o i hj hr
      exact absurd (hu j' o' hj' hr') (Ne.symm hne)
    · exact absurd he (scratch_ne h hi hi' hs hs' hii)

/-! ## The static checks -/

theorem pairs_eq (ops : Array Operand) (clob : List Reg) :
    (ops.zip (spillLocs ops clob)).toList =
      ops.toList.zipIdx.map (fun x => (x.1, locOf ops clob x.2 x.1)) := by
  apply List.ext_getElem?
  intro n
  rw [Array.getElem?_toList, Array.zip_eq_zipWith, Array.getElem?_zipWith', spillLocs_get,
    List.getElem?_map, List.getElem?_zipIdx, ← Array.getElem?_toList]
  cases ops.toList[n]? <;> simp

theorem zipIdx_lt {α : Type} : ∀ (L : List α) (k : Nat), (L.zipIdx k).Pairwise (fun a b => a.2 < b.2)
  | [], _ => .nil
  | a :: L, k => by
    rw [List.zipIdx_cons, List.pairwise_cons]
    refine ⟨fun b hb => ?_, zipIdx_lt L (k + 1)⟩
    have := List.mem_zipIdx hb
    omega

theorem forM_ok {α : Type} {l : List α} {f : α → Except String Unit} (h : ∀ x ∈ l, f x = .ok ()) :
    l.forM f = .ok () := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.forM, h a List.mem_cons_self]
    exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem mem_zipIdx_get {L : List Operand} {o : Operand} {j : Nat} (h : (o, j) ∈ L.zipIdx) :
    L[j]? = some o := List.mem_zipIdx_iff_getElem?.mp h

/-- A def's location is not clobbered. -/
theorem def_not_clob (h : OpsOk ops clob) {j : Nat} {o : Operand} (hj : ops.toList[j]? = some o)
    (hd : o.kind = .def) : locOf ops clob j o ∉ clob.map Loc.reg := by
  intro hm
  obtain ⟨r, hr, he⟩ := List.mem_map.mp hm
  rcases loc_root h hj with ⟨p, hp⟩ | hs | ⟨i, oi, -, hi, hs, -, hl⟩
  · rw [locOf_fixed hp] at he
    exact h.fixedDefClob o (List.mem_of_getElem? hj) _ hd hp (by injection he with he; rw [← he]; exact hr)
  · exact scratch_ne_clob h hj hs r he.symm hr
  · rw [hl] at he
    exact scratch_ne_clob h hi hs r he.symm hr

/-- **The static checks accept the spill allocation** of an instruction meeting `OpsOk`. -/
theorem checkStatic_spill (c : CheckCtx) (w : String) (h : OpsOk ops clob) :
    c.checkStatic w ops (spillLocs ops clob) clob = .ok () := by
  have hL := pairs_eq ops clob
  -- the operand checks
  have hop : ∀ x ∈ (ops.zip (spillLocs ops clob)).toList.zipIdx,
      c.checkOperand w ops (spillLocs ops clob) x = .ok () := by
    rintro ⟨⟨o0, l0⟩, j⟩ hx
    have hx' := List.mem_zipIdx_iff_getElem?.mp hx
    rw [hL, List.getElem?_map, List.getElem?_zipIdx] at hx'
    simp only [Nat.zero_add] at hx'
    cases hj : ops.toList[j]? with
    | none => rw [hj] at hx'; cases hx'
    | some o =>
      rw [hj] at hx'
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hx'
      obtain ⟨rfl, rfl⟩ := hx'
      obtain ⟨r, hl, ha, hc⟩ := locOf_reg h hj
      unfold CheckCtx.checkOperand
      rcases hcon : o.con with _ | _ | _ | p | i
      · simp [ensure, hcon, hl, CheckCtx.locOk, Loc.cls?, hc, ha]; rfl
      · simp [ensure, hcon, hl, CheckCtx.locOk, Loc.cls?, hc, ha, Loc.isReg]; rfl
      · exact absurd hcon (h.noStack o (List.mem_of_getElem? hj))
      · rw [locOf_fixed hcon] at hl ⊢; injection hl with hl; subst hl
        simp [ensure, hcon, CheckCtx.locOk, Loc.cls?, hc, ha]; rfl
      · obtain ⟨oi, hi, hk, -, -, he⟩ := locOf_reuse h hj hcon
        have e1 : ops[i]? = some oi := by rw [← Array.getElem?_toList]; exact hi
        have e2 : (spillLocs ops clob)[i]? = some (Loc.reg r) := by
          rw [spillLocs_get, hi, ← hl, he]; rfl
        simp [ensure, hcon, e1, e2, hl, CheckCtx.locOk, Loc.cls?, hc, ha, hk, Loc.isReg]; rfl
  -- the operand–location pairs
  have hmem : ∀ x ∈ (ops.zip (spillLocs ops clob)).toList, ∃ j, ops.toList[j]? = some x.1 ∧
      x.2 = locOf ops clob j x.1 := by
    intro x hx
    rw [hL, List.mem_map] at hx
    obtain ⟨⟨o, j⟩, hy, rfl⟩ := hx
    exact ⟨j, mem_zipIdx_get hy, rfl⟩
  have hnodup : ((((ops.zip (spillLocs ops clob)).toList.filter (·.1.kind == .def))).map (·.2)).Nodup := by
    rw [hL, List.filter_map, List.map_map, List.Nodup, List.pairwise_map]
    refine ((zipIdx_lt ops.toList 0).filter _).imp_of_mem fun {a b} ha hb hlt he => ?_
    rcases a with ⟨o, j⟩
    rcases b with ⟨o', j'⟩
    rw [List.mem_filter] at ha hb
    have hj := mem_zipIdx_get ha.1
    have hj' := mem_zipIdx_get hb.1
    have hd : o.kind = .def := by simpa using ha.2
    have hd' : o'.kind = .def := by simpa using hb.2
    simp only [Function.comp] at he
    rcases loc_eq_cases h hj hj' (Nat.ne_of_lt hlt) he with ⟨p, hp, hp'⟩ | hr | hr
    · exact absurd (h.fixedDefs j j' o o' p hj hj' hd hd' hp hp') (Nat.ne_of_lt hlt)
    · obtain ⟨-, -, oi, hi, hk, -⟩ := h.reuse j o j' hj hr
      rw [hj'] at hi; cases hi; rw [hd'] at hk; cases hk
    · obtain ⟨-, -, oi, hi, hk, -⟩ := h.reuse j' o' j hj' hr
      rw [hj] at hi; cases hi; rw [hd] at hk; cases hk
  have hconf : ∀ x ∈ (ops.zip (spillLocs ops clob)).toList.filter (·.1.kind == .def),
      (!(defConflicts ((ops.zip (spillLocs ops clob)).toList.filter (·.1.kind == .use))
        (clob.map Loc.reg) x.1.pos).contains x.2) = true := by
    intro x hx
    rw [List.mem_filter] at hx
    obtain ⟨j, hj, hx2⟩ := hmem x hx.1
    have hd : x.1.kind = .def := by simpa using hx.2
    have hcl := def_not_clob h hj hd
    rw [← hx2] at hcl
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, List.contains_iff_mem]
    rcases hpos : x.1.pos
    · -- early def: a scratch register, not a use's
      simp only [defConflicts, List.mem_append, not_or]
      refine ⟨fun hu => ?_, hcl⟩
      obtain ⟨y, hy, hyl⟩ := List.mem_map.mp hu
      rw [List.mem_filter] at hy
      obtain ⟨j', hj', hy2⟩ := hmem y hy.1
      have hu' : y.1.kind = .use := by simpa using hy.2
      have hs := h.earlyDef x.1 (List.mem_of_getElem? hj) hd hpos
      have hne : j ≠ j' := by
        rintro rfl; rw [hj] at hj'; injection hj' with hj'; rw [← hj', hd] at hu'; cases hu'
      rw [hx2, hy2] at hyl
      rcases loc_eq_cases h hj hj' hne hyl.symm with ⟨p, hp, -⟩ | hr | hr
      · rw [hp] at hs; cases hs
      · rw [hr] at hs; cases hs
      · obtain ⟨hk, -⟩ := h.reuse j' y.1 j hj' hr
        rw [hk] at hu'; cases hu'
    · -- late def: no late uses
      simp only [defConflicts, List.mem_append, not_or]
      refine ⟨fun hu => ?_, hcl⟩
      obtain ⟨y, hy, -⟩ := List.mem_map.mp hu
      rw [List.mem_filter, List.mem_filter] at hy
      have hu' : y.1.kind = .use := by simpa using hy.1.2
      obtain ⟨j', hj', -⟩ := hmem y hy.1.1
      have := h.useEarly y.1 (List.mem_of_getElem? hj') hu'
      have hl : y.1.pos = .late := by simpa using hy.2
      rw [this] at hl; cases hl
  have hlate : ∀ x ∈ ((ops.zip (spillLocs ops clob)).toList.filter (·.1.kind == .use)).filter
      (·.1.pos == .late), False := by
    intro x hx
    rw [List.mem_filter, List.mem_filter] at hx
    obtain ⟨j, hj, -⟩ := hmem x hx.1.1
    have := h.useEarly x.1 (List.mem_of_getElem? hj) (by simpa using hx.1.2)
    have hl : x.1.pos = .late := by simpa using hx.2
    rw [this] at hl; cases hl
  unfold CheckCtx.checkStatic
  simp only [ensure, spillLocs_size, beq_self_eq_true, ite_true, forM_ok hop, hnodup, decide_true]
  rw [forM_ok (fun x hx => by simp only [hconf x hx, ite_true]; rfl),
    forM_ok (fun x hx => absurd (hlate x hx) id)]
  rfl

/-! ## The uses' locations (the loads in front of the instruction) -/

/-- Two uses in one location carry one vreg of one class. -/
theorem useEq (h : OpsOk ops clob) {j j' : Nat} {o o' : Operand}
    (hj : ops.toList[j]? = some o) (hj' : ops.toList[j']? = some o') (hu : o.kind = .use)
    (hu' : o'.kind = .use) (he : locOf ops clob j o = locOf ops clob j' o') :
    o.vreg = o'.vreg ∧ o.cls = o'.cls := by
  by_cases hne : j = j'
  · subst hne; rw [hj] at hj'; injection hj' with hj'; subst hj'; exact ⟨rfl, rfl⟩
  rcases loc_eq_cases h hj hj' hne he with ⟨p, hp, hp'⟩ | hr | hr
  · have m := List.mem_of_getElem? hj
    have m' := List.mem_of_getElem? hj'
    refine ⟨h.fixedUse o m o' m' p hu hu' hp hp', ?_⟩
    have := (h.fixedReg o m p hp).2
    rw [(h.fixedReg o' m' p hp').2] at this
    exact (Option.some.inj this).symm
  · obtain ⟨hk, -⟩ := h.reuse j o j' hj hr; rw [hk] at hu; cases hu
  · obtain ⟨hk, -⟩ := h.reuse j' o' j hj' hr; rw [hk] at hu'; cases hu'

/-- The use–location pairs of the spill allocation. -/
theorem mem_spillPairs {o : Operand} {l : Loc} (hx : (o, l) ∈ (ops.zip (spillLocs ops clob)).toList) :
    ∃ j, ops.toList[j]? = some o ∧ l = locOf ops clob j o := by
  rw [pairs_eq, List.mem_map] at hx
  obtain ⟨⟨o', j⟩, hy, he⟩ := hx
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨j, mem_zipIdx_get hy, rfl⟩

/-- **Uses of one location** in the spill allocation carry one vreg of one class (so the loads in
front of the instruction, in any order, leave every use's value in its location). -/
theorem spill_useEq (h : OpsOk ops clob) {o o' : Operand} {l : Loc}
    (hx : (o, l) ∈ (ops.zip (spillLocs ops clob)).toList)
    (hx' : (o', l) ∈ (ops.zip (spillLocs ops clob)).toList) (hu : o.kind = .use)
    (hu' : o'.kind = .use) : o.vreg = o'.vreg ∧ o.cls = o'.cls := by
  obtain ⟨j, hj, rfl⟩ := mem_spillPairs hx
  obtain ⟨j', hj', he⟩ := mem_spillPairs hx'
  exact useEq h hj hj' hu hu' he

/-- **Every location** of the spill allocation is an allocatable register of its operand's
class. -/
theorem spill_reg (h : OpsOk ops clob) {o : Operand} {l : Loc}
    (hx : (o, l) ∈ (ops.zip (spillLocs ops clob)).toList) :
    ∃ r, l = .reg r ∧ r.allocatable = true ∧ r.realClass? = some o.cls := by
  obtain ⟨j, hj, rfl⟩ := mem_spillPairs hx
  exact locOf_reg h hj

/-- A load (home slot into a register) passes `checkMove`. -/
theorem checkMove_load (c : CheckCtx) (w : String) {s : Nat} {cls : RegClass} {r : Reg}
    (hs : s < c.rf.spillSlots) (ha : r.allocatable = true) (hc : r.realClass? = some cls) :
    c.checkMove w (.stack s cls) (.reg r) = .ok () := by
  simp [CheckCtx.checkMove, CheckCtx.locOk, Loc.cls?, hs, ha, hc, ensure, Loc.isReg]; rfl

/-- A store (register into a home slot) passes `checkMove`. -/
theorem checkMove_store (c : CheckCtx) (w : String) {s : Nat} {cls : RegClass} {r : Reg}
    (hs : s < c.rf.spillSlots) (ha : r.allocatable = true) (hc : r.realClass? = some cls) :
    c.checkMove w (.reg r) (.stack s cls) = .ok () := by
  simp [CheckCtx.checkMove, CheckCtx.locOk, Loc.cls?, hs, ha, hc, ensure, Loc.isReg]; rfl

end Backend.Proof.Spill
