import FV.Backend.Proof.SpillLocalCheck

/-!
# The abstract-state effect of one spilled instruction (V4 (a), step 3)

Building blocks of the dataflow invariant (step 4), on the checker's abstract states:

* `runMoves_spec`: a list of moves into pairwise-compatible registers (`loadMoves`: the loads
  in front of an instruction) leaves each destination with its source's symbols and every
  location no move writes unchanged (`loads_run`);
* `transferOp_kept`: after `transferOp` a kept def's location holds exactly its vreg;
  `transferOp_nonReg`: a location that is not a register only loses the defs' vregs.
-/

namespace Backend.Proof.Spill

open Backend

/-! ## `AState` basics -/

theorem index_inj {l l' : Loc} {i : Nat} (h : l.index = some i) (h' : l'.index = some i) : l = l' := by
  unfold Loc.index at h h'
  split at h <;> split at h' <;> (try split at h) <;> (try split at h') <;> simp_all <;> omega

theorem get_put_self {a : AState} {l : Loc} {i : Nat} (hi : l.index = some i) (hlt : i < a.size)
    (s : List Sym) : (a.put l s).get l = s := by
  simp [AState.get, AState.put, hi, Array.getD_eq_getD_getElem?, hlt]

theorem get_put_ne {a : AState} {l l' : Loc} (hne : l ≠ l') (s : List Sym) :
    (a.put l s).get l' = a.get l' := by
  unfold AState.get AState.put
  cases hi : l.index with
  | none => rfl
  | some i =>
    cases hi' : l'.index with
    | none => rfl
    | some i' =>
      have : i ≠ i' := fun e => hne (index_inj hi (e ▸ hi'))
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne this]

theorem size_put (a : AState) (l : Loc) (s : List Sym) : (a.put l s).size = a.size := by
  unfold AState.put; split <;> simp

theorem get_remove (a : AState) (s : Sym) (l : Loc) :
    (a.remove s).get l = (a.get l).filter (· != s) := by
  unfold AState.get AState.remove
  split
  · simp [Array.getD_eq_getD_getElem?]; cases a[‹Nat›]? <;> rfl
  · rfl

theorem size_remove (a : AState) (s : Sym) : (a.remove s).size = a.size := by simp [AState.remove]

/-- An allocatable register's index is below 64. -/
theorem reg_index_all : aarch64Env.allocatable.all (fun r => match (Loc.reg r).index with
    | some i => decide (i < 64)
    | none => false) = true := by decide

theorem reg_index {r : Reg} (h : r.allocatable = true) : ∃ i, (Loc.reg r).index = some i ∧ i < 64 := by
  have hm : r ∈ aarch64Env.allocatable := List.contains_iff_mem.mp h
  have := List.all_eq_true.mp reg_index_all r hm
  revert this
  cases (Loc.reg r).index with
  | some i => intro h; exact ⟨i, rfl, by simpa using h⟩
  | none => intro h; cases h

/-! ## Moves -/

/-- Moves run by the checker, in order. -/
def runMoves (c : CheckCtx) (w : String) : List (Loc × Loc) → AState → Except String AState
  | [], a => .ok a
  | m :: ms, a => do let a ← c.stepMove w m.1 m.2 a; runMoves c w ms a

/-- **Moves into registers**: if every move passes `checkMove`, writes an allocatable register
from a location that is not a register, and moves into one register share their source, then
each destination ends with its source's symbols and every location no move writes keeps its
symbols. -/
theorem runMoves_spec (c : CheckCtx) (w : String) : ∀ (ms : List (Loc × Loc)) (a : AState),
    (∀ m ∈ ms, c.checkMove w m.1 m.2 = .ok ()) →
    (∀ m ∈ ms, ∃ r, m.2 = .reg r ∧ r.allocatable = true) → (∀ m ∈ ms, m.1.isReg = false) →
    (∀ m ∈ ms, ∀ m' ∈ ms, m.2 = m'.2 → m.1 = m'.1) → 64 ≤ a.size →
    ∃ a', runMoves c w ms a = .ok a' ∧ a'.size = a.size ∧ (∀ m ∈ ms, a'.get m.2 = a.get m.1) ∧
      ∀ l, (∀ m ∈ ms, m.2 ≠ l) → a'.get l = a.get l
  | [], a, _, _, _, _, _ => ⟨a, rfl, rfl, by simp, fun _ _ => rfl⟩
  | m :: ms, a, hc, hd, hs, hf, hsz => by
    have hcm := hc m List.mem_cons_self
    obtain ⟨r, hr, hra⟩ := hd m List.mem_cons_self
    obtain ⟨i, hi, hi64⟩ := reg_index hra
    obtain ⟨a1, ha1⟩ : ∃ a1, a1 = a.put m.2 (a.get m.1) := ⟨_, rfl⟩
    have hsz1 : a1.size = a.size := ha1 ▸ size_put _ _ _
    -- the first move keeps every other location, in particular the non-register sources
    have keep : ∀ l, l ≠ m.2 → a1.get l = a.get l := fun l hl => ha1 ▸ get_put_ne (Ne.symm hl) _
    obtain ⟨a', hrun, hsz', hget, hkeep⟩ := runMoves_spec c w ms a1
      (fun m' h => hc m' (List.mem_cons_of_mem _ h)) (fun m' h => hd m' (List.mem_cons_of_mem _ h))
      (fun m' h => hs m' (List.mem_cons_of_mem _ h))
      (fun m' h m'' h' => hf m' (List.mem_cons_of_mem _ h) m'' (List.mem_cons_of_mem _ h'))
      (by omega)
    have srcKeep : ∀ m' ∈ m :: ms, a1.get m'.1 = a.get m'.1 := by
      intro m' hm'
      apply keep
      intro he
      have := hs m' hm'
      rw [he, hr] at this
      cases this
    refine ⟨a', ?_, by omega, ?_, ?_⟩
    · simp only [runMoves, CheckCtx.stepMove, hcm, bind, Except.bind, pure, Except.pure]
      rw [← ha1]; exact hrun
    · intro m' hm'
      rcases List.mem_cons.mp hm' with rfl | hm'
      · by_cases hin : ∃ m'' ∈ ms, m''.2 = m'.2
        · obtain ⟨m'', hm'', he⟩ := hin
          rw [← he, hget m'' hm'', srcKeep m'' (List.mem_cons_of_mem _ hm''),
            hf m'' (List.mem_cons_of_mem _ hm'') m' List.mem_cons_self he]
        · rw [hkeep m'.2 (fun m'' hm'' he => hin ⟨m'', hm'', he⟩), ha1,
            get_put_self (hr ▸ hi) (by omega)]
      · rw [hget m' hm', srcKeep m' (List.mem_cons_of_mem _ hm')]
    · intro l hl
      rw [hkeep l (fun m' hm' => hl m' (List.mem_cons_of_mem _ hm')),
        keep l (fun he => hl m List.mem_cons_self he.symm)]

/-- The loads in front of an instruction (`spillInst`): each use's home into its location. -/
def loadMoves (hm : Homes) (ops : Array Operand) (clob : List Reg) : List (Loc × Loc) :=
  ((ops.zip (spillLocs ops clob)).toList.filter (·.1.kind == .use)).map
    fun (o, l) => (spillHome hm o.vreg o.cls, l)

/-- **The loads**: each use's location then holds its home's symbols; every location that is
not a register is unchanged. -/
theorem loads_run (c : CheckCtx) (w : String) {hm : Homes} {ops : Array Operand} {clob : List Reg}
    (hok : OpsOk ops clob)
    (hslot : ∀ o ∈ ops.toList, o.kind = .use → hm.getD (o.vreg, o.cls) 0 < c.rf.spillSlots)
    {a : AState} (hsz : 64 ≤ a.size) :
    ∃ a', runMoves c w (loadMoves hm ops clob) a = .ok a' ∧ a'.size = a.size ∧
      (∀ o l, (o, l) ∈ (ops.zip (spillLocs ops clob)).toList → o.kind = .use →
        a'.get l = a.get (spillHome hm o.vreg o.cls)) ∧
      ∀ l, l.isReg = false → a'.get l = a.get l := by
  have mem : ∀ m ∈ loadMoves hm ops clob, ∃ o, (o, m.2) ∈ (ops.zip (spillLocs ops clob)).toList ∧
      o.kind = .use ∧ m.1 = spillHome hm o.vreg o.cls := by
    intro m hm'
    simp only [loadMoves, List.mem_map, List.mem_filter] at hm'
    obtain ⟨⟨o, l⟩, ⟨hx, hk⟩, rfl⟩ := hm'
    exact ⟨o, hx, by simpa using hk, rfl⟩
  obtain ⟨a', hrun, hsz', hget, hkeep⟩ := runMoves_spec c w (loadMoves hm ops clob) a
    (fun m hm' => by
      obtain ⟨o, hx, hk, h1⟩ := mem m hm'
      obtain ⟨r, hr, ha, hc⟩ := spill_reg hok hx
      obtain ⟨j, hj, -⟩ := mem_spillPairs hx
      rw [h1, hr]
      exact checkMove_load c w (hslot o (List.mem_of_getElem? hj) hk) ha hc)
    (fun m hm' => by
      obtain ⟨o, hx, -, -⟩ := mem m hm'
      obtain ⟨r, hr, ha, -⟩ := spill_reg hok hx
      exact ⟨r, hr, ha⟩)
    (fun m hm' => by obtain ⟨o, -, -, h1⟩ := mem m hm'; rw [h1]; rfl)
    (fun m hm' m' hm'' he => by
      obtain ⟨o, hx, hk, h1⟩ := mem m hm'
      obtain ⟨o', hx', hk', h1'⟩ := mem m' hm''
      rw [he] at hx
      obtain ⟨e1, e2⟩ := spill_useEq hok hx hx' hk hk'
      rw [h1, h1', e1, e2])
    hsz
  refine ⟨a', hrun, hsz', fun o l hx hk => ?_, fun l hl => hkeep l fun m hm' he => ?_⟩
  · have hmem : (spillHome hm o.vreg o.cls, l) ∈ loadMoves hm ops clob := by
      simp only [loadMoves, List.mem_map, List.mem_filter]
      exact ⟨(o, l), ⟨hx, by simpa using hk⟩, rfl⟩
    exact hget _ hmem
  · obtain ⟨o, hx, -, -⟩ := mem m hm'
    obtain ⟨r, hr, -, -⟩ := spill_reg hok hx
    rw [← he, hr] at hl
    cases hl

/-! ## The instruction's transfer -/

theorem inj_of_nodup_map {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup →
    ∀ {x y : α}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by cases hx
  | a :: l, h, x, y, hx, hy, he => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hx with h1 | h1 <;> rcases List.mem_cons.mp hy with h2 | h2
    · exact h1.trans h2.symm
    · subst h1; exact absurd (he ▸ List.mem_map_of_mem h2) h.1
    · subst h2; exact absurd (he.symm ▸ List.mem_map_of_mem h1) h.1
    · exact inj_of_nodup_map h.2 h1 h2 he

/-- `defineAll` at a location none of the defs writes: the defs' vregs leave it. -/
theorem defineAll_get_other : ∀ (ds : List (Operand × Loc)) (a : AState) (l : Loc),
    (∀ x ∈ ds, x.2 ≠ l) →
    (defineAll a ds).get l = (a.get l).filter fun s => !(ds.any fun x => s == .vreg x.1.vreg)
  | [], a, l, _ => by simp only [defineAll, List.foldl_nil, List.any_nil, Bool.not_false]; exact (List.filter_eq_self.mpr fun _ _ => rfl).symm
  | x :: ds, a, l, h => by
    have ih := defineAll_get_other ds (a.define x.2 (.vreg x.1.vreg)) l
      (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [defineAll, List.foldl_cons] at ih ⊢
    rw [ih, AState.define, get_put_ne (h x List.mem_cons_self), get_remove, List.filter_filter]
    congr 1; funext s
    first | rfl | simp [bne, Bool.and_comm]

theorem size_defineAll : ∀ (ds : List (Operand × Loc)) (a : AState), (defineAll a ds).size = a.size
  | [], _ => rfl
  | x :: ds, a => by
    have := size_defineAll ds (a.define x.2 (.vreg x.1.vreg))
    simp only [defineAll, List.foldl_cons] at this ⊢
    rw [this, AState.define, size_put, size_remove]

/-- `defineAll` with distinct register locations and distinct vregs: each def's location holds
exactly its vreg. -/
theorem defineAll_get_mem : ∀ (ds : List (Operand × Loc)) (a : AState),
    (ds.map (·.2)).Nodup → (ds.map (·.1.vreg)).Nodup →
    (∀ x ∈ ds, ∃ i, x.2.index = some i ∧ i < a.size) →
    ∀ x ∈ ds, (defineAll a ds).get x.2 = [.vreg x.1.vreg]
  | [], _, _, _, _, x, hx => by cases hx
  | y :: ds, a, hl, hv, hi, x, hx => by
    rw [List.map_cons, List.nodup_cons] at hl hv
    simp only [defineAll, List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · have := defineAll_get_other ds (a.define x.2 (.vreg x.1.vreg)) x.2
        (fun z hz he => hl.1 (he ▸ List.mem_map_of_mem hz))
      simp only [defineAll] at this
      obtain ⟨i, hi1, hi2⟩ := hi x List.mem_cons_self
      rw [this, AState.define, get_put_self hi1 (by rw [size_remove]; exact hi2)]
      simp only [List.filter_cons, List.filter_nil]
      have : (ds.any fun z => Sym.vreg x.1.vreg == .vreg z.1.vreg) = false := by
        rw [Bool.eq_false_iff]
        intro hany
        obtain ⟨z, hz, hze⟩ := List.any_eq_true.mp hany
        simp at hze
        exact hv.1 (hze ▸ List.mem_map_of_mem hz)
      simp [this]
    · have := defineAll_get_mem ds (a.define y.2 (.vreg y.1.vreg)) hl.2 hv.2
        (fun z hz => by
          obtain ⟨i, h1, h2⟩ := hi z (List.mem_cons_of_mem _ hz)
          exact ⟨i, h1, by rw [AState.define, size_put, size_remove]; exact h2⟩) x hx
      simpa [defineAll] using this

theorem clobberAll_get_other : ∀ (clob : List Reg) (a : AState) (l : Loc), (∀ r ∈ clob, Loc.reg r ≠ l) →
    (clobberAll a clob).get l = a.get l
  | [], _, _, _ => rfl
  | r :: clob, a, l, h => by
    have := clobberAll_get_other clob (a.put (.reg r) ((a.get (.reg r)).filter (· == .entry r))) l
      (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
    simp only [clobberAll, List.foldl_cons] at this ⊢
    rw [this, get_put_ne (h r List.mem_cons_self)]

theorem size_clobberAll : ∀ (b : AState) (clob : List Reg), (clobberAll b clob).size = b.size := by
  intro b clob
  induction clob generalizing b with
  | nil => rfl
  | cons r rs ih =>
    have := ih (b.put (.reg r) ((b.get (.reg r)).filter (· == .entry r)))
    simp only [clobberAll, List.foldl_cons] at this ⊢
    rw [this, size_put]

theorem forgetDefs_get (a : AState) (ps : List (Operand × Loc)) (l : Loc) :
    (forgetDefs a ps).get l =
      (a.get l).filter fun s => !(ps.any fun p => p.1.kind == .def && s == .vreg p.1.vreg) := by
  unfold AState.get forgetDefs
  split
  · simp [Array.getD_eq_getD_getElem?]; cases a[‹Nat›]? <;> rfl
  · rfl

theorem mem_atPos {ps : List (Operand × Loc)} {k : OpKind} {p : OpPos} {x : Operand × Loc} :
    x ∈ atPos ps k p ↔ x ∈ ps ∧ x.1.kind = k ∧ x.1.pos = p := by
  rcases x with ⟨o, l⟩
  simp [atPos]

theorem atPos_sublist (ps : List (Operand × Loc)) (p : OpPos) :
    (atPos ps .def p).Sublist (ps.filter (·.1.kind == .def)) := by
  have : atPos ps .def p = (ps.filter (·.1.kind == .def)).filter (·.1.pos == p) := by
    rw [List.filter_filter]
    unfold atPos
    congr 1
    funext x; rcases x with ⟨o, l⟩; simp [Bool.and_comm]
  rw [this]
  exact List.filter_sublist

variable {ops : Array Operand} {clob : List Reg}

/-- The defs' locations are pairwise distinct. -/
theorem spill_defLocs_nodup (h : OpsOk ops clob) :
    ((((ops.zip (spillLocs ops clob)).toList.filter (·.1.kind == .def))).map (·.2)).Nodup := by
  rw [pairs_eq, List.filter_map, List.map_map, List.Nodup, List.pairwise_map]
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
    rw [hj'] at hi; injection hi with hi; rw [← hi, hd'] at hk; cases hk
  · obtain ⟨-, -, oi, hi, hk, -⟩ := h.reuse j' o' j hj' hr
    rw [hj] at hi; injection hi with hi; rw [← hi, hd] at hk; cases hk

/-- The defs' vregs are pairwise distinct. -/
theorem spill_defVregs_nodup (h : OpsOk ops clob) :
    ((((ops.zip (spillLocs ops clob)).toList.filter (·.1.kind == .def))).map (·.1.vreg)).Nodup := by
  have hfst : (ops.zip (spillLocs ops clob)).toList.map Prod.fst = ops.toList := by
    rw [pairs_eq, List.map_map]; exact List.zipIdx_map_fst 0 _
  have : (((ops.zip (spillLocs ops clob)).toList.filter (·.1.kind == .def))).map (·.1.vreg) =
      (ops.toList.filter (·.kind == .def)).map (·.vreg) := by
    rw [← hfst, List.filter_map, List.map_map]; rfl
  rw [this]; exact h.defsNodup

/-- **A kept def's location holds exactly its vreg after the instruction's transfer.** -/
theorem transferOp_kept {i : MInst} (h : OpsOk ops i.clobbers) {a : AState} (hsz : 64 ≤ a.size)
    {o : Operand} {l : Loc} (hk : (o, l) ∈ keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList) :
    (transferOp i (ops.zip (spillLocs ops i.clobbers)).toList a).get l = [.vreg o.vreg] := by
  generalize hP : (ops.zip (spillLocs ops i.clobbers)).toList = P at hk
  have hDl := spill_defLocs_nodup h
  have hDv := spill_defVregs_nodup h
  rw [hP] at hDl hDv
  set_option linter.unusedVariables false in
  have hD : (o, l) ∈ P.filter (·.1.kind == .def) := by
    unfold keptPairs at hk
    split at hk
    · exact hk
    · exact List.mem_of_mem_take hk
  have hDP := (List.mem_filter.mp hD)
  have hreg : ∀ x ∈ P, ∃ i, x.2.index = some i ∧ i < 64 := by
    intro x hx
    rw [← hP] at hx
    obtain ⟨r, hr, ha, -⟩ := spill_reg h hx
    rw [hr]; exact reg_index ha
  -- locations and vregs distinct among the defs
  have injL : ∀ x ∈ P.filter (·.1.kind == .def), x.2 = l → x = (o, l) :=
    fun x hx he => inj_of_nodup_map hDl hx hD he
  have injV : ∀ x ∈ P.filter (·.1.kind == .def), x.1.vreg = o.vreg → x = (o, l) :=
    fun x hx he => inj_of_nodup_map hDv hx hD he
  have subE := atPos_sublist P .early
  have subL := atPos_sublist P .late
  have hnotclob : ∀ r ∈ i.clobbers, Loc.reg r ≠ l := by
    intro r hr he
    rw [← hP] at hDP
    obtain ⟨j, hj, hl⟩ := mem_spillPairs hDP.1
    exact def_not_clob h hj (by simpa using hDP.2) (hl ▸ he ▸ List.mem_map_of_mem hr)
  -- after the defines and the clobbers
  have hA3 : (defineAll (clobberAll (defineAll a (atPos P .def .early)) i.clobbers)
      (atPos P .def .late)).get l = [.vreg o.vreg] := by
    have bnd : ∀ (b : AState), 64 ≤ b.size → ∀ ds : List (Operand × Loc), ds.Sublist P →
        ∀ x ∈ ds, ∃ i, x.2.index = some i ∧ i < b.size := by
      intro b hb ds hs x hx
      obtain ⟨i, h1, h2⟩ := hreg x (hs.subset hx)
      exact ⟨i, h1, by omega⟩
    rcases hpos : o.pos
    · -- early: defined first, then kept
      have hE : (o, l) ∈ atPos P .def .early := mem_atPos.mpr ⟨hDP.1, by simpa using hDP.2, hpos⟩
      have h1 := defineAll_get_mem (atPos P .def .early) a ((subE.map _).nodup hDl)
        ((subE.map _).nodup hDv) (bnd a hsz _ (subE.trans List.filter_sublist)) (o, l) hE
      have h2 := clobberAll_get_other i.clobbers (defineAll a (atPos P .def .early)) l hnotclob
      rw [defineAll_get_other, h2, h1]
      · simp only [List.filter_cons, List.filter_nil]
        have : ((atPos P .def .late).any fun x => Sym.vreg o.vreg == .vreg x.1.vreg) = false := by
          rw [Bool.eq_false_iff]
          intro hany
          obtain ⟨x, hx, hxe⟩ := List.any_eq_true.mp hany
          simp at hxe
          have := injV x (subL.subset hx) hxe.symm
          rw [this] at hx
          rw [(mem_atPos.mp hx).2.2] at hpos; cases hpos
        simp [this]
      · intro x hx he
        have := injL x (subL.subset hx) he
        rw [this] at hx
        rw [(mem_atPos.mp hx).2.2] at hpos; cases hpos
    · -- late
      have hLt : (o, l) ∈ atPos P .def .late := mem_atPos.mpr ⟨hDP.1, by simpa using hDP.2, hpos⟩
      have hb : 64 ≤ (clobberAll (defineAll a (atPos P .def .early)) i.clobbers).size := by
        rw [size_clobberAll, size_defineAll]; exact hsz
      exact defineAll_get_mem _ _ ((subL.map _).nodup hDl) ((subL.map _).nodup hDv)
        (bnd _ hb _ (subL.trans List.filter_sublist)) (o, l) hLt
  unfold transferOp
  split
  · exact hA3
  · rename_i n hn
    rw [forgetDefs_get, hA3]
    simp only [List.filter_cons, List.filter_nil]
    have : (((P.filter (·.1.kind == .def)).drop n).any fun p =>
        p.1.kind == .def && Sym.vreg o.vreg == .vreg p.1.vreg) = false := by
      rw [Bool.eq_false_iff]; intro hany
      obtain ⟨x, hx, hxe⟩ := List.any_eq_true.mp hany
      simp at hxe
      have := injV x (List.mem_of_mem_drop hx) hxe.2.symm
      have hnd : (P.filter (·.1.kind == .def)).Nodup :=
        List.Pairwise.of_map _ (fun a b h e => h (e ▸ rfl)) hDv
      have hk' : (o, l) ∈ (P.filter (·.1.kind == .def)).take n := by
        unfold keptPairs at hk; rw [hn] at hk; exact hk
      rw [← List.take_append_drop n (P.filter (·.1.kind == .def))] at hnd
      rw [this] at hx
      exact (List.nodup_append.mp hnd).2.2 _ hk' _ hx rfl
    simp [this]

/-- **A location that is not a register only loses the defs' vregs in the instruction's
transfer.** -/
theorem transferOp_nonReg {i : MInst} (h : OpsOk ops i.clobbers) {a : AState} {l : Loc}
    (hl : l.isReg = false) {s : Sym}
    (hs : s ∈ (transferOp i (ops.zip (spillLocs ops i.clobbers)).toList a).get l) :
    s ∈ a.get l ∧ ∀ o ∈ ops.toList, o.kind = .def → s ≠ .vreg o.vreg := by
  generalize hP : (ops.zip (spillLocs ops i.clobbers)).toList = P at hs
  have hne : ∀ x ∈ P, x.2 ≠ l := by
    intro x hx he
    rw [← hP] at hx
    obtain ⟨r, hr, -, -⟩ := spill_reg h hx
    rw [← he, hr] at hl; cases hl
  have hE := defineAll_get_other (atPos P .def .early) a l
    (fun x hx => hne x (mem_atPos.mp hx).1)
  have hC := clobberAll_get_other i.clobbers (defineAll a (atPos P .def .early)) l
    (fun r _ he => by rw [← he] at hl; cases hl)
  have hL := defineAll_get_other (atPos P .def .late)
    (clobberAll (defineAll a (atPos P .def .early)) i.clobbers) l
    (fun x hx => hne x (mem_atPos.mp hx).1)
  have hmid : s ∈ (defineAll (clobberAll (defineAll a (atPos P .def .early)) i.clobbers)
      (atPos P .def .late)).get l := by
    unfold transferOp at hs
    split at hs
    · exact hs
    · rw [forgetDefs_get] at hs; exact (List.mem_filter.mp hs).1
  rw [hL, hC, hE] at hmid
  simp only [List.mem_filter, Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at hmid
  refine ⟨hmid.1.1, fun o ho hd he => ?_⟩
  have hfst : (ops.zip (spillLocs ops i.clobbers)).toList.map Prod.fst = ops.toList := by
    rw [pairs_eq, List.map_map]; exact List.zipIdx_map_fst 0 _
  rw [← hfst, hP, List.mem_map] at ho
  obtain ⟨x, hx, rfl⟩ := ho
  rcases hpos : x.1.pos
  · exact hmid.1.2 x (mem_atPos.mpr ⟨hx, hd, hpos⟩) he
  · exact hmid.2 x (mem_atPos.mpr ⟨hx, hd, hpos⟩) he

end Backend.Proof.Spill
