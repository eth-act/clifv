module

public import FV.Backend.Proof.LSRun
public import FV.Backend.Proof.SpillStep4Edge

@[expose] public section

/-!
# The checker accepts the Lean allocator's validated plans (V4b-3, #275): block entries

`entry_runs`: the saves of the callee-saved registers (block 0) and the entry moves (the results
of the only predecessor's `try_call` from their fixed registers into their locations) establish
`Good` at the block's first instruction from its in-state. `inState_entryOk`: the entry block's
in-state is `EntryOk`; `inState_le_entry`: with nothing available on entry, it is below
`entryState`.
-/

namespace Backend.Proof.LS

open Backend Backend.LinearScan Backend.Proof Backend.Proof.Spill
open Backend.LinearScan.Ctx (Parts blockItems)

/-! ## Helpers -/

private theorem eraseDups_snd' {α β : Type} [DecidableEq α] [DecidableEq β] :
    ∀ (n : Nat) (l : List (α × β)), l.length ≤ n → (∀ a ∈ l, ∀ b ∈ l, a.2 = b.2 → a = b) →
      (l.eraseDups.map (·.2)).Nodup
  | _, [], _, _ => by simp
  | 0, _ :: _, hn, _ => by simp at hn
  | n + 1, a :: l, hn, h => by
    rw [List.eraseDups_cons, List.map_cons, List.nodup_cons]
    constructor
    · intro hm
      obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
      rw [List.mem_eraseDups, List.mem_filter] at hb
      have := h a List.mem_cons_self b (List.mem_cons_of_mem _ hb.1) he.symm
      subst this; simp at hb
    · refine eraseDups_snd' n _ (Nat.le_trans (List.length_filter_le _ _) (by simp at hn; omega))
        fun x hx y hy => h x (List.mem_cons_of_mem _ (List.mem_filter.mp hx).1) y
          (List.mem_cons_of_mem _ (List.mem_filter.mp hy).1)

private theorem mem_clean' {m : Loc × Loc} {l : List (Loc × Loc)} :
    m ∈ cleanMoves l ↔ m ∈ l ∧ m.1 ≠ m.2 := by
  unfold cleanMoves
  rw [List.mem_eraseDups, List.mem_filter]
  rcases m with ⟨a, b⟩
  simp

/-- The destinations of cleaned moves are distinct if two proper moves with one destination
are one. -/
private theorem clean_nodup' {l : List (Loc × Loc)}
    (h : ∀ m ∈ l, ∀ m' ∈ l, m.1 ≠ m.2 → m'.1 ≠ m'.2 → m.2 = m'.2 → m = m') :
    ((cleanMoves l).map (·.2)).Nodup := by
  unfold cleanMoves
  refine eraseDups_snd' _ _ (Nat.le_refl _) fun a ha b hb he => ?_
  rw [List.mem_filter] at ha hb
  rcases a with ⟨a1, a2⟩
  rcases b with ⟨b1, b2⟩
  simp only [bne_iff_ne, ne_eq] at ha hb
  exact h _ ha.1 _ hb.1 ha.2 hb.2 he

/-- `entryState` holds the entry value of every callee-saved register in the register. -/
private theorem entry_mem_entryState' {N : Nat} {r : Reg} {i : Nat} (hr : r ∈ calleeSaved)
    (hi : (Loc.reg r).index = some i) (hlt : i < N) : Sym.entry r ∈ (entryState N).get (.reg r) := by
  unfold entryState
  suffices ∀ (rs : List Reg) (a : AState), a.size = N → (r ∈ rs ∨ Sym.entry r ∈ a.get (.reg r)) →
      Sym.entry r ∈ (rs.foldl (fun a r => a.put (.reg r) [.entry r]) a).get (.reg r) from
    this calleeSaved _ (by simp) (.inl hr)
  intro rs
  induction rs with
  | nil => intro a _ h; simpa using h
  | cons r' rs ih =>
    intro a hsz h
    simp only [List.foldl_cons]
    refine ih _ (by rw [Spill.size_put]; exact hsz) ?_
    by_cases e : r' = r
    · subst e
      right
      rw [Spill.get_put_self hi (by omega)]
      exact List.mem_singleton_self _
    · rcases h with h | h
      · exact .inl ((List.mem_cons.mp h).resolve_left (Ne.symm e))
      · right
        rw [Spill.get_put_ne (by intro h'; cases h'; exact e rfl)]
        exact h

private theorem preds_get {fn : Fn} {s b : Nat} (h : fn.preds.getD s #[] = #[b]) :
    fn.preds[s]? = some #[b] := by
  rw [Array.getD_eq_getD_getElem?] at h
  cases hp : fn.preds[s]? with
  | none => rw [hp] at h; simp at h
  | some a => rw [hp] at h; simp only [Option.getD_some] at h; rw [h]

section
variable {vc : VCode} {c : LinearScan.Ctx}

/-- A location of the plan is no save slot. -/
private theorem loc_ne_save (v : Nat) (r : Reg) : c.loc v ≠ .save r := by
  unfold LinearScan.Ctx.loc Fn.loc
  split <;> simp

/-- Two vregs live at one position in one location are one. -/
private theorem loc_inj (hpf : PlanFacts vc c) {v w q : Nat} (hv : v < c.fn.nv) (hw : w < c.fn.nv)
    (hcv : c.pl.cov v q = true) (hcw : c.pl.cov w q = true) (h : c.loc v = c.loc w) : v = w := by
  unfold LinearScan.Ctx.loc Fn.loc at h
  cases hrv : c.pl.regOf v <;> cases hrw : c.pl.regOf w <;> simp only [hrv, hrw] at h
  · injection h with h1 h2
    exact hpf.homes v w q hv hw hrv hrw h1 h2 hcv hcw
  · cases h
  · cases h
  · cases h
    exact hpf.inter v w _ q hrv hrw hcv hcw

/-- A vreg live into a block is live after the last instruction of each predecessor. -/
private theorem edgeOk_cov {v t b : Nat} (h : c.edgeOk v t b = true) :
    c.pl.cov v (pos (c.lastOf b) 4) = true := by
  unfold LinearScan.Ctx.edgeOk at h
  split at h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨-, h⟩ := h
    split at h
    · simp only [Bool.and_eq_true] at h
      exact cov_of_covI h.2 (by unfold pos; omega) (Nat.le_refl _)
    · cases h
  · exact h

/-- A def's claim covers the position after its instruction. -/
private theorem opRange_def {g : Nat} {o : Operand} (h : o.kind = .def) :
    (opRange g o true).1 ≤ pos g 4 ∧ pos g 4 ≤ (opRange g o true).2 := by
  unfold opRange
  rw [h]
  simp only [ite_true]
  constructor
  · unfold pos; split <;> omega
  · exact Nat.le_refl _

/-- A def of the predecessor's terminator on the edge into `s` is an entry pair of `s`. -/
private theorem edgeDefs_pair {s b : Nat} (hp : c.fn.preds.getD s #[] = #[b]) {o : Operand}
    (ho : o ∈ edgeDefs vc c.fn.succs b s) :
    ∃ y ∈ entryPairs vc c.fn.succs c.fn.preds s, y.1 = o := by
  rw [entryPairs_one (preds_get hp)]
  unfold entryPairsOf
  unfold edgeDefs at ho
  revert ho
  rcases vc.blocks[b]? with _ | vb <;> rcases c.fn.succs[b]? with _ | ss <;> intro ho <;>
    try cases ho
  dsimp only at ho ⊢
  revert ho
  rcases List.idxOf? s ss.toList with _ | j <;> intro ho
  · cases ho
  · exact List.mem_map.mp ho

/-- An entry move: from the fixed register of an entry pair into its vreg's location. -/
private theorem move_facts {s : Nat} {ms : List (Loc × Loc)}
    (hms : ∀ m ∈ ms, ∃ b o p, c.fn.preds.getD s #[] = #[b] ∧ o ∈ edgeDefs vc c.fn.succs b s ∧
        o.con = .fixed p ∧ c.pl.cov o.vreg (pos (c.fn.start.getD s 0) 0) = true ∧
        m = (.reg p, c.loc o.vreg)) {m : Loc × Loc} (hm : m ∈ ms) :
    ∃ y ∈ entryPairs vc c.fn.succs c.fn.preds s, ∃ p, y.1.con = .fixed p ∧
      c.pl.cov y.1.vreg (pos (c.fn.start.getD s 0) 0) = true ∧ m = (.reg p, c.loc y.1.vreg) := by
  obtain ⟨b, o, p, hp, ho, hf, hc, rfl⟩ := hms m hm
  obtain ⟨y, hy, rfl⟩ := edgeDefs_pair hp ho
  exact ⟨y, hy, p, hf, hc, rfl⟩

end

section
variable {vc : VCode} {c : LinearScan.Ctx} {rf : RFunc} {D : Nat → Nat → Bool}
  (H : Hyps vc c rf D)
include H

/-- An entry pair of `s` is a def of the terminator of `s`'s only predecessor `b`, on the edge
into `s` (`edgeDefs`). -/
private theorem pair_facts {s : Nat} {y : Operand × Loc}
    (hy : y ∈ entryPairs vc c.fn.succs c.fn.preds s) :
    ∃ b ops, c.fn.preds.getD s #[] = #[b] ∧ y.1 ∈ edgeDefs vc c.fn.succs b s ∧
      c.fn.ops[c.lastOf b]? = some ops ∧ y.1 ∈ ops.toList ∧ y.1.kind = .def ∧
      (∃ clob, OpsOk ops clob) ∧ c.fn.clsOf y.1.vreg = y.1.cls := by
  obtain ⟨b, vb, ss, j, hp, hvb, hss, hj, hyt⟩ := entryPairs_spec hy
  obtain ⟨T, ops, hT, -, hops, hk, -⟩ := termEdgeDefs_spec hyt
  obtain ⟨hz, hdef⟩ := mem_keptPairs hk
  have hyo : y.1 ∈ ops.toList := spillPairs_fst ops T.clobbers ▸ List.mem_map_of_mem hz
  obtain ⟨hpos, hTk⟩ := back_get hT
  have hg := (H.fn.opsGetD hvb hTk hops).1
  have hl : c.lastOf b = c.fn.start.getD b 0 + (vb.insts.size - 1) := by
    unfold LinearScan.Ctx.lastOf
    rw [H.fn.startSucc hvb]
    omega
  obtain ⟨ops', hops', hok, -⟩ := H.loc.1 b vb _ T hvb hTk
  rw [hops] at hops'
  cases hops'
  refine ⟨b, ops, by simp [Array.getD_eq_getD_getElem?, hp], ?_, by rw [hl]; exact hg, hyo, hdef,
    ⟨_, hok⟩, H.fn.cls _ _ (H.loc.2.1.1 b vb _ T ops hvb hTk hops y.1 hyo)⟩
  simp only [edgeDefs, hvb, hss, hj]
  exact List.mem_map_of_mem hyt

/-- A fixed entry pair: its vreg is a vreg of the function, its register and location are of its
class, and its register holds no other vreg after the predecessor's terminator. -/
private theorem pair_fixed {s : Nat} {y : Operand × Loc}
    (hy : y ∈ entryPairs vc c.fn.succs c.fn.preds s) {p : Reg} (hp : y.1.con = .fixed p) :
    y.1.vreg < c.fn.nv ∧ LocCls (.reg p) y.1.cls ∧ LocCls (c.loc y.1.vreg) y.1.cls ∧
    ∃ b, c.fn.preds.getD s #[] = #[b] ∧
      ∀ w, c.pl.regOf w = some p → c.pl.cov w (pos (c.lastOf b) 4) = true → w = y.1.vreg := by
  obtain ⟨b, ops, hpr, -, hg, hyo, hdef, ⟨clob, hok⟩, hcls⟩ := pair_facts H hy
  obtain ⟨ha, hrc⟩ := hok.fixedReg y.1 hyo p hp
  refine ⟨H.fn.nv_ops _ ops hg y.1 hyo, .inl ⟨p, rfl, ha, hrc⟩, loc_cls H.plan hcls, b, hpr,
    fun w hw hcw => ?_⟩
  obtain ⟨h1, h2⟩ := opRange_def (g := c.lastOf b) hdef
  exact (H.plan.claim _ ops hg y.1 hyo p hp).2 w hw _ h1 h2 hcw

/-- A vreg live at the start of block `s` is live after the terminator of its predecessor. -/
private theorem live_pred {s b v : Nat} (hs : s < vc.blocks.size) (hv : v < c.fn.nv)
    (hp : c.fn.preds.getD s #[] = #[b]) (hc : c.pl.cov v (pos (c.fn.start.getD s 0) 0) = true) :
    c.pl.cov v (pos (c.lastOf b) 4) = true :=
  edgeOk_cov (H.plan.edge v hv s hs hc b (by rw [hp]; simp))

/-- The entry location of the vreg of a fixed entry pair is its register. -/
private theorem entryLoc_fixed {s : Nat} {y : Operand × Loc}
    (hy : y ∈ entryPairs vc c.fn.succs c.fn.preds s) {p : Reg} (hp : y.1.con = .fixed p) :
    entryLoc vc c s y.1.vreg = .reg p := by
  have hnd := (Spill.entryPairs_facts (succs := c.fn.succs) (preds := c.fn.preds) H.loc s).2
  unfold entryLoc
  cases hf : ((entryPairs vc c.fn.succs c.fn.preds s).map (·.1)).find? (·.vreg == y.1.vreg) with
  | none =>
    have := List.find?_eq_none.mp hf y.1 (List.mem_map_of_mem hy)
    simp at this
  | some o =>
    have hv : o.vreg = y.1.vreg := by simpa using List.find?_some hf
    obtain ⟨y', hy', rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hf)
    have : y' = y := inj_of_nodup_map hnd hy' hy hv
    subst this
    simp only [hp]

/-- The start of a block: the saves (block 0) and the entry moves establish `Good` at its first
instruction. -/
theorem entry_runs {b : Nat} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) {p : Parts}
    (hp : c.blockParts b = .ok p) :
    Runs (ctxOf vc c rf) vb 0 ((if b = 0 then savesOf rf.saved else []) ++ p.entry)
      (inState vc c rf D b) fun k' a' => k' = 0 ∧
        Good c rf (availStart vc c.fn.succs c.fn.preds D b) (pos (c.fn.start.getD b 0) 0) a' := by
  have hpf := H.plan
  have hbl : b < vc.blocks.size := (Array.getElem?_eq_some_iff.mp hvb).1
  have hne : 0 ≠ vb.insts.size := by
    obtain ⟨t, ts, ht, -⟩ := (Prep.cfg_spec H.fn.cfg).blk b vb hvb
    have := (back_get ht).1
    omega
  have hsz0 := size_inState (vc := vc) (c := c) (rf := rf) (D := D) b
  have hnd := (Spill.entryPairs_facts (succs := c.fn.succs) (preds := c.fn.preds) H.loc b).2
  -- the saves
  have hS : Runs (ctxOf vc c rf) vb 0 (if b = 0 then savesOf rf.saved else [])
      (inState vc c rf D b) fun k a => k = 0 ∧ a.size = 128 + 2 * rf.spillSlots ∧
        (∀ l, (∀ r, l ≠ .save r) → a.get l = (inState vc c rf D b).get l) ∧
        (∀ r ∈ rf.saved, Sym.entry r ∈ a.get (.save r)) := by
    by_cases hb : b = 0
    · subst hb
      simp only [↓reduceIte]
      rw [savesOf_eq]
      refine (Runs.moves hne _ _ (fun m hm => ?_) (fun m hm m' hm' => ?_) ?_ (fun m hm => ?_)).mono
        fun k a ⟨e1, e2, e3, e4⟩ => ⟨e1, by rw [e2, hsz0], fun l hl => e4 l fun m hm he => ?_,
          fun r hr => ?_⟩
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
        exact checkMove_save hr (H.build.saved r hr)
      · obtain ⟨r, -, rfl⟩ := List.mem_map.mp hm
        obtain ⟨r', -, rfl⟩ := List.mem_map.mp hm'
        simp
      · rw [List.map_map]
        exact Spill.nodup_map_of_inj (g := id) (by simpa using H.build.savedNodup)
          fun x _ y _ h => by simpa using h
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
        obtain ⟨i, h1, h2⟩ := save_index (H.build.saved r hr)
        exact ⟨i, h1, by rw [hsz0]; omega⟩
      · obtain ⟨r, -, rfl⟩ := List.mem_map.mp hm
        exact hl r he.symm
      · rw [e3 (Loc.reg r, Loc.save r) (List.mem_map_of_mem hr)]
        exact inState_entryReg (H.build.saved r hr) (.inl rfl)
    · simp only [hb, ↓reduceIte]
      exact Runs.nil ⟨rfl, hsz0, fun l _ => rfl,
        fun r hr => inState_entrySave (H.build.saved r hr) hb hr⟩
  -- the entry moves
  obtain ⟨ms, hent, hms, hall⟩ := entryMoves_facts H.fn (partsFacts hp).entry
  refine Runs.append hS fun k a ⟨hk, hsz, hfr, hsv⟩ => ?_
  subst hk
  rw [hent, mv_eq]
  have hmf : ∀ m ∈ cleanMoves ms, ∃ y ∈ entryPairs vc c.fn.succs c.fn.preds b, ∃ q,
      y.1.con = .fixed q ∧ c.pl.cov y.1.vreg (pos (c.fn.start.getD b 0) 0) = true ∧
      m = (.reg q, c.loc y.1.vreg) := fun m hm => move_facts hms (mem_clean'.mp hm).1
  have hit : ∀ m ∈ cleanMoves ms, RItem.move m.1 m.2 ∈ blockItems vb p [] := fun m hm =>
    entry_mem _ (by rw [hent]; exact List.mem_map_of_mem hm)
  have hslot : ∀ m ∈ cleanMoves ms, ∀ s cl, m.2 = .stack s cl → s < rf.spillSlots :=
    fun m hm s cl he => H.build.slots b vb p hvb hp _ (hit m hm) m.2 (by simp [RItem.locs]) s cl he
  refine (Runs.moves hne (cleanMoves ms) a (fun m hm => ?_) (fun m hm m' hm' he => ?_) ?_
    (fun m hm => ?_)).mono fun k' a' ⟨e1, e2, e3, e4⟩ =>
      ⟨e1, ⟨by rw [e2, hsz], fun v hv hcov hA hloc => ?_,
        fun r hr => ⟨fun hrs => ?_, fun hrs => ?_⟩⟩⟩
  · -- the moves pass the checker's move check
    obtain ⟨y, hy, q, hq, -, rfl⟩ := hmf m hm
    obtain ⟨-, hcs, hcd, -⟩ := pair_fixed H hy hq
    exact checkMove_ok hcs hcd (fun s cl he => by cases he) (hslot _ hm) (.inl rfl)
  · -- no source is a destination
    obtain ⟨y, hy, q, hq, -, rfl⟩ := hmf m hm
    obtain ⟨y', hy', q', hq', hc', rfl⟩ := hmf m' hm'
    obtain ⟨-, -, -, b', hpr, hcl⟩ := pair_fixed H hy hq
    have hv' := (pair_fixed H hy' hq').1
    have he' : c.loc y'.1.vreg = .reg q := he.symm
    have hw := hcl _ (loc_reg he') (live_pred H hbl hv' hpr hc')
    apply (mem_clean'.mp hm).2
    show Loc.reg q = c.loc y.1.vreg
    rw [← hw, he']
  · -- the destinations are distinct
    refine clean_nodup' fun m hm m' hm' _ _ he => ?_
    obtain ⟨y, hy, q, hq, hc, rfl⟩ := move_facts hms hm
    obtain ⟨y', hy', q', hq', hc', rfl⟩ := move_facts hms hm'
    have hv := loc_inj hpf (pair_fixed H hy hq).1 (pair_fixed H hy' hq').1 hc hc' he
    have : y = y' := inj_of_nodup_map hnd hy hy' hv
    subst this
    rw [hq] at hq'
    cases hq'
    rfl
  · -- the destinations are represented
    obtain ⟨y, hy, q, hq, -, rfl⟩ := hmf m hm
    obtain ⟨i, h1, h2⟩ := locValid_of_cls (pair_fixed H hy hq).2.2.1 (hslot _ hm)
    exact ⟨i, h1, by rw [hsz]; exact h2⟩
  · -- a live, available vreg is in its location
    have hA' : (D b v || (entryStored vc c.fn.succs c.fn.preds b).contains v) = true := hA
    by_cases hx : ∃ y ∈ entryPairs vc c.fn.succs c.fn.preds b, y.1.vreg = v ∧
        ∃ q, y.1.con = .fixed q ∧ c.loc v ≠ .reg q
    · obtain ⟨y, hy, rfl, q, hq, hne'⟩ := hx
      obtain ⟨-, hcs, -, -⟩ := pair_fixed H hy hq
      obtain ⟨b', -, hpr, hyd, -⟩ := pair_facts H hy
      have hmem : (Loc.reg q, c.loc y.1.vreg) ∈ cleanMoves ms :=
        mem_clean'.mpr ⟨(hall b' (by rw [hpr]; simp) y.1 hyd hcov).1 q hq hne',
          fun h => hne' h.symm⟩
      rw [e3 _ hmem, hfr _ (fun r => by simp)]
      have hl := entryLoc_fixed H hy hq
      rw [← hl]
      refine inState_vreg hv hcov hA' ?_
      rw [hl]
      exact locValid_of_cls hcs (fun _ _ he => by cases he)
    · have hel : entryLoc vc c b v = c.loc v := by
        rcases entryLoc_cases (vc := vc) (c := c) b v with h | ⟨y, hy, hyv, q, hq, h⟩
        · exact h
        · rw [h]
          exact Classical.byContradiction fun hne' =>
            hx ⟨y, hy, hyv, q, hq, fun he => hne' he.symm⟩
      rw [e4 _ (fun m hm he => ?_), hfr _ (fun r => loc_ne_save v r)]
      · rw [← hel]
        exact inState_vreg hv hcov hA' (hel ▸ hloc)
      · obtain ⟨y, hy, q, hq, hc, rfl⟩ := hmf m hm
        have hvv := loc_inj hpf (pair_fixed H hy hq).1 hv hc hcov he
        apply (mem_clean'.mp hm).2
        show Loc.reg q = c.loc y.1.vreg
        exact Classical.byContradiction fun hne' =>
          hx ⟨y, hy, hvv, q, hq, fun h' => hne' (by rw [hvv]; exact h'.symm)⟩
  · -- a saved register's entry value stays in its save slot
    rw [e4 _ fun m hm he => ?_]
    · exact hsv r hrs
    · obtain ⟨y, -, q, -, -, rfl⟩ := hmf m hm
      exact loc_ne_save _ r he
  · -- an unsaved callee-saved register keeps its entry value
    rw [e4 _ fun m hm he => ?_, hfr _ (fun r' => by simp)]
    · exact inState_entryReg hr (.inr hrs)
    · exact H.build.notSaved r hr hrs b vb p hvb hp _ (hit m hm) (by rw [← he]; simp [RItem.locs])

omit H in
/-- The entry block's in-state is `EntryOk`. -/
theorem inState_entryOk : EntryOk (inState vc c rf D 0) := by
  refine ⟨fun l r h => ?_, fun l l' v h h' => ?_⟩
  · rcases (mem_inState h).2 with ⟨v, he, -⟩ | ⟨r', he, (⟨rfl, hr, -⟩ | ⟨-, h0, -⟩)⟩
    · cases he
    · cases he
      exact ⟨hr, rfl⟩
    · exact absurd rfl h0
  · rcases (mem_inState h).2 with ⟨w, he, -, -, -, hl⟩ | ⟨r', he, -⟩
    · rcases (mem_inState h').2 with ⟨w', he', -, -, -, hl'⟩ | ⟨r', he', -⟩
      · cases he
        cases he'
        rw [← hl, ← hl']
      · cases he'
    · cases he

/-- With nothing available on entry, the entry block's in-state is below `entryState`. -/
theorem inState_le_entry (hD0 : ∀ v, D 0 v = false) :
    (inState vc c rf D 0).le (entryState (128 + 2 * rf.spillSlots)) = true := by
  have hE := H.loc.2.2 _ _ H.fn.cfg
  have hes : entryStored vc c.fn.succs c.fn.preds 0 = [] :=
    entryStored_ne fun b hb => by rw [hE.entry.2.1] at hb; simp at hb
  refine le_of_mem fun l x h => ?_
  obtain ⟨⟨i, hi, hlt⟩, hm⟩ := mem_inState h
  rcases hm with ⟨v, -, -, -, hd, -⟩ | ⟨r, rfl, (⟨rfl, hr, -⟩ | ⟨-, h0, -⟩)⟩
  · rw [hD0, hes] at hd
    simp at hd
  · exact entry_mem_entryState' hr hi hlt
  · exact absurd rfl h0

end

end Backend.Proof.LS
