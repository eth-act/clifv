import FV.Backend.Proof.SpillStep4State

/-!
# Block entries, argument copies and edges of the spill allocation (V4 (a), step 4)

`pre_runs`: the saves (entry block) and the entry stores take a block's in-state to a `Good`
state for `availStart`. `argMoves_runs`: the two-phase parallel copy of a `jump`'s arguments
(`spillArgMoves`) leaves every parameter's home with its argument's symbols and every other home
and save slot untouched. `edge_noargs` / `edge_args`: the out-state of a block feeds each
successor's in-state (`CheckCtx.edge`, `AState.le`), from `SpillAvail.edges`.
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof

/-! ## Generic facts -/

theorem availAt_succ {insts : Array MInst} {k : Nat} {i : MInst} (hi : insts[k]? = some i)
    (A : Nat → Bool) : availAt insts A (k + 1) = availInst i (availAt insts A k) := by
  unfold availAt
  rw [List.take_add_one, List.foldl_append, Array.getElem?_toList, hi]
  rfl

theorem back_get {vb : VBlock} {T : MInst} (h : vb.insts.back? = some T) :
    0 < vb.insts.size ∧ vb.insts[vb.insts.size - 1]? = some T := by
  rw [Array.back?_eq_getElem?] at h
  have := (Array.getElem?_eq_some_iff.mp h).1
  exact ⟨by omega, h⟩

theorem mem_blockVregs_op {vb : VBlock} {k : Nat} {i : MInst} {ops : Array Operand}
    (hi : vb.insts[k]? = some i) (hops : i.operands = .ok ops) {o : Operand} (ho : o ∈ ops.toList) :
    (o.vreg, o.cls) ∈ blockVregs vb := by
  unfold blockVregs
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, ?_, ?_⟩)
  · exact List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hi)
  · rw [hops]; exact List.mem_map_of_mem ho

theorem mem_blockVregs_reg {vb : VBlock} {r : Reg} (hr : r ∈ vb.params.toList ++ vb.branchArgs.toList)
    {n : Nat} {c : RegClass} (he : r = .vreg n c) : (n, c) ∈ blockVregs vb := by
  unfold blockVregs
  exact List.mem_append_left _ (List.mem_filterMap.mpr ⟨r, hr, by rw [he]⟩)

theorem scratch_ok : ∀ c, (spillScratch c).allocatable = true ∧ (spillScratch c).realClass? = some c := by
  intro c; cases c <;> decide

section
variable {vc : VCode} {succs preds : Array (Array Nat)} {D : Nat → Nat → Bool}

theorem opFacts (hloc : SpillLocalOk vc) {b : Nat} {vb : VBlock} {k : Nat} {i : MInst}
    {ops : Array Operand} (hvb : vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    (hops : i.operands = .ok ops) :
    ∀ o ∈ ops.toList, vc.classes[o.vreg]? = some o.cls ∧
      ∃ n, (spillHomes vc)[(o.vreg, o.cls)]? = some n :=
  fun o ho => ⟨hloc.2.1.1 b vb k i ops hvb hi hops o ho,
    spillHomes_mem vc hvb (mem_blockVregs_op hi hops ho)⟩

theorem regFacts (hloc : SpillLocalOk vc) {b : Nat} {vb : VBlock} (hvb : vc.blocks[b]? = some vb)
    {r : Reg} (hr : r ∈ vb.params.toList ++ vb.branchArgs.toList) :
    ∃ n c, r = .vreg n c ∧ vc.classes[n]? = some c ∧ ∃ m, (spillHomes vc)[(n, c)]? = some m := by
  obtain ⟨n, c, rfl, hc⟩ := hloc.2.1.2 b vb hvb r hr
  exact ⟨n, c, rfl, hc, spillHomes_mem vc hvb (mem_blockVregs_reg hr rfl)⟩

theorem termEdgeDefs_sub (vb : VBlock) (j : Nat) : termEdgeDefs vb j = [] ∨
    ∃ T ops, vb.insts.back? = some T ∧ T.operands = .ok ops ∧
      (termEdgeDefs vb j).Sublist (keptPairs T (ops.zip (spillLocs ops T.clobbers)).toList) := by
  generalize hx : termEdgeDefs vb j = x
  unfold termEdgeDefs at hx
  split at hx
  · exact .inl hx.symm
  rename_i T hT
  split at hx
  · exact .inl hx.symm
  split at hx
  · exact .inl hx.symm
  rename_i ops hops
  refine .inr ⟨T, ops, hT, hops, ?_⟩
  subst hx
  split
  · split
    · exact List.take_sublist _ _
    · exact List.Sublist.refl _
  · exact List.Sublist.refl _

/-- The registers of a block's terminator defs live on an edge hold allocatable registers of
their class, with consistent classes and homes, and carry pairwise distinct vregs. -/
theorem termEdgeDefs_facts (hloc : SpillLocalOk vc) {b : Nat} {vb : VBlock}
    (hvb : vc.blocks[b]? = some vb) (j : Nat) :
    (∀ y ∈ termEdgeDefs vb j, (∃ r, y.2 = .reg r ∧ r.allocatable = true ∧ r.realClass? = some y.1.cls) ∧
      vc.classes[y.1.vreg]? = some y.1.cls ∧ ∃ n, (spillHomes vc)[(y.1.vreg, y.1.cls)]? = some n) ∧
    ((termEdgeDefs vb j).map (·.1.vreg)).Nodup := by
  rcases termEdgeDefs_sub vb j with h | ⟨T, ops, hT, hops, hsub⟩
  · rw [h]; exact ⟨fun y hy => (by cases hy), List.nodup_nil⟩
  obtain ⟨-, hTk⟩ := back_get hT
  obtain ⟨ops', hops', hok, -⟩ := hloc.1 b vb _ T hvb hTk
  rw [hops] at hops'
  cases hops'
  refine ⟨fun y hy => ?_, (keptPairs_vregs_nodup hok).sublist (hsub.map _)⟩
  have hyP := (mem_keptPairs (hsub.subset hy)).1
  have hyo : y.1 ∈ ops.toList := spillPairs_fst ops T.clobbers ▸ List.mem_map_of_mem hyP
  exact ⟨spill_reg hok hyP, opFacts hloc hvb hTk hops y.1 hyo⟩

theorem entryPairs_facts (hloc : SpillLocalOk vc) (s : Nat) :
    (∀ y ∈ entryPairs vc succs preds s, (∃ r, y.2 = .reg r ∧ r.allocatable = true ∧
      r.realClass? = some y.1.cls) ∧ vc.classes[y.1.vreg]? = some y.1.cls ∧
      ∃ n, (spillHomes vc)[(y.1.vreg, y.1.cls)]? = some n) ∧
    ((entryPairs vc succs preds s).map (·.1.vreg)).Nodup := by
  by_cases hb : ∃ b, preds[s]? = some #[b]
  · obtain ⟨b, hp⟩ := hb
    rw [entryPairs_one hp]
    unfold entryPairsOf
    rcases hvb : vc.blocks[b]? with _ | vb <;> rcases succs[b]? with _ | ss <;>
      try exact ⟨fun y hy => (by cases hy), List.nodup_nil⟩
    dsimp only
    rcases List.idxOf? s ss.toList with _ | j
    · exact ⟨fun y hy => (by cases hy), List.nodup_nil⟩
    · exact termEdgeDefs_facts hloc hvb j
  · rw [entryPairs_ne fun b h => hb ⟨b, h⟩]
    exact ⟨fun y hy => (by cases hy), List.nodup_nil⟩

/-! ## Block entry: saves and entry stores -/

/-- **The start of a block**: the saves (entry block) and the entry stores take the in-state to a
`Good` state for `availStart`. -/
theorem pre_runs (hcfg : vc.cfg = .ok (succs, preds)) (hloc : SpillLocalOk vc) {c : CheckCtx}
    (hsl : c.rf.spillSlots = (spillHomes vc).size + maxArgs vc) (hsv : c.rf.saved = calleeSaved)
    {b : Nat} {vb : VBlock} (hne : 0 ≠ vb.insts.size) :
    Runs c vb 0 ((if b == 0 then spillSaves else []) ++ spillEntryStores (spillHomes vc) vc succs preds b)
      (inState vc succs preds D b) fun k a => k = 0 ∧ Good vc (availStart vc succs preds D b) a := by
  have hE := hloc.2.2 succs preds hcfg
  obtain ⟨hfa, hfnd⟩ := entryPairs_facts (succs := succs) (preds := preds) hloc b
  have hS : Runs c vb 0 (if b == 0 then spillSaves else []) (inState vc succs preds D b)
      fun k a => k = 0 ∧ a.size = stN vc ∧
        (∀ v cl n, D b v = true → vc.classes[v]? = some cl → (spillHomes vc)[(v, cl)]? = some n →
          Sym.vreg v ∈ a.get (.stack n cl)) ∧
        (∀ r ∈ calleeSaved, Sym.entry r ∈ a.get (.save r)) ∧
        (∀ y ∈ entryPairs vc succs preds b, Sym.vreg y.1.vreg ∈ a.get y.2) := by
    by_cases hb : b = 0
    · subst hb
      simp only [BEq.rfl, ↓reduceIte]
      rw [spillSaves_eq]
      refine (Runs.moves hne _ _
        (fun m hm => by
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
          exact (checkMove_saves c hsv _ hr).1)
        (fun m hm m' hm' => by
          obtain ⟨r, -, rfl⟩ := List.mem_map.mp hm
          obtain ⟨r', -, rfl⟩ := List.mem_map.mp hm'
          simp)
        (by
          rw [List.map_map]
          exact nodup_map_of_inj (g := id) (by simpa using calleeSaved_nodup)
            fun x _ y _ h => by simpa using h)
        (fun m hm => by
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
          obtain ⟨i, h1, h2⟩ := save_index hr
          exact ⟨i, h1, by rw [inState, size_mkState]; unfold stN; omega⟩)).mono
        fun k a ⟨e1, e2, e3, e4⟩ => ⟨e1, by rw [e2, inState, size_mkState], ?_, ?_, ?_⟩
      · intro v cl n hv hc hn
        rw [e4 _ (by simp)]
        exact inState_home hv hc hn
      · intro r hr
        rw [e3 (Loc.reg r, Loc.save r) (List.mem_map_of_mem hr)]
        exact inState_reg0 hr
      · intro y hy
        rw [entryPairs_nil hE.entry.2.1] at hy
        cases hy
    · have hb' : (b == 0) = false := by simpa using hb
      simp only [hb', Bool.false_eq_true, ↓reduceIte]
      refine Runs.nil ⟨rfl, by rw [inState, size_mkState], fun v cl n hv hc hn => inState_home hv hc hn,
        fun r hr => inState_save hb hr, fun y hy => ?_⟩
      obtain ⟨⟨r, hr, ha, -⟩, -⟩ := hfa y hy
      exact inState_pair ha hy hr
  refine Runs.append hS fun k a ⟨hk, hsz, hh, hs, hy⟩ => ?_
  subst hk
  rw [spillEntryStores_eq]
  have hmem : ∀ m ∈ (entryPairs vc succs preds b).map
      (fun x => (x.2, spillHome (spillHomes vc) x.1.vreg x.1.cls)), ∃ y ∈ entryPairs vc succs preds b,
      ∃ r n, m = (.reg r, .stack n y.1.cls) ∧ y.2 = .reg r ∧ r.allocatable = true ∧
        r.realClass? = some y.1.cls ∧ (spillHomes vc)[(y.1.vreg, y.1.cls)]? = some n := by
    intro m hm
    obtain ⟨y, hyy, rfl⟩ := List.mem_map.mp hm
    obtain ⟨⟨r, hr, ha, hc⟩, -, n, hn⟩ := hfa y hyy
    exact ⟨y, hyy, r, n, by rw [hr, spillHome_eq hn], hr, ha, hc, hn⟩
  refine (Runs.moves hne _ a (fun m hm => ?_) (fun m hm m' hm' he => ?_) ?_
    (fun m hm => ?_)).mono fun k' a' ⟨e1, e2, e3, e4⟩ => ⟨e1, ⟨by rw [e2, hsz], ?_, ?_⟩⟩
  · obtain ⟨y, -, r, n, rfl, -, ha, hc, hn⟩ := hmem m hm
    exact checkMove_store c _ (by rw [hsl]; have := spillHomes_lt vc hn; omega) ha hc
  · obtain ⟨y, -, r, n, rfl, -⟩ := hmem m hm
    obtain ⟨y', -, r', n', rfl, -⟩ := hmem m' hm'
    cases he
  · rw [List.map_map]
    refine nodup_map_of_inj hfnd fun x hx y hy he => ?_
    obtain ⟨-, -, n, hn⟩ := hfa x hx
    obtain ⟨-, -, n', hn'⟩ := hfa y hy
    simp only [Function.comp, spillHome_eq hn, spillHome_eq hn'] at he
    injection he with e1 e2
    rw [← e1, ← e2] at hn'
    have := spillHomes_inj vc hn hn'
    injection this
  · obtain ⟨y, -, r, n, rfl, -, -, -, hn⟩ := hmem m hm
    obtain ⟨j, h1, h2⟩ := home_index_lt hn
    exact ⟨j, h1, by rw [hsz]; exact h2⟩
  · intro v cl n hv hc hn
    by_cases hx : ∃ y ∈ entryPairs vc succs preds b, y.1.vreg = v
    · obtain ⟨y, hyy, rfl⟩ := hx
      obtain ⟨⟨r, hr, -⟩, hcy, ny, hny⟩ := hfa y hyy
      rw [hc] at hcy
      cases hcy
      rw [hn] at hny
      cases hny
      have hm : (y.2, Loc.stack n y.1.cls) ∈ (entryPairs vc succs preds b).map
          (fun x => (x.2, spillHome (spillHomes vc) x.1.vreg x.1.cls)) :=
        List.mem_map.mpr ⟨y, hyy, by rw [spillHome_eq hn]⟩
      rw [e3 _ hm]
      exact hy y hyy
    · have hD : D b v = true := by
        unfold availStart at hv
        rw [entryStored_eq] at hv
        rcases Bool.or_eq_true_iff.mp hv with h | h
        · exact h
        · obtain ⟨y, hyy, rfl⟩ := List.mem_map.mp (List.contains_iff_mem.mp h)
          exact absurd ⟨y, hyy, rfl⟩ hx
      rw [e4 _ fun m hm he => ?_]
      · exact hh v cl n hD hc hn
      · obtain ⟨y, hyy, r, n', rfl, -, -, -, hn'⟩ := hmem m hm
        simp only at he
        injection he with e1 e2
        subst e1 e2
        have := spillHomes_inj vc hn' hn
        injection this with ev
        exact hx ⟨y, hyy, ev⟩
  · intro r hr
    rw [e4 _ fun m hm he => ?_]
    · exact hs r hr
    · obtain ⟨y, -, r', n', rfl, -⟩ := hmem m hm
      cases he

/-! ## Edges without arguments -/

theorem edgeForget_cases {c : CheckCtx} (hcvc : c.vc = vc) {b s : Nat} {vb : VBlock} {T : MInst}
    {ops : Array Operand} (hvb : vc.blocks[b]? = some vb) (hT : vb.insts.back? = some T)
    (hops : T.operands = .ok ops) (a : AState) :
    c.edgeForget b s a = a ∨ ∃ jn n, T.normalDead = some (jn, n) ∧ c.succs[b]?.bind (·[jn]?) = some s ∧
      c.edgeForget b s a = forgetOps a ((ops.toList.filter (·.kind == .def)).drop n) := by
  unfold CheckCtx.edgeForget
  rw [hcvc, hvb]
  simp only [hT]
  rcases hnd : T.normalDead with _ | ⟨jn, n⟩
  · exact .inl rfl
  · simp only
    by_cases he : c.succs[b]?.bind (·[jn]?) = some s
    · rw [ite_eq_left_of_eq_true _ _ (eq_true he), hops]; exact .inr ⟨jn, n, rfl, he, rfl⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false he)]; exact .inl rfl

theorem kept_take_not_drop {i : MInst} {ops : Array Operand} (hok : OpsOk ops i.clobbers) {n : Nat}
    {y : Operand × Loc} (hy : y ∈ (keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList).take n) :
    ∀ o ∈ (ops.toList.filter (·.kind == .def)).drop n, y.1.vreg ≠ o.vreg := by
  intro o ho he
  have h1 : y.1 ∈ (keptOps i ops.toList).take n := by
    have := List.mem_map_of_mem (f := Prod.fst) hy
    rwa [List.map_take, keptPairs_fst, spillPairs_fst] at this
  have h2 : y.1 ∈ (ops.toList.filter (·.kind == .def)).take n := by
    unfold keptOps at h1
    split at h1
    · exact h1
    · rw [List.take_take] at h1
      exact (List.take_sublist_take_left (Nat.min_le_left _ _)).subset h1
  have hnd := hok.defsNodup
  rw [← List.take_append_drop n (ops.toList.filter (·.kind == .def)), List.map_append,
    List.nodup_append] at hnd
  exact hnd.2.2 _ (List.mem_map_of_mem h2) _ (List.mem_map_of_mem ho) he

theorem mem_drop_defs {ops : Array Operand} {n : Nat} {o : Operand}
    (h : o ∈ (ops.toList.filter (·.kind == .def)).drop n) : o ∈ ops.toList ∧ o.kind = .def := by
  have := List.mem_filter.mp (List.mem_of_mem_drop h)
  exact ⟨this.1, by simpa using this.2⟩

/-- **An edge without arguments** feeds the successor's in-state. -/
theorem edge_noargs (hcfg : vc.cfg = .ok (succs, preds)) (hloc : SpillLocalOk vc)
    (hav : SpillAvail vc D) {c : CheckCtx} (hcvc : c.vc = vc) (hcs : c.succs = succs)
    {b : Nat} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) (hba : vb.branchArgs = #[])
    {T : MInst} {ops : Array Operand} (hT : vb.insts.back? = some T) (hTt : T.isTerminator = true)
    (hops : T.operands = .ok ops) (hok : OpsOk ops T.clobbers) {a : AState}
    (hg : Good vc (availAt vb.insts (availStart vc succs preds D b) vb.insts.size) a)
    (hkept : ∀ x ∈ keptPairs T (ops.zip (spillLocs ops T.clobbers)).toList,
      Sym.vreg x.1.vreg ∈ a.get x.2) :
    ∀ s ∈ (c.succs[b]?.getD #[]).toList, ∃ e, c.edge b s a = .ok e ∧
      (inState vc succs preds D s).le e = true := by
  intro s hs
  have hE := hloc.2.2 succs preds hcfg
  obtain ⟨ss, hss⟩ := cfg_succs_some hcfg (Array.getElem?_eq_some_iff.mp hvb).1
  rw [hcs, hss, Option.getD_some] at hs
  have hslt := cfg_succ_lt hcfg hss hs
  obtain ⟨sb, hsb⟩ : ∃ sb, vc.blocks[s]? = some sb := ⟨_, Array.getElem?_eq_getElem hslt⟩
  have hpar : sb.params = #[] := hE.noArgs b vb ss s sb hvb hba hss hs hsb
  have hs0 : s ≠ 0 := fun h => preds_empty hcfg (h ▸ hE.entry.2.1) hss hs
  obtain ⟨jj, hjj⟩ := List.mem_iff_getElem?.mp hs
  have hjj' : ss[jj]? = some s := by rw [← Array.getElem?_toList]; exact hjj
  have hF := edgeForget_cases (s := s) hcvc hvb hT hops a
  have hC : c.edgeCopy b s (c.edgeForget b s a) = .ok (c.edgeForget b s a) := by
    unfold CheckCtx.edgeCopy
    rw [hcvc, hvb, hsb]
    simp [hba, hpar, ensure]
    rfl
  refine ⟨c.edgeForget b s a, hC, le_of_mem fun l x hx => ?_⟩
  have hx' := (mem_get_mkState hx).1
  have keep : ∀ l x, x ∈ a.get l → (∀ o ∈ ops.toList, o.kind = .def → x ≠ .vreg o.vreg) →
      x ∈ (c.edgeForget b s a).get l := by
    intro l x hx hd
    rcases hF with hF | ⟨jn, n, -, -, hF⟩
    · rw [hF]; exact hx
    · rw [hF]
      exact mem_forgetOps hx fun o ho hk => hd o (mem_drop_defs ho).1 hk
  obtain ⟨hpos, hTk⟩ := back_get hT
  cases l with
  | reg r =>
    rcases inReg_mem hx' with ⟨h0, -, -⟩ | ⟨y, hy, hyr, rfl⟩
    · exact absurd h0 hs0
    · obtain ⟨p, vbp, ssp, j, hp, hvbp, hssp, hj, hyt⟩ := entryPairs_spec hy
      obtain ⟨rfl, huniq⟩ := preds_single hcfg hss hjj' hp
      rw [hvb] at hvbp
      cases hvbp
      rw [hss] at hssp
      cases hssp
      have hjs : ss[j]? = some s := by
        obtain ⟨hlt, he, -⟩ := List.idxOf?_eq_some_iff.mp hj
        rw [← Array.getElem?_toList, List.getElem?_eq_getElem hlt, he]
      obtain ⟨T', ops', hT', -, hops', hyk, htake⟩ := termEdgeDefs_spec hyt
      rw [hT] at hT'
      cases hT'
      rw [hops] at hops'
      cases hops'
      have hya := hkept y hyk
      rw [← hyr]
      rcases hF with hF | ⟨jn, n, hnd, hjn, hF⟩
      · rw [hF]; exact hya
      · rw [hF]
        have hjn' : ss[jn]? = some s := by rw [hcs, hss] at hjn; simpa using hjn
        have e1 := huniq jn hjn'
        have e2 := huniq j hjs
        have hyt' := htake jn n hnd (by omega)
        exact mem_forgetOps hya fun o ho _ he => by
          injection he with he
          exact kept_take_not_drop hok hyt' o ho he
  | save r =>
    obtain ⟨-, hr, rfl⟩ := inSave_mem hx'
    exact keep _ _ (hg.save r hr) fun _ _ _ h => by cases h
  | stack n cl =>
    obtain ⟨v, rfl, hn, hc, hD⟩ := inStack_mem hx'
    have hea := hav.edges succs preds hcfg b vb ss s sb hvb hss hs hsb v hD
    simp only [edgeAvail, hpar, Array.toList_empty, List.map_nil, List.idxOf?_nil] at hea
    refine keep _ _ (hg.home v cl n hea hc hn) fun o ho hk he => ?_
    injection he with he
    subst he
    have hsz : vb.insts.size - 1 + 1 = vb.insts.size := by omega
    rw [← hsz, availAt_succ hTk, availInst_eq hops, isDefOf_of ho hk, storedDefs_eq] at hea
    simp [hTt] at hea

end

end Backend.Proof.Spill
