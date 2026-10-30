import FV.Concurrency.ArmAllocLoopMem
import FV.E2E.RegLevelGoto
import FV.E2E.EmitLabels

/-!
# Layer 4b with the block-ending branches (T2, #311)

The scope of `ArmAllocLoopMem.arm_alloc_refines_loop` extended by the block-ending branches
(`jump`, `condBr`, `testBitAndBranch`), so that functions with more than one block are covered:

* `reach_bE`, `reach_rcbE`, `reach_cbE`: `Backend.Proof.reach_b`, `reach_rcb`, `reach_cb` with
  the facts layer 4b needs of the steps (`NoEvSteps`: the branch lines `b`, `b.cond`, `cbz`,
  `tbz` and the relaxation's inverted short branch have no event and are no store exclusive);
  a `b` dropped by `fallthrough` takes no step, and then the next line is the target's label;
* `realizes_gotoE`: `Backend.Proof.realizes_goto` with these facts; when no Arm step is taken
  (a `jump` to the next block, dropped by `fallthrough`), the successor is block `b + 1`
  (`succ_of_label`: the block labels are distinct, as `labelOffsets` defines every label once);
* `μR`: **the measure** of layer 4b with branches: the remaining items of the current block,
  ranked by the block (`(blocks - b) * itemBound + items`), which a fall-through `jump` decreases;
  the steps that stay in their block or end the function (`SameB`: every step but those of
  `GotoForm`, `csem_goto`) decrease it when they decrease `MConf.measure` (`opOutR_of`);
* `goto_op`: **the per-item obligation at a branch item** (`OpOutR`, `OpOutG` with `μR`);
* `MemScopeB`, `itemSim_br`: the scope `MemScopeL` with the branches, and its per-item obligation
  with moves, under `OkPriv`;
* **`arm_alloc_refines_br`**: `arm_alloc_refines_loop`'s conclusion for the functions of
  `MemScopeB`.
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot ArmPrecise Backend Backend.Proof AllocThread ThreadRefine
  VCodeThread Code VCodeEvents

/-! ## The branch lines on the machine -/

/-- The single-core steps `i < n` from `s` have no event and are no store exclusive. -/
def NoEvSteps (R : RL) (n : Nat) (s : ArmState) : Prop :=
  ∀ i < n, stepEvs (iterN R.step i s) = [] ∧ NoStx (iterN R.step i s)

/-- The branch instructions (any target, the relaxation's `.skip` too). -/
def BrInsn (x : Insn) : Prop :=
  (∃ l, x = .b l) ∨ (∃ c l, x = .bcond c l) ∨ (∃ nz w r l, x = .cbz nz w r l) ∨
    (∃ nz r bit l, x = .tbz nz r bit l)

/-- A branch line: no event, no store exclusive. -/
theorem br_noEv {R : RL} (hR : R.Wf) {j : Nat} {x : Insn} (hj : R.L[j]? = some (.ins x none))
    (hx : BrInsn x) {u : ArmState} (hprog : u.program = R.fb.program R.base)
    (hpc : Arm.r .PC u = R.pcOf j) (herr : Arm.r .ERR u = .None) : stepEvs u = [] ∧ NoStx u := by
  have hh : x.hooked = false ∧ insnKind x = none := by
    rcases hx with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
      exact ⟨rfl, rfl⟩
  exact line_noEv hR hj hh.1 hh.2 hprog hpc herr

theorem brInsn_of {bc : Insn} {t : Lbl}
    (hbc : (∃ c, bc = .bcond c t) ∨ (∃ nz w r, bc = .cbz nz w r t) ∨ (∃ nz r bit, bc = .tbz nz r bit t)) :
    BrInsn bc := by
  rcases hbc with ⟨c, rfl⟩ | ⟨nz, w, r, rfl⟩ | ⟨nz, r, bit, rfl⟩
  · exact .inr (.inl ⟨_, _, rfl⟩)
  · exact .inr (.inr (.inl ⟨_, _, _, _, rfl⟩))
  · exact .inr (.inr (.inr ⟨_, _, _, _, rfl⟩))

/-- A branch instruction is unhooked and not a `ret`. -/
theorem brInsn_hooked {x : Insn} (hx : BrInsn x) : x.hooked = false ∧ x ≠ .ret := by
  rcases hx with ⟨l, rfl⟩ | ⟨c, l, rfl⟩ | ⟨nz, w, r, l, rfl⟩ | ⟨nz, r, bit, l, rfl⟩ <;>
    exact ⟨rfl, by simp⟩

/-- **`reach_b` with the steps' facts**: the steps have no event and are no store exclusive; no
step only when the `b` was dropped, the next line defining the target; every state before the
last step is at an unhooked line other than `ret`. -/
theorem reach_bE {R : RL} (hR : R.Wf) {s : ArmState} {j0 : Nat} {x : Lbl} {Z T : List Line}
    (hdrop : R.L.drop j0 = relaxLines R.far (ftList (.ins (.b x) none :: Z)) ++ T) (hx : x ≠ .skip)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) :
    ∃ n jl, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧ R.L[jl]? = some (.label x) ∧
      NoEvSteps R n s ∧ (n = 0 → ∃ Z', Z = .label x :: Z') ∧
      ∀ i < n, AtNonRet R (iterN R.step i s) := by
  rcases ft_b x Z with ⟨Z', rfl, he⟩ | he
  · rw [he, ft_label, relaxLines_cons, relaxLine_label, List.singleton_append] at hdrop
    refine ⟨0, j0, ?_, drop_get hdrop, fun i hi => absurd hi (by omega),
      (And.intro (fun _ => ⟨Z', rfl⟩) fun i hi => absurd hi (by omega))⟩
    simp only [iterN]; rw [← hpc, Arm.w_irrelevant]
  · rw [he, relaxLines_cons, relaxLine_of_none rfl, List.singleton_append] at hdrop
    obtain ⟨a, jl, ha, hjl, hstep⟩ := step_branch hR (drop_get hdrop) (.inl rfl) hx hprog hpc herr
    refine ⟨1, jl, ?_, hjl, fun i hi => ?_,
      (And.intro (fun h => absurd h (by omega)) fun i hi => ?_)⟩
    · simp only [iterN]; rw [hstep, brCond_b ha]; rfl
    · obtain rfl : i = 0 := by omega
      exact br_noEv hR (drop_get hdrop) (.inl ⟨_, rfl⟩) hprog hpc herr
    · obtain rfl : i = 0 := by omega
      exact ⟨j0, .b x, none, drop_get hdrop, (brInsn_hooked (x := .b x) (.inl ⟨x, rfl⟩)).2,
        (brInsn_hooked (x := .b x) (.inl ⟨x, rfl⟩)).1, hpc⟩

/-- **`reach_rcb` with the steps' facts**, at least one step; every state before the last step is
at an unhooked line other than `ret`. -/
theorem reach_rcbE {R : RL} (hR : R.Wf) {s : ArmState} {j0 : Nat} {bc : Insn} {t : Lbl}
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
      NoEvSteps R n s ∧ 0 < n ∧ ∀ i < n, AtNonRet R (iterN R.step i s) := by
  have hform : bc = .b t ∨ (∃ c, bc = .bcond c t) ∨ (∃ nz w r, bc = .cbz nz w r t) ∨
      (∃ nz r bit, bc = .tbz nz r bit t) := .inr hbc
  rcases relaxLine_cases R.far bc with h | ⟨t', ht', h⟩
  · rw [h] at hdrop
    have hj := drop_get (Z := []) (by simpa using hdrop)
    obtain ⟨a, jl, ha, hjl, hstep⟩ := step_branch hR hj hform ht hprog hpc herr
    have h1 : NoEvSteps R 1 s := fun i hi => by
      obtain rfl : i = 0 := by omega
      exact br_noEv hR hj (brInsn_of hbc) hprog hpc herr
    have hAT : ∀ i < 1, AtNonRet R (iterN R.step i s) := fun i hi => by
      obtain rfl : i = 0 := by omega
      exact ⟨j0, bc, none, hj, (brInsn_hooked (brInsn_of hbc)).2,
        (brInsn_hooked (brInsn_of hbc)).1, hpc⟩
    rw [hc _ _ ha] at hstep
    cases cond
    · exact ⟨1, j0 + 1, by simp only [iterN]; rw [hstep]; rfl, by simp, by simp [h], h1,
        Nat.one_pos, hAT⟩
    · exact ⟨1, jl, by simp only [iterN]; rw [hstep]; rfl, fun _ => hjl, by simp, h1, Nat.one_pos,
        hAT⟩
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
    have hn0 := br_noEv hR hj0 (brInsn_of (t := .skip) (invertTo_form hbc)) hprog hpc herr
    have hAT0 : AtNonRet R s := ⟨j0, bc.invertTo .skip, none, hj0,
      (brInsn_hooked (brInsn_of (t := .skip) (invertTo_form hbc))).2,
      (brInsn_hooked (brInsn_of (t := .skip) (invertTo_form hbc))).1, hpc⟩
    rw [hcs hct _ _ ha] at hstep
    cases cond
    · exact ⟨1, j0 + 2, by simp only [iterN]; rw [hstep]; rfl, by simp, by simp [h],
        fun i hi => by
          obtain rfl : i = 0 := by omega
          exact hn0, Nat.one_pos, fun i hi => by
            obtain rfl : i = 0 := by omega
            exact hAT0⟩
    · have hprog1 : (Arm.w .PC (R.pcOf (j0 + 1)) s).program = R.fb.program R.base := by
        rw [Arm.w_program, hprog]
      have herr1 : Arm.r .ERR (Arm.w .PC (R.pcOf (j0 + 1)) s) = .None := by
        rw [Arm.r_of_w_different (by simp), herr]
      obtain ⟨a', jl, ha', hjl, hstep'⟩ := step_branch hR hj1 (.inl rfl) ht hprog1
        (Arm.r_of_w_same ..) herr1
      have hn1 := br_noEv hR hj1 (.inl ⟨_, rfl⟩) hprog1 (Arm.r_of_w_same ..) herr1
      rw [brCond_b ha'] at hstep'
      simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hstep
      refine ⟨2, jl, ?_, fun _ => hjl, by simp, fun i hi => ?_, by omega, fun i hi => ?_⟩
      · simp only [iterN]
        rw [hstep, hstep', Arm.w_of_w_shadow]
        rfl
      · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · exact hn0
        · simp only [iterN]
          rw [hstep]
          exact hn1
      · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · exact hAT0
        · simp only [iterN]
          rw [hstep]
          exact ⟨j0 + 1, .b t', none, hj1, (brInsn_hooked (x := .b t') (.inl ⟨t', rfl⟩)).2,
            (brInsn_hooked (x := .b t') (.inl ⟨t', rfl⟩)).1, Arm.r_of_w_same ..⟩

/-- **`reach_cb` with the steps' facts**, at least one step; every state before the last step is
at an unhooked line other than `ret`. -/
theorem reach_cbE {R : RL} (hR : R.Wf) {s : ArmState} {j0 : Nat} {bc : Insn} {t e : Lbl}
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
      R.L[jl]? = some (.label (if cond then t else e)) ∧ NoEvSteps R n s ∧ 0 < n ∧
      ∀ i < n, AtNonRet R (iterN R.step i s) := by
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
    obtain ⟨n, jl, hn, hjt, hjf, hne, hpos, hAT⟩ := reach_rcbE hR hdrop hform he (!cond)
      (hc' hct e) (fun _ env a ha => by rw [hcc hct env a ha, Bool.not_not]) hprog hpc herr
    refine ⟨n, jl, hn, ?_, hne, hpos, hAT⟩
    cases cond
    · simpa using hjt rfl
    · have hd' : R.L.drop jl = [Line.label L] ++ relaxLines R.far (ftList Z') ++ T := by
        rw [hjf rfl, ← List.drop_drop, hdrop, List.drop_left, List.append_assoc]
      simpa using drop_get (by simpa using hd')
  · rw [hft, relaxLines_cons, List.append_assoc] at hdrop
    obtain ⟨n, jl, hn, hjt, hjf, hne, hpos, hAT⟩ := reach_rcbE hR hdrop hbc ht cond hc
      (fun hct' => hc' hct' .skip) hprog hpc herr
    cases cond
    · have hd1 : R.L.drop jl = relaxLines R.far (ftList (.ins (.b e) none :: Z)) ++ T := by
        rw [hjf rfl, ← List.drop_drop, hdrop, List.drop_left]
      have hs1 : (iterN R.step n s).program = R.fb.program R.base := by
        rw [hn, Arm.w_program, hprog]
      obtain ⟨n', jl', hn', hjl', hne', -, hAT'⟩ := reach_bE hR hd1 he hs1
        (by rw [hn]; exact Arm.r_of_w_same ..) (by rw [hn, Arm.r_of_w_different (by simp), herr])
      refine ⟨n + n', jl', ?_, by simpa using hjl', fun i hi => ?_, by omega, fun i hi => ?_⟩
      · rw [iterN_add, hn', hn, Arm.w_of_w_shadow]
      · rcases Nat.lt_or_ge i n with h | h
        · exact hne i h
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
          rw [iterN_add]
          exact hne' k (by omega)
      · rcases Nat.lt_or_ge i n with h | h
        · exact hAT i h
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
          rw [iterN_add]
          exact hAT' k (by omega)
    · exact ⟨n, jl, hn, by simpa using hjt rfl, hne, hpos, hAT⟩

/-! ## The block labels are distinct -/

/-- `labelOffsets` defines every label once. -/
theorem labelOffsets_go_nodup : ∀ {L : List Line} {off : Nat} {m0 m : Std.HashMap Lbl Nat},
    labelOffsets.go L off m0 = .ok m →
      (E2E.EmitLabels.defs L).Nodup ∧ ∀ l ∈ E2E.EmitLabels.defs L, m0.contains l = false
  | [], _, _, _, _ => ⟨List.nodup_nil, fun _ h => by simp at h⟩
  | ln :: L, off, m0, m, h => by
    cases ln with
    | label l =>
      simp only [labelOffsets.go] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · rename_i hc
        obtain ⟨ih1, ih2⟩ := labelOffsets_go_nodup h
        have hl : l ∉ E2E.EmitLabels.defs L := fun hm => by
          have := ih2 l hm
          simp [Std.HashMap.contains_insert] at this
        refine ⟨by simpa [E2E.EmitLabels.lineDef] using ⟨hl, ih1⟩, fun x hx => ?_⟩
        simp only [E2E.EmitLabels.defs_cons, E2E.EmitLabels.lineDef, Option.toList_some,
          List.singleton_append, List.mem_cons] at hx
        rcases hx with rfl | hx
        · simpa using hc
        · have := ih2 x hx
          rw [Std.HashMap.contains_insert, Bool.or_eq_false_iff] at this
          exact this.2
    | ins i t =>
      simp only [labelOffsets.go] at h
      simpa [E2E.EmitLabels.lineDef] using labelOffsets_go_nodup h
    | word a b =>
      simp only [labelOffsets.go] at h
      simpa [E2E.EmitLabels.lineDef] using labelOffsets_go_nodup h
    | data w =>
      simp only [labelOffsets.go] at h
      simpa [E2E.EmitLabels.lineDef] using labelOffsets_go_nodup h

/-- The blocks' labels are among the labels the blocks' lines define, in order. -/
theorem blocks_defs {c : FnCtx} {af : AFunc} :
    ∀ (bs : List (Label × Array AInst)) (ps ps' : Backend.PState) (body : List Line),
      blocksLinesE c af bs ps = .ok (body, ps') →
      (bs.map fun p => Lbl.block p.1).Sublist (E2E.EmitLabels.defs body)
  | [], _, _, _, _ => List.nil_sublist _
  | (l', code) :: bs, ps, ps', body, h => by
    simp only [blocksLinesE, bind, Except.bind] at h
    cases h1 : codeLinesE c af code.toList ps with
    | error e => rw [h1] at h; cases h
    | ok r =>
      rw [h1] at h
      obtain ⟨l1, ps1⟩ := r
      simp only at h
      cases h2 : blocksLinesE c af bs ps1 with
      | error e => rw [h2] at h; cases h
      | ok r2 =>
        rw [h2] at h
        obtain ⟨l2, ps2⟩ := r2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have ih := blocks_defs bs ps1 ps2 l2 h2
        simp only [List.map_cons, List.cons_append, E2E.EmitLabels.defs_cons,
          E2E.EmitLabels.lineDef, Option.toList_some, E2E.EmitLabels.defs_append]
        exact (ih.trans (List.sublist_append_right _ _)).cons_cons _

/-- **The allocated function's block labels are distinct** (as lines: `labelOffsets` defines
every label once). -/
theorem af_nodup {R : RL} (hR : R.Wf) : (R.af.blocks.toList.map fun p => Lbl.block p.1).Nodup := by
  obtain ⟨body, psF, hb, hL, -⟩ := emit_block hR.emit
  have hn := (labelOffsets_go_nodup (show labelOffsets.go R.fa.lines.toList 0 {} = .ok R.lm
    from hR.lm)).1
  rw [hL, E2E.EmitLabels.defs_append, (E2E.EmitLabels.relaxLines_spec _ _).1,
    E2E.EmitLabels.defs_append, (E2E.EmitLabels.ftList_spec _ body (Nat.le_refl _)).1] at hn
  exact (blocks_defs _ _ _ _ hb).nodup (List.nodup_append.1 (List.nodup_append.1 hn).1).1

theorem nodup_idx {α : Type} {l : List α} (h : l.Nodup) {i j : Nat} {x : α} (hi : l[i]? = some x)
    (hj : l[j]? = some x) : i = j := by
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.1 hi
  obtain ⟨hj', e⟩ := List.getElem?_eq_some_iff.1 hj
  exact (List.Nodup.getElem_inj h).1 e.symm

/-- **The block with the label of block `b + 1`** is block `b + 1`. -/
theorem succ_of_label {R : RL} (hR : R.Wf) {st b : Nat} {vs : VBlock} {items : Array RItem}
    (hvs : R.vc.blocks[st]? = some vs) (hit : R.rf.blocks[st]? = some items)
    {p : Label × Array AInst} (hp : R.af.blocks[b + 1]? = some p) (hl : p.1 = vs.label) :
    st = b + 1 := by
  obtain ⟨⟨-, -, -, hbl⟩, -⟩ := lowerRFunc_ok hR.alloc
  obtain ⟨code, -, haf⟩ := hbl st vs items hvs hit
  refine nodup_idx (af_nodup hR) (x := Lbl.block vs.label) ?_ ?_
  · simp [haf]
  · simp [hp, hl]

/-- The line after a block's code (code lines define no block label): the next block's label. -/
theorem head_label {c : FnCtx} {af : AFunc} {code : List AInst} {ps ps' : Backend.PState}
    {ls : List Line} (h : codeLinesE c af code ps = .ok (ls, ps')) {b : Nat} {L : Label}
    {Z : List Line} (hz : ls ++ nxtOf af b = .label (.block L) :: Z) :
    ∃ p, af.blocks[b + 1]? = some p ∧ p.1 = L := by
  cases ls with
  | cons ln ls =>
    simp only [List.cons_append, List.cons.injEq] at hz
    obtain ⟨rfl, -⟩ := hz
    have hc := E2E.EmitLabels.code_chunk
      (T := code.flatMap fun a => match a with | .inst m => m.targets | _ => []) code ps ps' _ h
      (fun m hm l hl => List.mem_flatMap.2 ⟨_, hm, by simpa using hl⟩)
    rcases hc.defs_in (.block L) (by simp [E2E.EmitLabels.lineDef]) with
      ⟨_, h, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩ <;> cases h
  | nil =>
    simp only [List.nil_append, nxtOf] at hz
    split at hz
    · rename_i p hp
      simp only [List.cons.injEq, Line.label.injEq, Lbl.block.injEq] at hz
      exact ⟨p, hp, hz.1⟩
    · cases hz

/-! ## The measure -/

/-- An upper bound of the blocks' item counts. -/
def itemBound (R : RL) : Nat := (R.rf.blocks.toList.map Array.size).sum + 1

/-- **The measure of layer 4b with branches**: the remaining items of the current block, ranked by
the block (a fall-through to the next block decreases it). -/
def μR (R : RL) : MConf CV ArmState → Nat
  | .run s => (R.rf.blocks.size - s.b) * itemBound R + s.its.length
  | _ => 0

/-- A return is below every item. -/
theorem μR_ret_lt {R : RL} {vals : List CV} {m : Loc → CV} {w : ArmState} {b : Nat} {it : RItem}
    {its : List RItem} {m' : Loc → CV} {w' : ArmState} :
    μR R (.ret vals m w) < μR R (.run ⟨b, it :: its, m', w'⟩) := by
  simp only [μR, List.length_cons]
  exact Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_add_left _ _)

theorem le_sum_of_mem' : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.sum
  | _ :: _, _, .head _ => by simp
  | _ :: _, _, .tail _ h => by have := le_sum_of_mem' h; simp; omega

theorem size_lt_itemBound {R : RL} {t : Nat} {items : Array RItem}
    (h : R.rf.blocks[t]? = some items) : items.size < itemBound R := by
  have hm : items.size ∈ R.rf.blocks.toList.map Array.size :=
    List.mem_map.2 ⟨items, Array.mem_toList_iff.2 (Array.mem_of_getElem? h), rfl⟩
  have := le_sum_of_mem' hm
  simp only [itemBound]
  omega

/-- A fall-through to block `b + 1` decreases the measure. -/
theorem μR_succ {R : RL} {b : Nat} {it : RItem} {its : List RItem} {m m' : Loc → CV}
    {w w' : ArmState} {items : Array RItem} (h : R.rf.blocks[b + 1]? = some items) :
    μR R (.run ⟨b + 1, items.toList, m', w'⟩) < μR R (.run ⟨b, it :: its, m, w⟩) := by
  have hb : b + 1 < R.rf.blocks.size := (Array.getElem?_eq_some_iff.1 h).1
  have hk := size_lt_itemBound h
  simp only [μR, List.length_cons, Array.length_toList]
  obtain ⟨d, hd⟩ : ∃ d, R.rf.blocks.size - b = d + 1 := ⟨R.rf.blocks.size - (b + 1), by omega⟩
  rw [hd, show R.rf.blocks.size - (b + 1) = d by omega, Nat.succ_mul]
  omega

/-- The successor `c'` stays in `c`'s block or ends the function. -/
def SameB (c c' : MConf CV ArmState) : Prop :=
  ∀ s, c = .run s → ∀ s', c' = .run s' → s'.b = s.b

theorem μR_lt {R : RL} {c c' : MConf CV ArmState} (hb : SameB c c')
    (h : c'.measure < c.measure) : μR R c' < μR R c := by
  match c, c' with
  | .run s, .run s' =>
    have e := hb s rfl s' rfl
    simp only [μR, MConf.measure] at h ⊢
    rw [e]
    omega
  | .run s, .ret .. => simp only [μR, MConf.measure] at h ⊢; omega
  | .run s, .halt _ => simp only [μR, MConf.measure] at h ⊢; omega
  | .ret .., _ => simp [MConf.measure] at h
  | .halt _, _ => simp [MConf.measure] at h

/-- The block-ending branches. -/
def BrForm (i : MInst) : Prop :=
  (∃ l, i = .jump l) ∨ (∃ t e kk, i = .condBr t e kk) ∨
    (∃ kd t e rn bit, i = .testBitAndBranch kd t e rn bit)

/-- The instructions whose step may go to another block. -/
def GotoForm (i : MInst) : Prop :=
  BrForm i ∨ (∃ info ti, i = .tryCall info ti) ∨ ∃ a ts c d e, i = .jtSequence a ts c d e

/-- `csem` goes to another block only at a `GotoForm`. -/
theorem csem_goto {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst} {uses : List CV}
    {w : ArmState} {outs : List CV} {w' : ArmState} {j : Nat}
    (h : csem F ctx X i uses w = some (outs, w', .goto j)) : GotoForm i := by
  cases hc : i.isCtl
  · cases csem_ctl hc h
  · cases i
    all_goals first
      | exact .inl (.inl ⟨_, rfl⟩)
      | exact .inl (.inr (.inl ⟨_, _, _, rfl⟩))
      | exact .inl (.inr (.inr ⟨_, _, _, _, _, rfl⟩))
      | exact .inr (.inl ⟨_, _, rfl⟩)
      | exact .inr (.inr ⟨_, _, _, _, _, rfl⟩)
      | (simp [MInst.isCtl] at hc; done)
      | skip
    all_goals exfalso
    all_goals simp only [csem, loopSem] at h
    all_goals (repeat' split at h) <;> simp_all

/-! ## Block-ending branches -/

/-- **`Backend.Proof.realizes_goto` with the steps' facts**: from `Q` at a branch item, the
machine reaches `Q` at the successor in `n` steps without events or store exclusives; with no
step only when the successor is the next block (a fall-through `jump`), which decreases `μR`. -/
theorem realizes_gotoE {R : RL} (hR : R.Wf) {s : ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : ArmState} {c' : MConf CV ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {i : MInst}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hbr : BrForm i)
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c') :
    ∃ n, Q R (iterN R.step n s) c' ∧ NoEvSteps R n s ∧
      (n = 0 → μR R c' < μR R (.run ⟨b, .op k allocs :: its, m, w⟩)) ∧
      ∀ i < n, AtNonRet R (iterN R.step i s) := by
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
    · simp [Proof.writeM]
  subst m2
  cases hn with
  | @goto _ st items' hk1 hsucc hitems =>
  have hwm : Proof.writeM m ((((ops2.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip
      ([] : List CV)).filter (·.1.1.isLate)) = m := by simp [Proof.writeM]
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
      R.L[jl]? = some (.label (.block vs.label)) ∧ NoEvSteps R n s ∧ (n = 0 → st = b + 1) ∧
      ∀ i < n, AtNonRet R (iterN R.step i s) := by
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
      obtain ⟨n, jl, hn, hjl, hne, h0, hAt⟩ := reach_bE hR (by simpa using hdrop) (by simp)
        (by rw [hst.prog]) hpc hst.err
      refine ⟨n, jl, hn, hjl, hne, fun hn0 => ?_, hAt⟩
      obtain ⟨Z', hZ⟩ := h0 hn0
      obtain ⟨p, hp, hpl⟩ := head_label h2 hZ
      exact succ_of_label hR hvs hitems hp (hpl.trans hlj)
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
      obtain ⟨n, jl, hn, hjl, hne, hpos, hAt⟩ := reach_cbE hR (by simpa using hdrop) hbc (by simp)
        (by simp) (kk.holds _ w)
        (fun env a ha => kind_brCond hst hkr _ ha)
        (fun hct e' env a ha => kind_brCond_inv hst hkr _ _ hct ha)
        (fun _ env a ha => kind_brCond hst hkr _ (by rwa [CondBrKind.insn_invertTo_invertTo] at ha))
        (by rw [hst.prog]) hpc hst.err
      refine ⟨n, jl, hn, ?_, hne, fun h0 => absurd h0 (by omega), hAt⟩
      rw [hjl, hU]
      rw [hjc t e kk rfl] at hlj
      simp only [MInst.targets] at hlj
      cases hcond : kk.holds U w <;> simp only [hcond] at hlj ⊢ <;> simp at hlj <;> rw [hlj] <;> simp
    · obtain ⟨nr, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
      obtain ⟨r', rfl, rfl⟩ := assign_one (n := nr) (sp := OpSpec.use)
        (mk := fun r => MInst.testBitAndBranch kd t e r bit)
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
      obtain ⟨n, jl, hn, hjl, hne, hpos, hAt⟩ := reach_cbE hR (by simpa using hdrop)
        (bc := .tbz (kd == .nz) (.x n') bit (.block t)) (.inr (.inr ⟨_, _, _, rfl⟩)) (by simp)
        (by simp) ((Arm.r (.GPR (rnum n')) s).getLsbD bit == (kd == .nz))
        (fun env a ha => brCond_tbz (by omega) ha s)
        (fun _ e' env a ha => by
          simp only [Insn.invertTo] at ha
          rw [brCond_tbz (by omega) ha s, beq_not_right])
        (fun _ env a ha => by
          simp only [Insn.invertTo, Bool.not_not] at ha
          exact brCond_tbz (by omega) ha s)
        (by rw [hst.prog]) hpc hst.err
      refine ⟨n, jl, hn, ?_, hne, fun h0 => absurd h0 (by omega), hAt⟩
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
  obtain ⟨n, jl, hn, hjl, hne, h0, hAt⟩ := hreach
  refine ⟨n, ?_, hne, fun hn0 => ?_, hAt⟩
  · rw [hn]
    exact q_entry hR hst0 hvs hitems hjl (Arm.r_of_w_same ..) (hst.pc _)
  · obtain rfl := h0 hn0
    exact μR_succ hitems

/-- The conclusion of `ItemSim` at one configuration with the measure `μR`. -/
abbrev OpOutR (R : RL) (ok : ArmState → Lab → Prop) (t : ArmState × Mon) (c : MConf CV ArmState)
    (ls : List Lab) : Prop :=
  Done R c ∨ ItemSimOut Policy.arm R.step ok (SrcStep R) (RelQ R) (PrivA R) (μR R) t c ls ∨
    (∃ evs c' φ, SrcStep R c evs c' ∧ Img (PrivA R) evs (evTr ls) φ) ∨ PrivW (PrivA R) (evTr ls)

/-- **The per-item obligation at a block-ending branch** (module doc): the Arm runs the branch
lines (no event, no store exclusive) to the successor's label, where `Q` holds; the source step
has no event; a run ending inside the branch (before reaching the successor) is at a line other
than `ret`. -/
theorem goto_opR {R : RL} (hR : R.Wf) {ok : ArmState → Lab → Prop} {s : ArmState} {mon : Mon}
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : ArmState}
    {evs0 : List Ev} {c0 : MConf CV ArmState}
    (hq : Q R s (OpC b k allocs its m w)) (hA : AInv R (OpC b k allocs its m w))
    (hs0 : SrcStep R (OpC b k allocs its m w) evs0 c0)
    (hform : ∀ vb i, R.vc.blocks[b]? = some vb → vb.insts[k]? = some i → BrForm i)
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm R.step ok (s, mon) ls t') :
    OpOutN R ok (μR R) (s, mon) (OpC b k allocs its m w) ls t' := by
  have hs0' := hs0
  cases hs0' with
  | @op _ _ _ _ _ _ vb i ops _ _ hvb hi hops hevs hfoot hst =>
  have hbr := hform vb i hvb hi
  have hak : akinds i = [] := by
    rcases hbr with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ <;> rfl
  have he : evs0 = [] := hevs.trans (cEvs_nil hak _ _)
  subst he
  rw [patch_nil] at hst
  obtain ⟨n, hq', hne, hμ, hAt⟩ := realizes_gotoE hR hq hvb hi hbr hst
  have hA' := aInv_step hR hq hA hst
  by_cases hN : n ≤ ls.length
  · obtain ⟨⟨s1, mon1⟩, r1, -⟩ := PRun.split (ls.take n) (ls.drop n)
      (by rw [List.take_append_drop]; exact hr)
    have hlen1 : (ls.take n).length = n := by simp; omega
    obtain ⟨hs1, hev1, -⟩ := prun_nil r1 fun i hi => hne i (by omega)
    rw [hlen1] at hs1
    simp only at hs1
    subst hs1
    refine .inr (.inl ⟨n, [], c0, _, fun _ => (0, 0), hN, ?_, hs0, r1, .inl ⟨hq', hA'⟩, img_nil hev1 _⟩)
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exact .inr (hμ h0)
    · exact .inl h0
  · obtain ⟨hs', hev, -⟩ := prun_nil hr fun i hi => hne i (by omega)
    refine .inr (.inr (.inr ⟨privW_of_nil hev, ?_⟩))
    rw [hs']
    exact hAt ls.length (by omega)

/-- **The per-item obligation at a block-ending branch** (module doc): the Arm runs the branch
lines (no event, no store exclusive) to the successor's label, where `Q` holds; the source step
has no event. -/
theorem goto_op {R : RL} (hR : R.Wf) {ok : ArmState → Lab → Prop} {s : ArmState} {mon : Mon}
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : ArmState}
    {evs0 : List Ev} {c0 : MConf CV ArmState}
    (hq : Q R s (OpC b k allocs its m w)) (hA : AInv R (OpC b k allocs its m w))
    (hs0 : SrcStep R (OpC b k allocs its m w) evs0 c0)
    (hform : ∀ vb i, R.vc.blocks[b]? = some vb → vb.insts[k]? = some i → BrForm i)
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm R.step ok (s, mon) ls t') :
    OpOutR R ok (s, mon) (OpC b k allocs its m w) ls :=
  (goto_opR hR hq hA hs0 hform hr).out

/-! ## The other items, with `μR` -/

/-- **The steps that stay in their block**: every step but those of a `GotoForm` instruction. -/
theorem sameB_step {R : RL} {b : Nat} {its : List RItem} {m : Loc → CV} {w : ArmState}
    {evs : List Ev} {c' : MConf CV ArmState} (h : SrcStep R (.run ⟨b, its, m, w⟩) evs c')
    (hng : ∀ k allocs its', its = .op k allocs :: its' → ∀ vb i, R.vc.blocks[b]? = some vb →
      vb.insts[k]? = some i → ¬ GotoForm i) :
    SameB (.run ⟨b, its, m, w⟩) c' := by
  intro s hs s' hs'
  injection hs with hs
  subst hs
  cases h with
  | move => cases hs'; rfl
  | @op _ k allocs its' _ _ vb i ops _ _ hvb hi hops hevs hfoot hst =>
    cases hst with
    | @op _ _ _ _ _ _ vb1 i1 ops1 outs outs' w' ctl m2 c'' hvb1 hi1 hops1 hsz hsem hlen hho hcl hn =>
      rw [hvb] at hvb1; cases hvb1; rw [hi] at hi1; cases hi1
      cases hn with
      | next _ => cases hs'; rfl
      | goto _ _ _ => exact absurd (csem_goto (R.sem_csem hsem)) (hng k allocs its' rfl vb i hvb hi)
      | ret _ => cases hs'
      | halt => cases hs'

/-- **From `MConf.measure` to `μR`**, at the configurations whose steps stay in their block. -/
theorem isOut_μR {R : RL} {ok : ArmState → Lab → Prop} {t : ArmState × Mon}
    {c : MConf CV ArmState} {ls : List Lab} (hng : ∀ evs c', SrcStep R c evs c' → SameB c c')
    (h : ItemSimOut Policy.arm R.step ok (SrcStep R) (RelQ R) (PrivA R) (fun c => c.measure) t c ls) :
    ItemSimOut Policy.arm R.step ok (SrcStep R) (RelQ R) (PrivA R) (μR R) t c ls := by
  obtain ⟨n, evs, c', t1, φ, hn, hpos, hs, hr1, hR1, hi⟩ := h
  exact ⟨n, evs, c', t1, φ, hn, hpos.imp id (μR_lt (hng _ _ hs)), hs, hr1, hR1, hi⟩

theorem opOutR_of {R : RL} {ok : ArmState → Lab → Prop} {t : ArmState × Mon}
    {c : MConf CV ArmState} {ls : List Lab} (hng : ∀ evs c', SrcStep R c evs c' → SameB c c')
    (h : OpOutG R ok t c ls) : OpOutR R ok t c ls := by
  rcases h with h | h | h | h
  · exact .inl h
  · exact .inr (.inl (isOut_μR hng h))
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

/-- `OpOut` (runs under any condition) gives `OpOutG` under `OkPriv`. -/
theorem opOut_okPriv {R : RL} {s : ArmState} {mon : Mon} {c : MConf CV ArmState}
    (h : ∀ ls t', PRun Policy.arm R.step (fun _ _ => True) (s, mon) ls t' → OpOut R (s, mon) c ls)
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm R.step (OkPriv R) (s, mon) ls t') :
    OpOutG R (OkPriv R) (s, mon) c ls := by
  rcases h ls t' (PRun.mono (fun _ _ _ => trivial) hr) with
    h | ⟨n, evs, c', t1, φ, hn, hpos, hs, hr1, hR1, hi'⟩ | h | h
  · exact .inl h
  · obtain ⟨t1', r1, -⟩ := PRun.split (ls.take n) (ls.drop n)
      (by rw [List.take_append_drop]; exact hr)
    obtain rfl := PRun.det (PRun.mono (fun _ _ _ => trivial) r1) hr1
    exact .inr (.inl ⟨n, evs, c', t1', φ, hn, hpos, hs, r1, hR1, hi'⟩)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

/-- The memory forms and LL/SC loops do not leave their block. -/
theorem noGoto_memFormL {ctx : FnCtx} {i : MInst} (h : MemFormL ctx i) : ¬ GotoForm i := by
  intro hg
  rcases hg with (⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩) | ⟨_, _, rfl⟩ |
      ⟨_, _, _, _, _, rfl⟩ <;>
    simp [MemFormL, MemForm, NoEvForm, MInst.isCtl] at h

/-! ## The scope with branches -/

/-- **The scope of `arm_alloc_refines_br`**: every instruction is a memory form, an LL/SC loop
(`MemFormL`) or a block-ending branch (`BrForm`). -/
def MemScopeB (R : RL) : Prop :=
  ∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst), R.vc.blocks[b]? = some vb →
    vb.insts[k]? = some i → MemFormL R.ctx i ∨ BrForm i

theorem memScopeB_of_memScopeL {R : RL} (h : MemScopeL R) : MemScopeB R :=
  fun b vb k i hb hi => .inl (h b vb k i hb hi)

/-- **The per-item obligation of the scope with branches, with moves**, for the measure `μR`. -/
theorem itemSim_br {R : RL} (hR : R.Wf) (hsc : MemScopeB R) :
    ItemSim Policy.arm R.step (OkPriv R) (SrcStep R) (RelQ R) (Done R) (μR R) (PrivA R) := by
  rintro ⟨s, mon⟩ c hqa ls t' hr
  match c with
  | .ret vals m w => exact .inl (.inl ⟨vals, m, w, rfl⟩)
  | .halt w => exact .inl (.inr (.inl ⟨w, rfl⟩))
  | .run ⟨b, its, m, w⟩ =>
  by_cases hS : ∃ evs c', SrcStep R (.run ⟨b, its, m, w⟩) evs c'
  case neg => exact .inl (.inr (.inr fun evs c' h => hS ⟨evs, c', h⟩))
  obtain ⟨evs0, c0, hs0⟩ := hS
  cases hs0 with
  | @move _ src dst its' =>
    have hng : ∀ evs c', SrcStep R (MvC b src dst its' m w) evs c' → SameB (MvC b src dst its' m w) c' :=
      fun evs c' h => sameB_step h fun _ _ _ e => by cases e
    rcases move_op hR hqa hr with h | h
    · exact .inr (.inl (isOut_μR hng h))
    · exact .inr (.inr (.inr h))
  | @op _ k allocs its' _ _ vb i ops _ _ hvb hi hops hevs hfoot hst =>
    have hs : SrcStep R (OpC b k allocs its' m w) _ _ := .op hvb hi hops hevs hfoot hst
    rcases RelQ.op' hqa hs with ⟨hq, hA⟩ | ⟨rfl, vals, m', w', rfl⟩
    case inr => exact .inr (.inl (itemSimOut_retμ hs μR_ret_lt))
    have uniq : ∀ vb' i', R.vc.blocks[b]? = some vb' → vb'.insts[k]? = some i' → i' = i :=
      fun vb' i' h1 h2 => by rw [hvb] at h1; cases h1; rw [hi] at h2; cases h2; rfl
    rcases hsc b vb k i hvb hi with hl | hbr
    · have hng : ∀ evs c', SrcStep R (OpC b k allocs its' m w) evs c' →
          SameB (OpC b k allocs its' m w) c' :=
        fun evs c' h => sameB_step h fun k1 allocs1 its1 e vb' i' h1 h2 => by
          injection e with e1 e2
          injection e1 with e3 e4
          subst e3
          exact uniq vb' i' h1 h2 ▸ noGoto_memFormL hl
      refine opOutR_of hng ?_
      rcases hl with (h | h | ⟨ty, rt, rn, fl, rfl, hfo⟩ | ⟨ty, rt, rn, fl, rfl, hfo⟩) | hl | hl
      · exact opOut_okPriv (fun ls t' hr => noev_op hR hq hA hs
          (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ h) hr) hr
      · exact opOut_okPriv (fun ls t' hr => fence_op hR hq hA hs
          (fun vb' i' h1 h2 => (uniq vb' i' h1 h2).trans h) hr) hr
      · exact opOut_okPriv (fun ls t' hr => oneEv_op hR hq hA hs
          (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ ldar_form hfo) hr) hr
      · exact opOut_okPriv (fun ls t' hr => oneEv_op hR hq hA hs
          (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ stlr_form hfo) hr) hr
      · exact rmw_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ hl) hr
      · exact cas_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ hl) hr
    · exact goto_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ hbr) hr

/-- **Layer 4b with the block-ending branches** (module doc): every precise Arm run under
`OkPriv` from a `Q`-related state realizes a run of the allocated code (`MTRun`) with `Refines`
(equal kinds, the addresses outside the world private, the atomic updates monitor pairs), up to the
allocated code's return, trap or undefined behaviour (`Done`), for functions whose instructions
are event-free, `fence`, `ldar`, `stlr`, LL/SC loops or block-ending branches (`MemScopeB`),
whatever their moves. -/
theorem arm_alloc_refines_br {R : RL} (hR : R.Wf) (hsc : MemScopeB R)
    {s : ArmState} {mon : Mon} {c : MConf CV ArmState} (hq : Q R s c) (hA : AInv R c)
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm R.step (OkPriv R) (s, mon) ls t') :
    ∃ n trS cE ψ, n ≤ ls.length ∧ MTRun R.vc R.rf R.sem ckeep (cEvs R.F R.ctx) c trS cE ∧
      Refines (· = ·) (PrivA R) (MonPair (evTr (ls.take n))) (PrepThread.conv trS)
        (PrepThread.conv (evTr (ls.take n))) ψ ∧ (n = ls.length ∨ Done R cE) := by
  obtain ⟨n, trS, cE, ψ, hn, hs, href, hend⟩ :=
    refines_of_itemSim (itemSim_br hR hsc) hr (RelQ.of hq hA)
  exact ⟨n, trS, cE, ψ, hn, mtrun_of_srun hs, href, hend⟩

end Concurrency.ArmAllocThread
