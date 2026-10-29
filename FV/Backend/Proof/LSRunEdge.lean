module

public import FV.Backend.Proof.LSRun
public import FV.Backend.Proof.LSTermFixed
public import FV.Backend.Proof.SpillStep4Edge

@[expose] public section

/-!
# The checker accepts the Lean allocator's validated plans (V4b-3, #275): edges without arguments

`last_edges`: after the last instruction of a block without branch arguments (`Post`), every
edge to a successor (the defs dead on it forgotten) gives a state that contains the successor's
in-state.

The successor `s` has no parameters (`EdgesOk.noArgs`), so the edge's copy is the identity and
only `edgeForget` acts. A symbol of `s`'s in-state is a callee-saved entry value (`Post.callee`),
a result of the terminator (a `try_call`) on this edge, in its fixed register (`term_kept_fixed`,
`Post.results`, not forgotten: `kept_take_not_drop`), or a vreg of `D s`: available at the end of
the block, so no def of the terminator (whose defs are never stored), live at its post position
(`edgeOk`) and born nowhere inside it, hence kept in its location (`Post.thru`).
-/

namespace Backend.Proof.LS

open Backend Backend.LinearScan Backend.Proof Backend.Proof.Spill
open Backend.LinearScan.Ctx (Parts blockItems)

/-- The entry location of a vreg some entry pair carries, when every entry pair is fixed. -/
private theorem entryLoc_fixed {vc : VCode} {c : LinearScan.Ctx} {s v : Nat}
    (hfix : ∀ y ∈ entryPairs vc c.fn.succs c.fn.preds s, ∃ p, y.1.con = .fixed p)
    (hy : ∃ y ∈ entryPairs vc c.fn.succs c.fn.preds s, y.1.vreg = v) :
    ∃ y ∈ entryPairs vc c.fn.succs c.fn.preds s, y.1.vreg = v ∧ ∃ p, y.1.con = .fixed p ∧
      entryLoc vc c s v = .reg p := by
  unfold entryLoc
  cases hf : ((entryPairs vc c.fn.succs c.fn.preds s).map (·.1)).find? (·.vreg == v) with
  | none =>
    obtain ⟨y, hy, rfl⟩ := hy
    have := List.find?_eq_none.mp hf y.1 (List.mem_map_of_mem hy)
    simp at this
  | some o =>
    have hv : o.vreg = v := by simpa using List.find?_some hf
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hf)
    obtain ⟨p, hp⟩ := hfix y hy
    refine ⟨y, hy, hv, p, hp, ?_⟩
    simp only [hp]

section
variable {vc : VCode} {c : LinearScan.Ctx} {rf : RFunc} {D : Nat → Nat → Bool}
  (H : Hyps vc c rf D)
include H

/-- The last instruction of a block without branch arguments: `Post` feeds every successor's
in-state. -/
theorem last_edges {b : Nat} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) {k : Nat}
    (hk : k + 1 = vb.insts.size) (hba : vb.branchArgs = #[]) {i : MInst}
    (hi : vb.insts[k]? = some i) {os : Array Operand} (hos : i.operands = .ok os)
    {A : Nat → Bool} (hA : A = availAt vb.insts (availStart vc c.fn.succs c.fn.preds D b) k)
    {a : AState} (hpost : Post c rf (c.fn.start.getD b 0 + k) i os A a) :
    ∀ s ∈ ((ctxOf vc c rf).succs[b]?.getD #[]).toList, ∃ e, (ctxOf vc c rf).edge b s a = .ok e ∧
      (inState vc c rf D s).le e = true := by
  intro s hs
  have hf := H.fn
  have hcfg := hf.cfg
  have hE := H.loc.2.2 _ _ hcfg
  obtain ⟨ss, hss⟩ := cfg_succs_some hcfg (Array.getElem?_eq_some_iff.mp hvb).1
  have hsc : (ctxOf vc c rf).succs = c.fn.succs := rfl
  rw [hsc, hss, Option.getD_some] at hs
  have hslt := cfg_succ_lt hcfg hss hs
  obtain ⟨sb, hsb⟩ : ∃ sb, vc.blocks[s]? = some sb := ⟨_, Array.getElem?_eq_getElem hslt⟩
  have hpar : sb.params = #[] := hE.noArgs b vb ss s sb hvb hba hss hs hsb
  have hs0 : s ≠ 0 := fun h => preds_empty hcfg (h ▸ hE.entry.2.1) hss hs
  obtain ⟨jj, hjj⟩ := List.mem_iff_getElem?.mp hs
  have hjj' : ss[jj]? = some s := by rw [← Array.getElem?_toList]; exact hjj
  have hback : vb.insts.back? = some i := by
    rw [Array.back?_eq_getElem?, ← hk, Nat.add_sub_cancel]; exact hi
  have hTt : i.isTerminator = true := by
    obtain ⟨T, hT, hTt⟩ := cfg_last hcfg hvb
    rw [hback] at hT
    cases hT
    exact hTt
  obtain ⟨os', hos', hok, -⟩ := H.loc.1 b vb k i hvb hi
  rw [hos] at hos'
  cases hos'
  have hF := edgeForget_cases (c := ctxOf vc c rf) (s := s) rfl hvb hback hos a
  have hC : (ctxOf vc c rf).edgeCopy b s ((ctxOf vc c rf).edgeForget b s a) =
      .ok ((ctxOf vc c rf).edgeForget b s a) := by
    unfold CheckCtx.edgeCopy
    simp only [ctxOf]
    rw [hvb, hsb]
    simp [hba, hpar, ensure]
    rfl
  refine ⟨_, hC, le_of_mem fun l x hx => ?_⟩
  have keep : ∀ l x, x ∈ a.get l → (∀ o ∈ os.toList, o.kind = .def → x ≠ .vreg o.vreg) →
      x ∈ ((ctxOf vc c rf).edgeForget b s a).get l := by
    intro l x hx hd
    rcases hF with hF | ⟨jn, n, -, -, hF⟩
    · rw [hF]; exact hx
    · rw [hF]
      exact mem_forgetOps hx fun o ho hk => hd o (mem_drop_defs ho).1 hk
  obtain ⟨hlv, hm⟩ := mem_inState hx
  rcases hm with ⟨v, rfl, hv, hcov, hav, hl⟩ | ⟨r, rfl, ⟨rfl, hr, hsv⟩ | ⟨rfl, -, hr⟩⟩
  · by_cases hy : ∃ y ∈ entryPairs vc c.fn.succs c.fn.preds s, y.1.vreg = v
    · -- a result of the terminator on this edge, in its fixed register
      have hpair : ∀ y ∈ entryPairs vc c.fn.succs c.fn.preds s,
          (∃ j, os[j]? = some y.1 ∧ j ∈ keptIdx i os) ∧ y.1.kind = .def ∧
          ∀ jn n, i.normalDead = some (jn, n) → ss[jn]? = some s →
            y ∈ (keptPairs i (os.zip (spillLocs os i.clobbers)).toList).take n := by
        intro y hy
        obtain ⟨p, vbp, ssp, j, hp, hvbp, hssp, hj, hyt⟩ := entryPairs_spec hy
        obtain ⟨rfl, huniq⟩ := preds_single hcfg hss hjj' hp
        rw [hvb] at hvbp
        cases hvbp
        rw [hss] at hssp
        cases hssp
        have hjs : ss[j]? = some s := by
          obtain ⟨hlt, he, -⟩ := List.idxOf?_eq_some_iff.mp hj
          rw [← Array.getElem?_toList, List.getElem?_eq_getElem hlt, he]
        obtain ⟨T', ops', hT', -, hops', hyk, htake⟩ := termEdgeDefs_spec hyt
        rw [hback] at hT'
        cases hT'
        rw [hos] at hops'
        cases hops'
        refine ⟨keptOps_idx ?_, (mem_keptPairs hyk).2, fun jn n hnd hjn => htake jn n hnd ?_⟩
        · have := List.mem_map_of_mem (f := Prod.fst) hyk
          rwa [keptPairs_fst, spillPairs_fst] at this
        · rw [huniq jn hjn, huniq j hjs]
      have hfix : ∀ y ∈ entryPairs vc c.fn.succs c.fn.preds s, ∃ p, y.1.con = .fixed p :=
        fun y hy => by
          obtain ⟨⟨j, hj, hjk⟩, -⟩ := hpair y hy
          exact term_kept_fixed hTt hos hj hjk
      obtain ⟨y, hy', rfl, p, hp, hel⟩ := entryLoc_fixed hfix hy
      rw [hel] at hl
      subst hl
      obtain ⟨⟨j, hj, hjk⟩, hyd, htk⟩ := hpair y hy'
      have hya := hpost.results hTt j y.1 p hj hyd hjk hp
      rcases hF with hF | ⟨jn, n, hnd, hjn, hF⟩
      · rw [hF]; exact hya
      · rw [hF]
        have hjn' : ss[jn]? = some s := by rw [hsc, hss] at hjn; simpa using hjn
        exact mem_forgetOps hya fun o ho _ he => by
          injection he with he
          exact kept_take_not_drop hok (htk jn n hnd hjn') o ho he
    · -- a vreg of `D s`, live and available across the terminator
      have hD : D s v = true := by
        rw [entryStored_eq] at hav
        rcases Bool.or_eq_true_iff.mp hav with h | h
        · exact h
        · obtain ⟨y, hyy, rfl⟩ := List.mem_map.mp (List.contains_iff_mem.mp h)
          exact absurd ⟨y, hyy, rfl⟩ hy
      rw [entryLoc_none fun y hy' he => hy ⟨y, hy', he⟩] at hl
      subst hl
      have hea := H.avail.edges _ _ hcfg b vb ss s sb hvb hss hs hsb v hD
      simp only [edgeAvail, hpar, Array.toList_empty, List.map_nil, List.idxOf?_nil] at hea
      rw [← hk, availAt_succ hi, availInst_eq hos, ← hA] at hea
      have hnd : isDefOf os v = false := by
        cases hd : isDefOf os v
        · rfl
        · rw [hd, storedDefs_eq] at hea
          simp [hTt] at hea
      rw [hnd] at hea
      simp only [Bool.false_eq_true, ite_false] at hea
      have hnot : ∀ o ∈ os.toList, o.kind = .def → o.vreg ≠ v := fun o ho hk' he => by
        have := isDefOf_of ho hk'
        rw [he, hnd] at this
        cases this
      -- live at the terminator's post position (`edgeOk`, no parameters)
      have hps : c.fn.params s = [] := by rw [hf.params hsb, hpar]; rfl
      have hlast : c.lastOf b = c.fn.start.getD b 0 + k := by
        unfold LinearScan.Ctx.lastOf
        rw [hf.startSucc hvb]
        omega
      have hedge := H.plan.edge v hv s hslt hcov b (mem_preds hcfg hss hs)
      simp only [LinearScan.Ctx.edgeOk, hps, List.idxOf?_nil, hlast] at hedge
      -- no birth inside the terminator
      have hpa : c.fn.paramAt (c.fn.start.getD b 0 + k) v = false := by
        have hbl := hf.blkGetD hvb (k := k) (by omega)
        have hsg : c.fn.succs.getD b #[] = ss := by
          rw [Array.getD_eq_getD_getElem?, hss, Option.getD_some]
        unfold Fn.paramAt
        simp only [hbl, hsg]
        split
        · rename_i t ht
          have htm : t ∈ ss.toList := by rw [ht]; exact List.mem_singleton_self t
          obtain ⟨tb, htb⟩ : ∃ tb, vc.blocks[t]? = some tb :=
            ⟨_, Array.getElem?_eq_getElem (cfg_succ_lt hcfg hss htm)⟩
          rw [hf.params htb, hE.noArgs b vb ss t tb hvb hba hss htm htb]
          simp
        · simp
      have hnb : ∀ s', pos (c.fn.start.getD b 0 + k) 0 < s' →
          s' ≤ pos (c.fn.start.getD b 0 + k) 4 → c.birthOk v s' = false := by
        intro s' h1 h2
        rw [Bool.eq_false_iff]
        intro hbo
        obtain ⟨sl, hsl, rfl⟩ : ∃ sl, sl < 5 ∧ s' = pos (c.fn.start.getD b 0 + k) sl :=
          ⟨s' - 5 * (c.fn.start.getD b 0 + k), by unfold pos at *; omega,
            by unfold pos at *; omega⟩
        obtain ⟨-, hb1, hb2⟩ := birthOk_pos hsl hbo
        have hsl0 : sl ≠ 0 := by unfold pos at h1; omega
        by_cases hsl1 : sl = 1
        · subst hsl1
          rw [hpa] at hb1
          cases hb1 rfl
        obtain ⟨o, ho, hk', hv', -⟩ := hb2 hsl0 hsl1
        rw [(hf.opsGetD hvb hi hos).2.1] at ho
        exact hnot o ho hk' hv'
      have hI := covI_of_nobirth H.plan hv hedge (by unfold pos; omega) hnb
      have hin := hpost.thru v hv hI hea hnot hlv
      exact keep _ _ hin fun o ho hk' he => by
        injection he with he
        exact hnot o ho hk' he.symm
  · -- an unsaved callee-saved register's entry value
    have hns : r ∉ rf.saved := hsv.resolve_left hs0
    exact keep _ _ ((hpost.callee r hr).2 hns) fun _ _ _ h => by cases h
  · -- a saved callee-saved register's entry value
    exact keep _ _ ((hpost.callee r (H.build.saved r hr)).1 hr) fun _ _ _ h => by cases h

end

end Backend.Proof.LS
