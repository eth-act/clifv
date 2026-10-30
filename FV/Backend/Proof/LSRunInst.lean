import FV.Backend.Proof.LSFacts
import FV.Backend.Proof.SpillStep4Cfg
import FV.Backend.Proof.LSRun

/-!
# The checker accepts the Lean allocator's validated plans (V4b-3, #275): one instruction

`inst_runs`: the items of one instruction (the moves into its operand registers, the restores
before a `Rets`, the instruction, the moves out of its def registers) pass the checker from a
state that is `Good` at the instruction's start, and leave `Post`: the vregs live across it that
it does not define stay in their locations, the defs it stores are in theirs, the kept defs of a
terminator are in their fixed registers, the callee-saved registers keep their entry values.
-/

namespace Backend.Proof.LS

open Backend Backend.LinearScan Backend.Proof Backend.Proof.Spill
open Backend.LinearScan.Ctx (Parts blockItems)

/-- `Runs.moves` for a possibly empty list of moves (an empty one may follow the terminator). -/
private theorem moves_runs' {cc : CheckCtx} {vb : VBlock} {k : Nat} (ms : List (Loc × Loc))
    (a : AState) (hk : ms ≠ [] → k ≠ vb.insts.size)
    (hc : ∀ m ∈ ms, cc.checkMove s!"block {vb.label}" m.1 m.2 = .ok ())
    (hsd : ∀ m ∈ ms, ∀ m' ∈ ms, m.1 ≠ m'.2) (hnd : (ms.map (·.2)).Nodup)
    (hi : ∀ m ∈ ms, ∃ i, m.2.index = some i ∧ i < a.size) :
    Runs cc vb k (ms.map Spill.mv) a fun k' a' => k' = k ∧ a'.size = a.size ∧
      (∀ m ∈ ms, a'.get m.2 = a.get m.1) ∧ ∀ l, (∀ m ∈ ms, m.2 ≠ l) → a'.get l = a.get l := by
  by_cases h : ms = []
  · subst h
    exact Runs.nil ⟨rfl, rfl, by simp, fun _ _ => rfl⟩
  · exact Runs.moves (hk h) ms a hc hsd hnd hi

/-- The def vregs of operand–location pairs are those of the operands. -/
private theorem defVregs_zip {os : Array Operand} {allocs : Array Loc} (h : os.size = allocs.size) :
    (((os.zip allocs).toList.filter (·.1.kind == .def)).map (·.1.vreg)) =
      (os.toList.filter (·.kind == .def)).map (·.vreg) := by
  have hfst : (os.zip allocs).toList.map Prod.fst = os.toList := by
    rw [Array.toList_zip]
    exact List.map_fst_zip (by simp [h])
  rw [← hfst, List.filter_map, List.map_map]
  rfl

/-- A location of the plan is a register or a stack slot, never a save slot. -/
private theorem loc_ne_save (c : LinearScan.Ctx) (v : Nat) (r : Reg) : c.loc v ≠ .save r := by
  unfold LinearScan.Ctx.loc Fn.loc
  split <;> simp

/-- The restores in front of instruction `k`: those of `rf.saved` before a `Rets`, else none. -/
private theorem restores_eq {vb : VBlock} {k : Nat} {i : MInst} (hi : vb.insts[k]? = some i)
    {L : List Reg} (hL : L.Nodup) : ∃ RS : List (Loc × Loc),
      (if vb.insts[k]? matches some (.rets _) then restoresOf L else []) = RS.map Spill.mv ∧
      (RS.map (·.2)).Nodup ∧
      (∀ m ∈ RS, (∃ us, i = .rets us) ∧ ∃ r ∈ L, m = (.save r, .reg r)) ∧
      ((∃ us, i = .rets us) → ∀ r ∈ L, (Loc.save r, Loc.reg r) ∈ RS) := by
  rw [hi]
  by_cases hR : ∃ us, i = .rets us
  · obtain ⟨us, rfl⟩ := hR
    refine ⟨L.map fun r => (.save r, .reg r), restoresOf_eq _, ?_, fun m hm => ?_,
      fun _ r hr => List.mem_map_of_mem hr⟩
    · rw [List.map_map]
      exact nodup_map_of_inj (g := id) (by simpa using hL) fun x _ y _ h => by simpa using h
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
      exact ⟨⟨us, rfl⟩, r, hr, rfl⟩
  · refine ⟨[], ?_, List.nodup_nil, fun _ h => absurd h List.not_mem_nil, fun h => absurd h hR⟩
    cases i <;> first | rfl | exact absurd ⟨_, rfl⟩ hR

section
variable {vc : VCode} {c : LinearScan.Ctx} {rf : RFunc} {D : Nat → Nat → Bool}
  (H : Hyps vc c rf D)
include H

/-- **One instruction**: its items keep the invariant (`Post`). -/
theorem inst_runs {b : Nat} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) {p : Parts}
    (hp : c.blockParts b = .ok p) {k : Nat} {args : List RItem} {io : IOut}
    (hk : p.insts[k]? = some (args, io)) {i : MInst} (hi : vb.insts[k]? = some i)
    {os : Array Operand} (hos : i.operands = .ok os) {A : Nat → Bool}
    (hA : A = availAt vb.insts (availStart vc c.fn.succs c.fn.preds D b) k) {a : AState}
    (hg : Good c rf A (pos (c.fn.start.getD b 0 + k) 0) a) :
    Runs (ctxOf vc c rf) vb k (io.pre.map LinearScan.mv ++
      (if vb.insts[k]? matches some (.rets _) then restoresOf rf.saved else []) ++
        [.op k io.allocs] ++ io.post.map LinearScan.mv) a
      fun k' a' => k' = k + 1 ∧ Post c rf (c.fn.start.getD b 0 + k) i os A a' := by
  have hf := H.fn
  have hpf := H.plan
  obtain ⟨hgo, -, hgi⟩ := hf.opsGetD hvb hi hos
  have hkl : k < vb.insts.size := (Array.getElem?_eq_some_iff.mp hi).1
  have hkn : k ≠ vb.insts.size := by omega
  obtain ⟨ops', hops', hok, hrets⟩ := H.loc.1 b vb k i hvb hi
  rw [hos] at hops'
  cases hops'
  have hcls : ∀ o ∈ os.toList, c.fn.clsOf o.vreg = o.cls := fun o ho =>
    hf.cls _ _ (H.loc.2.1.1 b vb k i os hvb hi hos o ho)
  have IF := H.inst _ i os io hgi hgo hok hcls ((partsFacts hp).inst k args io hk).1
  obtain ⟨hmPre, hmOp, hmPost⟩ : (∀ m ∈ io.pre, LinearScan.mv m ∈ blockItems vb p []) ∧
      RItem.op k io.allocs ∈ blockItems vb p [] ∧
      (∀ m ∈ io.post, LinearScan.mv m ∈ blockItems vb p []) :=
    (piece_mem (L := []) hk).2
  have hslot := H.build.slots b vb p hvb hp
  have hnots := fun r hr hns => H.build.notSaved r hr hns b vb p hvb hp
  have hsz := hg.size
  generalize hgdef : c.fn.start.getD b 0 + k = g at hgo hgi hg IF ⊢
  -- operand–location pairs
  have hPj : ∀ x ∈ (os.zip io.allocs).toList, ∃ j, os[j]? = some x.1 ∧ io.allocs[j]? = some x.2 :=
    fun x hx => zip_get hx
  have hPo : ∀ x ∈ (os.zip io.allocs).toList, x.1 ∈ os.toList := fun x hx => by
    obtain ⟨j, hj, -⟩ := hPj x hx
    exact mem_of_get hj
  have hPreg : ∀ x ∈ (os.zip io.allocs).toList, ∃ r, x.2 = .reg r ∧ r.allocatable = true :=
    fun x hx => by
      obtain ⟨j, hj, hl⟩ := hPj x hx
      obtain ⟨r, hr, ha, -⟩ := IF.allocs j x.1 hj
      rw [hl] at hr
      exact ⟨r, Option.some.inj hr, ha⟩
  -- moves into operand registers
  have hpreD : ∀ m ∈ io.pre, ∃ r, m.2 = .reg r := fun m hm => by
    obtain ⟨j, o, hj, -, -, hl⟩ := IF.pre m hm
    obtain ⟨r, hr, -⟩ := IF.allocs j o hj
    rw [hl] at hr
    exact ⟨r, Option.some.inj hr⟩
  have hR1 := moves_runs' (cc := ctxOf vc c rf) (vb := vb) (k := k) io.pre a (fun _ => hkn)
    (fun m hm => by
      obtain ⟨j, o, hj, -, hsrc, hl⟩ := IF.pre m hm
      obtain ⟨r, hr, ha, hrc⟩ := IF.allocs j o hj
      rw [hl] at hr
      have hm2 : m.2 = .reg r := Option.some.inj hr
      rw [hsrc]
      refine checkMove_ok (cl := o.cls) (loc_cls hpf (hcls o (mem_of_get hj)))
        (.inl ⟨r, hm2, ha, hrc⟩) (fun s c' he => hslot _ (hmPre m hm) _ ?_ s c' he)
        (fun s c' he => by rw [hm2] at he; cases he) (.inr (by rw [hm2]; rfl))
      rw [← hsrc]
      simp [RItem.locs, LinearScan.mv])
    IF.preSrc IF.preNodup
    (fun m hm => by
      obtain ⟨r, hr⟩ := hpreD m hm
      obtain ⟨j, o, hj, -, -, hl⟩ := IF.pre m hm
      obtain ⟨r', hr', ha, -⟩ := IF.allocs j o hj
      rw [hl, hr] at hr'
      cases hr'
      obtain ⟨n, h1, h2⟩ := reg_index ha
      exact ⟨n, by rw [hr]; exact h1, by omega⟩)
  -- the restores in front of a `Rets`
  obtain ⟨RS, hRSe, hRSnd, hRSm, hRSall⟩ := restores_eq hi H.build.savedNodup
  rw [hRSe, LS.mv_eq]
  have hR2 : ∀ a1 : AState, a1.size = 128 + 2 * rf.spillSlots →
      Runs (ctxOf vc c rf) vb k (RS.map Spill.mv) a1 fun k' a' => k' = k ∧ a'.size = a1.size ∧
        (∀ m ∈ RS, a'.get m.2 = a1.get m.1) ∧ ∀ l, (∀ m ∈ RS, m.2 ≠ l) → a'.get l = a1.get l :=
    fun a1 ha1 => moves_runs' RS a1 (fun _ => hkn)
      (fun m hm => by
        obtain ⟨-, r, hr, rfl⟩ := hRSm m hm
        exact checkMove_restore (cc := ctxOf vc c rf) hr (H.build.saved r hr))
      (fun m hm m' hm' => by
        obtain ⟨-, r, -, rfl⟩ := hRSm m hm
        obtain ⟨-, r', -, rfl⟩ := hRSm m' hm'
        simp)
      hRSnd
      (fun m hm => by
        obtain ⟨-, r, hr, rfl⟩ := hRSm m hm
        obtain ⟨n, h1, h2⟩ := reg_index (LS.calleeSaved_ok r (H.build.saved r hr)).1
        exact ⟨n, h1, by omega⟩)
  -- the restores write no operand location (a `Rets`'s operands are fixed outside the
  -- callee-saved registers) and no location of a vreg live across the instruction
  have hRSuse : ∀ (j : Nat) (o : Operand) (l : Loc), os[j]? = some o → io.allocs[j]? = some l →
      ∀ m ∈ RS, m.2 ≠ l := by
    intro j o l hj hl m hm he
    obtain ⟨⟨us, rfl⟩, r, hr, rfl⟩ := hRSm m hm
    subst he
    obtain ⟨q, hq, hqn⟩ := hrets us rfl o (mem_of_get hj)
    have := IF.fixed j o q hj hq
    rw [hl] at this
    simp only [Option.some.injEq, Loc.reg.injEq] at this
    subst this
    exact hqn (H.build.saved _ hr)
  have hRSthru : ∀ v, c.pl.covI v (pos g 0) (pos g 4) = true → ∀ m ∈ RS, m.2 ≠ c.loc v := by
    intro v hcov m hm he
    obtain ⟨⟨us, rfl⟩, r, hr, rfl⟩ := hRSm m hm
    have := hpf.retsClob g us hgi r (H.build.saved r hr) v (loc_reg he.symm)
    rw [cov_of_covI hcov (by unfold pos; omega) (by unfold pos; omega)] at this
    cases this
  -- after the moves in and the restores: the uses in their locations, the callee-saved
  -- registers' entry values, the vregs live across in their locations
  have h12 : Runs (ctxOf vc c rf) vb k (io.pre.map Spill.mv ++ RS.map Spill.mv) a
      fun k' a2 => k' = k ∧ a2.size = 128 + 2 * rf.spillSlots ∧
        (∀ (j : Nat) (o : Operand) (l : Loc), os[j]? = some o → o.kind = .use →
          io.allocs[j]? = some l →
          Sym.vreg o.vreg ∈ a2.get l) ∧
        (∀ r ∈ calleeSaved, (r ∈ rf.saved → Sym.entry r ∈ a2.get (.save r)) ∧
          (r ∉ rf.saved → Sym.entry r ∈ a2.get (.reg r)) ∧
          ((∃ us, i = .rets us) → Sym.entry r ∈ a2.get (.reg r))) ∧
        (∀ v < c.fn.nv, c.pl.covI v (pos g 0) (pos g 4) = true → A v = true →
          (∀ o ∈ os.toList, o.kind = .def → o.vreg ≠ v) → LocValid rf (c.loc v) →
          Sym.vreg v ∈ a2.get (c.loc v)) := by
    refine Runs.append hR1 fun k1 a1 ⟨e1, e2, e3, e4⟩ => ?_
    subst k1
    refine (hR2 a1 (by omega)).mono fun k2 a2 ⟨f1, f2, f3, f4⟩ => ⟨f1, by omega, ?_, ?_, ?_⟩
    · intro j o l hj hu hl
      rw [f4 l (hRSuse j o l hj hl)]
      have ho := mem_of_get hj
      have hv := hf.nv_ops g os hgo o ho
      have hcov : c.pl.cov o.vreg (pos g 0) = true :=
        cov_of_covI (hpf.use g os hgo o ho hu) (Nat.le_refl _) (by unfold pos; omega)
      have hAv : A o.vreg = true := by
        rw [hA]; exact H.avail.uses _ _ hf.cfg b vb k i os hvb hi hos o ho hu
      rcases IF.useIn j o hj hu with ⟨hl', hnp⟩ | ⟨l', hl', hm⟩
      · rw [hl] at hl'
        cases hl'
        rw [e4 _ hnp]
        obtain ⟨r, hr, ha, -⟩ := IF.allocs j o hj
        rw [hl] at hr
        refine hg.vregs o.vreg hv hcov hAv ?_
        rw [Option.some.inj hr]
        obtain ⟨n, h1, h2⟩ := reg_index ha
        exact ⟨n, h1, by omega⟩
      · rw [hl] at hl'
        cases hl'
        rw [show a1.get l = a.get (c.loc o.vreg) from e3 _ hm]
        exact hg.vregs o.vreg hv hcov hAv (locValid_of_cls (loc_cls hpf (hcls o ho))
          fun s c' he => hslot _ (hmPre _ hm) _ (by simp [RItem.locs, LinearScan.mv]) s c' he)
    · intro r hrc
      have hS : r ∈ rf.saved → Sym.entry r ∈ a2.get (.save r) := fun hs => by
        rw [f4 _ (fun m hm he => by obtain ⟨-, r', -, rfl⟩ := hRSm m hm; cases he),
          e4 _ (fun m hm he => by obtain ⟨r', hr'⟩ := hpreD m hm; rw [hr'] at he; cases he)]
        exact (hg.callee r hrc).1 hs
      have hN : r ∉ rf.saved → Sym.entry r ∈ a2.get (.reg r) := fun hns => by
        rw [f4 _ (fun m hm he => by
            obtain ⟨-, r', hr', rfl⟩ := hRSm m hm
            simp only [Loc.reg.injEq] at he
            subst he
            exact hns hr'),
          e4 _ (fun m hm he => hnots r hrc hns _ (hmPre m hm)
            (by rw [← he]; simp [RItem.locs, LinearScan.mv]))]
        exact (hg.callee r hrc).2 hns
      refine ⟨hS, hN, fun hR => ?_⟩
      by_cases hs : r ∈ rf.saved
      · rw [show a2.get (.reg r) = a1.get (.save r) from f3 _ (hRSall hR r hs),
          e4 _ (fun m hm he => by obtain ⟨r', hr'⟩ := hpreD m hm; rw [hr'] at he; cases he)]
        exact (hg.callee r hrc).1 hs
      · exact hN hs
    · intro v hv hcov hAv hnd hloc
      rw [f4 _ (hRSthru v hcov), e4 _ (IF.frame v hv hcov hnd).1]
      exact hg.vregs v hv (cov_of_covI hcov (Nat.le_refl _) (by unfold pos; omega)) hAv hloc
  -- the instruction
  have h123 : Runs (ctxOf vc c rf) vb k (io.pre.map Spill.mv ++ RS.map Spill.mv ++
      [.op k io.allocs]) a fun k' a3 => k' = k + 1 ∧ a3.size = 128 + 2 * rf.spillSlots ∧
        CalleeOk rf a3 ∧
        (∀ v < c.fn.nv, c.pl.covI v (pos g 0) (pos g 4) = true → A v = true →
          (∀ o ∈ os.toList, o.kind = .def → o.vreg ≠ v) → LocValid rf (c.loc v) →
          Sym.vreg v ∈ a3.get (c.loc v)) ∧
        (∀ (j : Nat) (o : Operand) (l : Loc), os[j]? = some o → o.kind = .def →
          j ∈ keptIdx i os → io.allocs[j]? = some l →
          a3.get l = [.vreg o.vreg]) := by
    refine Runs.append h12 fun k2 a2 ⟨f1, f2, hU, hC, hT⟩ => ?_
    subst k2
    have hst := IF.static (ctxOf vc c rf) s!"block {vb.label} inst {k}"
    obtain ⟨hDl, hnc⟩ := checkStatic_defs hst
    refine Runs.op hkn hi hos (stepOp_of hst ?_ ?_ ?_) ⟨rfl, ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨hxP, hxu, -⟩ := mem_atPos.mp hx
      obtain ⟨j, hj, hl⟩ := hPj x hxP
      exact hU j x.1 x.2 hj hxu hl
    · apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      obtain ⟨hxP, hxu, hxl⟩ := mem_atPos.mp hx
      have := hok.useEarly x.1 (hPo x hxP) hxu
      rw [hxl] at this
      cases this
    · by_cases hR : ∃ us, i = .rets us
      · obtain ⟨us, rfl⟩ := hR
        apply retCheck_rets
        intro r hr
        refine transferOp_entry ((hC r hr).2.2 ⟨us, rfl⟩) fun x hx _ he => ?_
        obtain ⟨j, hj, hl⟩ := hPj x hx
        obtain ⟨q, hq, hqn⟩ := hrets us rfl x.1 (hPo x hx)
        have := IF.fixed j x.1 q hj hq
        rw [hl, he] at this
        simp only [Option.some.injEq, Loc.reg.injEq] at this
        subst this
        exact hqn hr
      · exact retCheck_other (fun us h => hR ⟨us, h⟩) _
    · rw [size_transferOp]; exact f2
    · intro r hrc
      refine ⟨fun hs => transferOp_keep (fun x hx _ he => ?_) (fun r' _ he => by cases he)
        ((hC r hrc).1 hs) (fun _ _ _ he => by cases he),
        fun hns => transferOp_entry ((hC r hrc).2.1 hns) fun x hx _ he => ?_⟩
      · obtain ⟨r', hr', -⟩ := hPreg x hx
        rw [hr'] at he
        cases he
      · obtain ⟨j, -, hl⟩ := hPj x hx
        exact hnots r hrc hns _ hmOp (by rw [← he]; exact mem_of_get hl)
    · intro v hv hcov hAv hnd hloc
      have hfr := IF.frame v hv hcov hnd
      refine transferOp_keep (fun x hx hd => ?_) (fun r hr he => ?_) (hT v hv hcov hAv hnd hloc)
        (fun x hx hd he => ?_)
      · obtain ⟨j, hj, hl⟩ := hPj x hx
        exact hfr.2.1 j x.1 x.2 hj hd hl
      · have := hpf.clob g i hgi r hr v (loc_reg he.symm)
        rw [cov_of_covI hcov (by unfold pos; omega) (by unfold pos; omega)] at this
        cases this
      · injection he with he
        exact hnd x.1 (hPo x hx) hd he.symm
    · intro j o l hj hd hkept hl
      exact transferOp_kept' (by omega) hDl
        (by rw [defVregs_zip IF.size.symm]; exact hok.defsNodup)
        (fun x hx => by
          obtain ⟨r, hr, ha⟩ := hPreg x hx
          rw [hr]
          exact reg_index ha)
        hnc (keptIdx_pair IF.size.symm hkept hj hl)
  -- the moves out of the def registers (none after a terminator)
  have hpostT : io.post ≠ [] → k + 1 ≠ vb.insts.size := by
    intro hne hlast
    obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨j, o, -, -, hs, -, -⟩ := IF.post m hm
    obtain ⟨t, ht, htt⟩ := cfg_last hf.cfg hvb
    rw [Array.back?_eq_getElem?, show vb.insts.size - 1 = k by omega, hi] at ht
    cases ht
    simp [LinearScan.Ctx.store, htt] at hs
  have hpostV : ∀ m ∈ io.post, LocValid rf m.2 := by
    intro m hm
    obtain ⟨j, o, hj, -, -, -, hm2⟩ := IF.post m hm
    have hlc : LocCls m.2 o.cls := by rw [hm2]; exact loc_cls hpf (hcls o (mem_of_get hj))
    exact locValid_of_cls hlc fun s c' he =>
      hslot _ (hmPost m hm) _ (by simp [RItem.locs, LinearScan.mv]) s c' he
  refine Runs.append h123 fun k3 a3 ⟨g1, g2, gC, gT, gK⟩ => ?_
  subst k3
  refine (moves_runs' io.post a3 hpostT (fun m hm => ?_) IF.postSrc IF.postNodup
    (fun m hm => ?_)).mono fun k4 a4 ⟨h1, h2, h3, h4⟩ => ⟨h1, ?_⟩
  · obtain ⟨j, o, hj, -, -, hl, hm2⟩ := IF.post m hm
    have hlc : LocCls m.2 o.cls := by rw [hm2]; exact loc_cls hpf (hcls o (mem_of_get hj))
    obtain ⟨r, hr, ha, hrc⟩ := IF.allocs j o hj
    rw [hl] at hr
    have hm1 : m.1 = .reg r := Option.some.inj hr
    exact checkMove_ok (.inl ⟨r, hm1, ha, hrc⟩) hlc (fun s c' he => by rw [hm1] at he; cases he)
      (fun s c' he => hslot _ (hmPost m hm) _ (by simp [RItem.locs, LinearScan.mv]) s c' he)
      (.inl (by rw [hm1]; rfl))
  · obtain ⟨n, h1, h2⟩ := hpostV m hm
    exact ⟨n, h1, by omega⟩
  refine ⟨by omega, fun r hrc => ⟨fun hs => ?_, fun hns => ?_⟩, fun v hv hcov hAv hnd hloc => ?_,
    fun j o hj hd hs => ?_, fun ht j o q hj hd hkept hq => ?_⟩
  · rw [h4 _ fun m hm he => by
      obtain ⟨_, o, _, _, _, _, hm2⟩ := IF.post m hm
      exact loc_ne_save c o.vreg r (hm2 ▸ he)]
    exact (gC r hrc).1 hs
  · rw [h4 _ fun m hm he => hnots r hrc hns _ (hmPost m hm)
      (by rw [← he]; simp [RItem.locs, LinearScan.mv])]
    exact (gC r hrc).2 hns
  · rw [h4 _ (IF.frame v hv hcov hnd).2.2]
    exact gT v hv hcov hAv hnd hloc
  · have hkept : j ∈ keptIdx i os := by
      simp only [LinearScan.Ctx.store, Bool.and_eq_true, List.contains_iff_mem] at hs
      exact hs.1.2
    rcases IF.defOut j o hj hd hs with ⟨hl, hnp⟩ | ⟨l, hl, hm⟩
    · rw [h4 _ hnp, gK j o _ hj hd hkept hl]
      exact List.mem_singleton_self _
    · rw [show a4.get (c.loc o.vreg) = a3.get l from h3 _ hm, gK j o l hj hd hkept hl]
      exact List.mem_singleton_self _
  · rw [h4 _ fun m hm _ => by
      obtain ⟨_, _, _, _, hs, _⟩ := IF.post m hm
      simp [LinearScan.Ctx.store, ht] at hs, gK j o _ hj hd hkept (IF.fixed j o q hj hq)]
    exact List.mem_singleton_self _

end

end Backend.Proof.LS
