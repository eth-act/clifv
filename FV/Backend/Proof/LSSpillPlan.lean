import FV.Backend.Proof.LSFacts
import FV.Backend.Proof.LSMoves
import FV.Backend.Proof.LSTermFixed
import FV.Backend.Proof.LSSpillPlanStruct
import FV.Backend.Proof.SpillLocalCheck

/-!
# The Lean allocator always has a validated plan (V4b-4, #276)

`spillPlan_checked`: on a VCode with a CFG and the in-scope local facts (`SpillLocalOk`), the
plan that spills every vreg for its whole life (`Fn.spillPlan`) passes the validator
(`Ctx.structOk`, `spillPlan_structOk`) and builds: every instruction finds its scratch registers
(their number is bounded by `OpsOk.enough`, `spillPlan_inst_ok`), the branch-argument copies
sequentialise (`seqMoves_ok`), the results of a `try_call` reach its successors (each has it as
only predecessor).
`leanAlloc_planOk`: the Lean allocator's output is the built function of a plan that passes
`planOk`.
-/

namespace Backend.Proof.LS

open Backend Backend.LinearScan Backend.Proof Backend.Proof.Spill

/-! ## Generic `Except` helpers -/

private theorem bind_ok_of {α β : Type} {x : Except String α} {f : α → Except String β}
    (hx : ∃ a, x = .ok a) (hf : ∀ a, ∃ b, f a = .ok b) : ∃ b, (x >>= f) = .ok b := by
  obtain ⟨a, rfl⟩ := hx
  exact hf a

private theorem foldlM_ok_of {α β : Type} {f : β → α → Except String β} :
    ∀ (l : List α) (init : β), (∀ a ∈ l, ∀ acc, ∃ r, f acc a = .ok r) →
      ∃ r, l.foldlM f init = .ok r
  | [], init, _ => ⟨init, rfl⟩
  | a :: l, init, h => by
    obtain ⟨r, hr⟩ := h a List.mem_cons_self init
    simp only [List.foldlM_cons, hr, bind, Except.bind]
    exact foldlM_ok_of l r fun a ha => h a (List.mem_cons_of_mem _ ha)

private theorem mapM_ok_of {α β : Type} {f : α → Except String β} :
    ∀ (l : List α), (∀ a ∈ l, ∃ r, f a = .ok r) → ∃ r, l.mapM f = .ok r
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨r, hr⟩ := h a List.mem_cons_self
    obtain ⟨rs, hrs⟩ := mapM_ok_of l fun a ha => h a (List.mem_cons_of_mem _ ha)
    exact ⟨r :: rs, by simp [List.mapM_cons, hr, hrs, bind, Except.bind, pure, Except.pure]⟩

/-! ## `Fn.make` -/

/-- `Fn.make` succeeds on a VCode with a CFG and the in-scope local facts. -/
theorem make_ok {vc : VCode} (hcfg : ∃ succs preds, vc.cfg = .ok (succs, preds))
    (hloc : SpillLocalOk vc) : ∃ fn, Fn.make vc = .ok fn := by
  obtain ⟨succs, preds, hc⟩ := hcfg
  have hops : ∃ ops, (vc.blocks.toList.flatMap (·.insts.toList)).mapM MInst.operands = .ok ops := by
    refine mapM_ok_of _ fun i hi => ?_
    obtain ⟨vb, hvb, hi⟩ := List.mem_flatMap.mp hi
    obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hvb
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
    obtain ⟨os, hos, -⟩ := hloc.1 b vb k i (by simpa using hb) (by simpa using hk)
    exact ⟨os, hos⟩
  obtain ⟨ops, hops⟩ := hops
  have hall : (vc.blocks.all fun b => (b.params ++ b.branchArgs).all fun r => (vregOf r).isSome) =
      true := by
    rw [Array.all_eq_true_iff_forall_mem]
    intro vb hvb
    obtain ⟨b, hb⟩ := Array.mem_iff_getElem?.mp hvb
    rw [Array.all_eq_true_iff_forall_mem]
    intro r hr
    obtain ⟨n, c, rfl, -⟩ := hloc.2.1.2 b vb hb r (by simpa using hr)
    rfl
  unfold Fn.make
  simp only [hc, hops, hall, bind, Except.bind, Bool.not_true, Bool.false_eq_true, ite_false]
  exact ⟨_, rfl⟩

/-! ## The entry moves -/

section
variable {vc : VCode} {fn : Fn}

private theorem spillPlan_loc (fn : Fn) (v : Nat) :
    (LinearScan.Ctx.ofPlan fn fn.spillPlan).loc v = .stack (fn.spillPlan.home.getD v 0) (fn.clsOf v) := by
  simp [LinearScan.Ctx.loc, LinearScan.Ctx.ofPlan, Fn.loc, spillPlan_regOf]

private theorem keptDefs_branch {T : MInst} (h : T.isBranch = true) : T.keptDefs = some 0 := by
  unfold MInst.keptDefs
  split
  · simp [MInst.isBranch] at h
  · simp [MInst.isBranch] at h
  · simp [h]

private theorem targets_ret {T : MInst} (h : T.isRet = true) : T.targets = [] := by
  unfold MInst.isRet at h
  split at h
  · rfl
  · rfl
  · cases h

private theorem notTry {T : MInst} (h : ¬∃ info ti, T = .tryCall info ti) :
    T.isTerminator = (T.isBranch || T.isRet) := by
  unfold MInst.isTerminator
  split
  · exact absurd ⟨_, _, rfl⟩ h
  · simp

/-- A terminator result live on an edge is fixed, and the edge is its target's only one. -/
private theorem edgeDefs_fixed (hf : FnOk vc fn) (hE : Spill.EdgesOk vc fn.succs fn.preds) {b s : Nat}
    {o : Operand} (h : o ∈ edgeDefs vc fn.succs b s) :
    (∃ p, o.con = .fixed p) ∧ fn.preds[s]? = some #[b] := by
  unfold edgeDefs at h
  split at h
  · rename_i vb ss hvb hss
    split at h
    · rename_i j hj
      have hs : s ∈ ss.toList := List.isSome_idxOf?.mp (by rw [hj]; rfl)
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
      obtain ⟨T, ops, hT, hterm, hops, hkept, -⟩ := termEdgeDefs_spec hx
      have hkO : x.1 ∈ keptOps T ops.toList := by
        have := List.mem_map_of_mem (f := Prod.fst) hkept
        rwa [keptPairs_fst, Array.toList_zip, List.map_fst_zip (by simp [spillLocs_size])] at this
      obtain ⟨jj, hjj, hkj⟩ := keptOps_idx hkO
      refine ⟨term_kept_fixed hterm hops hjj hkj, ?_⟩
      by_cases htc : ∃ info ti, T = .tryCall info ti
      · obtain ⟨info, ti, rfl⟩ := htc
        exact (hE.tryEdge b vb info ti ss s hvb hT).2 hss hs
      · exfalso
        have hnt := notTry htc
        cases hbr : T.isBranch
        · cases hret : T.isRet
          · rw [hnt, hbr, hret] at hterm; cases hterm
          · obtain ⟨T', ts, hT', -, hts, hsz, -⟩ := (Prep.cfg_spec hf.cfg).blk b vb hvb
            rw [hT] at hT'
            cases hT'
            rw [hss] at hts
            cases hts
            rw [targets_ret hret] at hsz
            have : ss.toList = [] := by simpa using hsz
            rw [this] at hs
            exact absurd hs List.not_mem_nil
        · simp [keptOps, keptDefs_branch hbr] at hkO
    · exact absurd h List.not_mem_nil
  · exact absurd h List.not_mem_nil

private theorem termMoves_ok (hf : FnOk vc fn) (hE : Spill.EdgesOk vc fn.succs fn.preds) (s g0 b : Nat) :
    ∃ l, (LinearScan.Ctx.ofPlan fn fn.spillPlan).termMoves s g0 b = .ok l := by
  unfold LinearScan.Ctx.termMoves
  refine bind_ok_of (foldlM_ok_of _ _ fun o ho acc => ?_) fun _ => ⟨_, rfl⟩
  have ho' : o ∈ edgeDefs vc fn.succs b s := by
    rw [← hf.vc_eq]; exact ho
  obtain ⟨⟨p, hp⟩, hpr⟩ := edgeDefs_fixed hf hE ho'
  have hsz : (fn.preds.getD s #[]).size = 1 := by
    rw [Array.getD_eq_getD_getElem?, hpr]; rfl
  simp only [LinearScan.Ctx.ofPlan] at hsz ⊢
  by_cases hc : fn.spillPlan.cov o.vreg (pos g0 0) = true
  · have hl := spillPlan_loc fn o.vreg
    simp only [LinearScan.Ctx.ofPlan] at hl
    simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false, hp, hl, hsz]
    exact ⟨_, rfl⟩
  · simp only [Bool.not_eq_true] at hc
    simp only [hc, Bool.not_false, ite_true]
    exact ⟨_, rfl⟩

private theorem entryMoves_ok (hf : FnOk vc fn) (hE : Spill.EdgesOk vc fn.succs fn.preds) (s : Nat) :
    ∃ l, (LinearScan.Ctx.ofPlan fn fn.spillPlan).entryMoves s = .ok l := by
  unfold LinearScan.Ctx.entryMoves
  exact bind_ok_of (mapM_ok_of _ fun b _ => termMoves_ok hf hE _ _ b) fun _ => ⟨_, rfl⟩

end

/-! ## The argument copies -/

section
variable {vc : VCode} {fn : Fn}

private theorem mem_zip_idx {A P : List Nat} {a p : Nat} (h : (a, p) ∈ A.zip P) :
    ∃ k : Nat, A[k]? = some a ∧ P[k]? = some p := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp h
  exact ⟨k, (List.getElem?_zip_eq_some.mp hk)⟩

/-- The parallel copy of a block's arguments, once its pairs are known (`P`: argument and
parameter vregs, of one class each, distinct parameters). -/
private theorem argSeq_ok {P : List (Nat × Nat)}
    (hP : ∀ a p, (a, p) ∈ P → a < fn.nv ∧ p < fn.nv ∧ fn.clsOf a = fn.clsOf p)
    (huniq : ∀ a a' p, (a, p) ∈ P → (a', p) ∈ P → a = a') {ms : List (Loc × Loc)}
    (hms : ∀ m ∈ ms, ∃ a p, (a, p) ∈ P ∧
      m = ((LinearScan.Ctx.ofPlan fn fn.spillPlan).loc a, (LinearScan.Ctx.ofPlan fn fn.spillPlan).loc p))
    {avoid : List Reg} (havoid : avoid = []) (g : Nat) :
    ∃ its, seqMoves ms
      (fun cl => scratchReg (LinearScan.Ctx.ofPlan fn fn.spillPlan).occ [] cl (pos g 0) (pos g 1) avoid)
      (fun cl => match scratchReg (LinearScan.Ctx.ofPlan fn fn.spillPlan).occ [] cl (pos g 0) (pos g 1)
          ((scratchReg (LinearScan.Ctx.ofPlan fn fn.spillPlan).occ [] cl (pos g 0) (pos g 1) avoid).toList ++
            avoid) with
        | some r => .reg r
        | none => .stack (LinearScan.Ctx.ofPlan fn fn.spillPlan).pl.nslots cl) = .ok its := by
  subst havoid
  have hocc : ∀ i, (LinearScan.Ctx.ofPlan fn fn.spillPlan).occ.getD i #[] = #[] :=
    spillPlan_occ fn
  have hscr : ∀ cl, ∃ r, scratchReg (LinearScan.Ctx.ofPlan fn fn.spillPlan).occ [] cl (pos g 0)
      (pos g 1) [] = some r := fun cl => by
    have : ∃ r ∈ scratchOrder cl, ∀ y ∈ ([] : List (Reg × Nat × Nat)), y.1 ≠ r := by
      cases cl
      · exact ⟨.x 9, by decide, fun _ h => absurd h List.not_mem_nil⟩
      · exact ⟨.v 16, by decide, fun _ h => absurd h List.not_mem_nil⟩
    obtain ⟨r, hr, -⟩ := spillPlan_scratch_some hocc this (pos g 0) (pos g 1)
    exact ⟨r, hr⟩
  have hloc : ∀ v, (LinearScan.Ctx.ofPlan fn fn.spillPlan).loc v =
      .stack (fn.spillPlan.home.getD v 0) (fn.clsOf v) := spillPlan_loc fn
  refine seqMoves_ok ?_ ?_ ?_ ?_ ?_ ?_
  · intro m hm m' hm' he
    obtain ⟨a, p, hap, rfl⟩ := hms m hm
    obtain ⟨a', p', hap', rfl⟩ := hms m' hm'
    simp only [hloc, Loc.stack.injEq] at he ⊢
    rw [spillPlan_home (hP a p hap).2.1, spillPlan_home (hP a' p' hap').2.1] at he
    obtain ⟨rfl, -⟩ := he
    rw [huniq a a' p hap hap']
    exact ⟨rfl, rfl⟩
  · intro m _ _ _
    obtain ⟨r, hr⟩ := hscr (locCls m.1)
    rw [hr]; rfl
  · intro cl _
    obtain ⟨r, hr⟩ := hscr cl
    rw [hr]; rfl
  · intro cl
    split
    · rename_i r hr
      obtain ⟨-, hc, -⟩ := scratchOrder_ok (List.mem_of_find?_eq_some hr)
      simp [locCls, Loc.cls?, hc]
    · rfl
  · intro cl m hm
    obtain ⟨a, p, hap, rfl⟩ := hms m hm
    have hnv : fn.spillPlan.nslots = fn.nv := rfl
    simp only [hloc, spillPlan_home (hP a p hap).1, spillPlan_home (hP a p hap).2.1]
    split
    · exact ⟨by simp, by simp⟩
    · simp only [LinearScan.Ctx.ofPlan, hnv, ne_eq, Loc.stack.injEq, not_and]
      exact ⟨fun h => absurd h (Nat.ne_of_lt (hP a p hap).1),
        fun h => absurd h (Nat.ne_of_lt (hP a p hap).2.1)⟩
  · intro m hm
    obtain ⟨a, p, hap, rfl⟩ := hms m hm
    simp [hloc, locCls, Loc.cls?, (hP a p hap).2.2]

private theorem nodup_zip_uniq {A P : List Nat} (hnd : P.Nodup) {a a' p : Nat}
    (h : (a, p) ∈ A.zip P) (h' : (a', p) ∈ A.zip P) : a = a' := by
  obtain ⟨k, hk, hpk⟩ := mem_zip_idx h
  obtain ⟨k', hk', hpk'⟩ := mem_zip_idx h'
  have hkl : k < P.length := (List.getElem?_eq_some_iff.mp hpk).1
  have hkl' : k' < P.length := (List.getElem?_eq_some_iff.mp hpk').1
  have : k = k' := by
    rw [List.getElem?_eq_getElem hkl] at hpk
    rw [List.getElem?_eq_getElem hkl'] at hpk'
    exact (hnd.getElem_inj (hi := hkl) (hj := hkl')).mp
      ((Option.some.inj hpk).trans (Option.some.inj hpk').symm)
  subst this
  rw [hk] at hk'
  exact Option.some.inj hk'

private theorem argMoves_ok (hf : FnOk vc fn) (hloc : SpillLocalOk vc) {b : Nat}
    (hb : b < vc.blocks.size) (g : Nat) :
    ∃ its, (LinearScan.Ctx.ofPlan fn fn.spillPlan).argMoves b g = .ok its := by
  have hE := hloc.2.2 _ _ hf.cfg
  have hvb : vc.blocks[b]? = some vc.blocks[b] := Array.getElem?_eq_getElem hb
  unfold LinearScan.Ctx.argMoves
  by_cases hba : vc.blocks[b].branchArgs = #[]
  · have hargs : fn.args b = [] := by rw [hf.args hvb, hba]; rfl
    simp only [LinearScan.Ctx.ofPlan, hargs]
    split
    · exact ⟨[], by simp [seqMoves, cleanMoves, seqGo, pure, Except.pure]⟩
    · exact ⟨[], rfl⟩
  · obtain ⟨-, t, tb, hss, htb, hsz, hcl, hnd⟩ := hE.args b _ hvb hba
    have hsucc : (fn.succs.getD b #[]).toList = [t] := by
      rw [Array.getD_eq_getD_getElem?, hss]; rfl
    simp only [LinearScan.Ctx.ofPlan, hsucc]
    have hvr : ∀ blk : VBlock, (vc.blocks[b]? = some blk ∨ vc.blocks[t]? = some blk) →
        ∀ r ∈ blk.params.toList ++ blk.branchArgs.toList, ∃ n c, r = .vreg n c := by
      rintro blk (h | h) r hr <;>
      · obtain ⟨n, c, he, -⟩ := hf.nv_regs _ blk h r hr
        exact ⟨n, c, he⟩
    have hargs : fn.args b = vc.blocks[b].branchArgs.toList.map Reg.homeNum := by
      rw [hf.args hvb]
      exact spillPlan_filterMap_vreg fun r hr => hvr _ (.inl hvb) r (List.mem_append_right _ hr)
    have hpar : fn.params t = tb.params.toList.map Reg.homeNum := by
      rw [hf.params htb]
      exact spillPlan_filterMap_vreg fun r hr => hvr _ (.inr htb) r (List.mem_append_left _ hr)
    have hP : ∀ a p, (a, p) ∈ (fn.args b).zip (fn.params t) →
        a < fn.nv ∧ p < fn.nv ∧ fn.clsOf a = fn.clsOf p := by
      intro a p hap
      have ha := (List.of_mem_zip hap).1
      have hp := (List.of_mem_zip hap).2
      refine ⟨spillPlan_mem_args hf (.inl ha), spillPlan_mem_args hf (.inr hp), ?_⟩
      obtain ⟨k, hk, hpk⟩ := mem_zip_idx hap
      rw [hargs, List.getElem?_map] at hk
      rw [hpar, List.getElem?_map] at hpk
      cases hra : vc.blocks[b].branchArgs.toList[k]? with
      | none => rw [hra] at hk; cases hk
      | some ra =>
        cases hrp : tb.params.toList[k]? with
        | none => rw [hrp] at hpk; cases hpk
        | some rp =>
          rw [hra] at hk
          rw [hrp] at hpk
          obtain ⟨x, y, cc, rfl, rfl⟩ := hcl k ra rp (by simpa using hra) (by simpa using hrp)
          simp only [Option.map_some, Option.some.injEq, Reg.homeNum] at hk hpk
          obtain ⟨n, c', he, hn⟩ := hloc.2.1.2 b _ hvb (.vreg x cc)
            (List.mem_append_right _ (List.mem_of_getElem? hra))
          cases he
          obtain ⟨n', c'', he', hn'⟩ := hloc.2.1.2 t tb htb (.vreg y cc)
            (List.mem_append_left _ (List.mem_of_getElem? hrp))
          cases he'
          rw [← hk, ← hpk, hf.cls x cc hn, hf.cls y cc hn']
    have huniq : ∀ a a' p, (a, p) ∈ (fn.args b).zip (fn.params t) →
        (a', p) ∈ (fn.args b).zip (fn.params t) → a = a' := fun a a' p h h' =>
      nodup_zip_uniq (by rw [hpar]; exact hnd) h h'
    refine argSeq_ok hP huniq ?_ ?_ g
    · intro m hm
      obtain ⟨⟨a, p⟩, hap, hm⟩ := List.mem_filterMap.mp hm
      by_cases hc : fn.spillPlan.cov p (pos (fn.start.getD t 0) 0) = true
      · simp only [hc, ite_true, Option.some.injEq] at hm
        subst hm
        exact ⟨a, p, hap, rfl⟩
      · simp only [hc, Bool.false_eq_true, ite_false, reduceCtorEq] at hm
    · refine List.flatMap_eq_nil_iff.mpr fun m hm => ?_
      obtain ⟨⟨a, p⟩, hap, hm⟩ := List.mem_filterMap.mp hm
      by_cases hc : fn.spillPlan.cov p (pos (fn.start.getD t 0) 0) = true
      · simp only [hc, ite_true, Option.some.injEq] at hm
        subst hm
        have := spillPlan_loc fn
        simp only [LinearScan.Ctx.ofPlan] at this
        simp [this, locReg?]
      · simp only [hc, Bool.false_eq_true, ite_false, reduceCtorEq] at hm

end

/-! ## The build -/

section
variable {vc : VCode} {fn : Fn} (hf : FnOk vc fn) (hloc : SpillLocalOk vc)
include hf hloc

private theorem blockParts_ok {b : Nat} (hb : b < vc.blocks.size) :
    ∃ p, (LinearScan.Ctx.ofPlan fn fn.spillPlan).blockParts b = .ok p := by
  have hE := hloc.2.2 _ _ hf.cfg
  have hbb := spillPlan_blockBounds hf hb
  unfold LinearScan.Ctx.blockParts
  refine bind_ok_of (entryMoves_ok hf hE b) fun _ => ?_
  refine bind_ok_of (mapM_ok_of _ fun k hk => ?_) fun _ => ⟨_, rfl⟩
  have hk' : k < _ := List.mem_range.mp hk
  have hg : fn.start.getD b 0 + k < fn.insts.size := by
    simp only [LinearScan.Ctx.ofPlan] at hk'; omega
  have hio : ∃ io, (LinearScan.Ctx.ofPlan fn fn.spillPlan).inst (fn.start.getD b 0 + k) = .ok io :=
    spillPlan_inst_ok (fun v => spillPlan_regOf fn v) (spillPlan_occ fn) (spillPlan_opsOk hf hloc hg).1
  dsimp only
  split
  · exact bind_ok_of (argMoves_ok hf hloc hb _) fun _ => bind_ok_of hio fun _ => ⟨_, rfl⟩
  · exact bind_ok_of ⟨_, rfl⟩ fun _ => bind_ok_of hio fun _ => ⟨_, rfl⟩

private theorem build_ok : ∃ rf, (LinearScan.Ctx.ofPlan fn fn.spillPlan).build = .ok rf := by
  unfold LinearScan.Ctx.build
  refine bind_ok_of (mapM_ok_of _ fun b hb => ?_) fun _ => ⟨_, rfl⟩
  have hb' := List.mem_range.mp hb
  simp only [LinearScan.Ctx.ofPlan, hf.nblocks] at hb'
  exact blockParts_ok hf hloc hb'

end

/-! ## The theorems -/

/-- **The all-spill plan passes the validator and builds.** -/
theorem spillPlan_checked {vc : VCode} {fn : Fn} (hmk : Fn.make vc = .ok fn)
    (hloc : SpillLocalOk vc) : (LinearScan.Ctx.ofPlan fn fn.spillPlan).checked.isSome = true := by
  have hf := fnOk_of_make hmk
  obtain ⟨rf, hrf⟩ := build_ok hf hloc
  simp [LinearScan.Ctx.checked, spillPlan_structOk hf hloc, hrf, Except.toOption]

theorem planOk_spillPlan {vc : VCode} {fn : Fn} (hmk : Fn.make vc = .ok fn)
    (hloc : SpillLocalOk vc) : planOk vc fn.spillPlan = true := by
  simp only [planOk, hmk]
  exact spillPlan_checked hmk hloc

/-- A plan whose context is `checked` passes `planOk` and builds to the checked function. -/
private theorem of_checked {vc : VCode} {fn : Fn} (hmk : Fn.make vc = .ok fn) {pl : LinearScan.Plan}
    {rf : RFunc} (h : (LinearScan.Ctx.ofPlan fn pl).checked = some rf) :
    planOk vc pl = true ∧ buildPlan vc pl = .ok rf := by
  refine ⟨by simp [planOk, hmk, h], ?_⟩
  simp only [buildPlan, hmk, bind, Except.bind]
  unfold LinearScan.Ctx.checked at h
  split at h
  · cases hb : (LinearScan.Ctx.ofPlan fn pl).build with
    | error e => rw [hb] at h; cases h
    | ok rf' => rw [hb] at h; cases h; rfl
  · cases h

/-- **The Lean allocator's output is the build of a validated plan.** -/
theorem leanAlloc_planOk {vc : VCode} (hcfg : ∃ succs preds, vc.cfg = .ok (succs, preds))
    (hloc : SpillLocalOk vc) :
    ∃ pl rf, planOk vc pl = true ∧ buildPlan vc pl = .ok rf ∧ leanAlloc vc = .ok rf := by
  obtain ⟨fn, hmk⟩ := make_ok hcfg hloc
  have hspill := spillPlan_checked hmk hloc
  have key : ∀ pl rf, (LinearScan.Ctx.ofPlan fn pl).checked = some rf → fn.alloc = some rf →
      ∃ pl rf, planOk vc pl = true ∧ buildPlan vc pl = .ok rf ∧ leanAlloc vc = .ok rf :=
    fun pl rf h ha => ⟨pl, rf, (of_checked hmk h).1, (of_checked hmk h).2, by
      simp [leanAlloc, hmk, bind, Except.bind, ha, pure, Except.pure]⟩
  unfold Fn.alloc at *
  cases h0 : (LinearScan.Ctx.ofPlan fn (fn.plan (reserved 0))).checked with
  | some rf => exact key _ rf h0 (by simp [h0])
  | none =>
    cases h2 : (LinearScan.Ctx.ofPlan fn (fn.plan (reserved 2))).checked with
    | some rf => exact key _ rf h2 (by simp [h0, h2])
    | none =>
      cases h4 : (LinearScan.Ctx.ofPlan fn (fn.plan (reserved 4))).checked with
      | some rf => exact key _ rf h4 (by simp [h0, h2, h4])
      | none =>
        obtain ⟨rf, hs⟩ := Option.isSome_iff_exists.mp hspill
        exact key _ rf hs (by simp [h0, h2, h4, hs])

end Backend.Proof.LS
