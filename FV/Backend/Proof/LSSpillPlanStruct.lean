import FV.Backend.Proof.LSSpillPlanInst
import FV.Backend.Proof.LSRun
import FV.Backend.Proof.SpillEdgesPrep
import FV.Backend.Proof.SpillStep4Cfg

/-!
# The all-spill plan passes the validator (V4b-4, #276)

`spillPlan_structOk`: every vreg below `nv` has one segment `[0, pos insts.size 0]`, no
register and its own home. The segment starts at the entry block's first instruction; every
edge into a block delivers its vregs (a parameter's predecessor has branch arguments, so it
ends in a `jump` to the block alone, `EdgesOk.args`); all uses and defs are covered; `occ` is
empty, so the register conditions hold trivially; each home holds one vreg's segment.
-/

namespace Backend.Proof.LS

open Backend Backend.LinearScan Backend.Proof Backend.Proof.Spill

/-! ## The plan's segments and homes -/

private theorem segs_getD (fn : Fn) (v : Nat) :
    fn.spillPlan.segs.getD v #[] = if v < fn.nv then #[(0, pos fn.insts.size 0)] else #[] := by
  simp only [Fn.spillPlan, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

private theorem spillPlan_cov {fn : Fn} {v p : Nat} :
    fn.spillPlan.cov v p = true ↔ v < fn.nv ∧ p ≤ pos fn.insts.size 0 := by
  rw [cov_iff, segs_getD]
  by_cases hv : v < fn.nv
  · rw [ite_eq_left hv]
    constructor
    · rintro ⟨s, e, hm, -, hp⟩
      simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact ⟨hv, hp⟩
    · rintro ⟨-, hp⟩
      exact ⟨0, _, by simp, Nat.zero_le _, hp⟩
  · rw [ite_eq_right hv]
    simp only [List.not_mem_nil, false_and, exists_false, false_iff]
    exact fun h => hv h.1

private theorem spillPlan_covI {fn : Fn} {v p q : Nat} :
    fn.spillPlan.covI v p q = true ↔ v < fn.nv ∧ q ≤ pos fn.insts.size 0 := by
  rw [covI_iff, segs_getD]
  by_cases hv : v < fn.nv
  · rw [ite_eq_left hv]
    constructor
    · rintro ⟨s, e, hm, -, hp⟩
      simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact ⟨hv, hp⟩
    · rintro ⟨-, hp⟩
      exact ⟨0, _, by simp, Nat.zero_le _, hp⟩
  · rw [ite_eq_right hv]
    simp only [List.not_mem_nil, false_and, exists_false, false_iff]
    exact fun h => hv h.1

theorem spillPlan_home {fn : Fn} {v : Nat} (hv : v < fn.nv) : fn.spillPlan.home.getD v 0 = v := by
  simp [Fn.spillPlan, Array.getD_eq_getD_getElem?, hv]

private theorem spillPlan_occ_eq (fn : Fn) : fn.spillPlan.occ = Array.replicate 64 #[] := by
  apply Array.ext
  · simp [occ_size]
  · intro i h1 h2
    have := spillPlan_occ fn i
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1] at this
    simpa using this

/-! ## Function facts -/

section
variable {vc : VCode} {fn : Fn}

/-- Every block ends in a terminator, so it is nonempty. -/
theorem spillPlan_blockBounds (hf : FnOk vc fn) {b : Nat} (hb : b < vc.blocks.size) :
    fn.start.getD b 0 < fn.start.getD (b + 1) 0 ∧ fn.start.getD (b + 1) 0 ≤ fn.insts.size := by
  have hvb : vc.blocks[b]? = some vc.blocks[b] := Array.getElem?_eq_getElem hb
  obtain ⟨t, ht, -⟩ := cfg_last hf.cfg hvb
  have hne : 0 < vc.blocks[b].insts.size := by
    rcases h : vc.blocks[b].insts.size with _ | n
    · rw [Array.back?, h] at ht
      have := (Array.getElem?_eq_some_iff.mp ht).1
      omega
    · omega
  rw [hf.startSucc hvb]
  refine ⟨by omega, ?_⟩
  rw [← hf.startSucc hvb, hf.total]
  exact hf.start_mono (by omega) (by omega)

/-- The operand facts of a global instruction. -/
theorem spillPlan_opsOk (hf : FnOk vc fn) (hloc : SpillLocalOk vc) {g : Nat} (hg : g < fn.insts.size) :
    OpsOk (fn.ops.getD g #[]) (fn.insts.getD g default).clobbers ∧
      ∃ i os, fn.insts[g]? = some i ∧ fn.ops[g]? = some os ∧ i.operands = .ok os ∧
        ∃ b vb k, vc.blocks[b]? = some vb ∧ vb.insts[k]? = some i ∧ g = fn.start.getD b 0 + k := by
  obtain ⟨b, vb, k, hvb, hk, rfl, -⟩ := hf.decode hg
  have hi : vb.insts[k]? = some vb.insts[k] := Array.getElem?_eq_getElem hk
  obtain ⟨os, hos, hok, -⟩ := hloc.1 b vb k _ hvb hi
  obtain ⟨hops, hgetD, hinst⟩ := hf.opsGetD hvb hi hos
  refine ⟨?_, _, os, hinst, hops, hos, b, vb, k, hvb, hi, rfl⟩
  rw [hgetD, Array.getD_eq_getD_getElem?, hinst]
  exact hok

/-- A predecessor of `t` has `t` among its successors. -/
private theorem pred_succ (hf : FnOk vc fn) {t b : Nat} (ht : t < vc.blocks.size)
    (hb : b ∈ (fn.preds.getD t #[]).toList) :
    b < vc.blocks.size ∧ ∃ ss, fn.succs[b]? = some ss ∧ t ∈ ss.toList := by
  rw [Array.getD_eq_getD_getElem?, cfg_preds hf.cfg ht, Option.getD_some, List.toList_toArray] at hb
  simp only [predsOf, List.mem_flatMap, List.mem_replicate] at hb
  obtain ⟨⟨ss, b'⟩, hq, hc, rfl⟩ := hb
  have hss : fn.succs[b]? = some ss := by
    rw [← Array.getElem?_toList]; exact List.mem_zipIdx_iff_getElem?.mp hq
  refine ⟨?_, ss, hss, List.count_pos_iff.mp (Nat.pos_of_ne_zero hc)⟩
  rw [← (Prep.cfg_spec hf.cfg).size]
  exact (Array.getElem?_eq_some_iff.mp hss).1

private theorem vreg_of {r : Reg} {n : Nat} (h : vregOf r = some n) : ∃ c, r = .vreg n c := by
  cases r <;> simp [vregOf] at h
  subst h
  exact ⟨_, rfl⟩

/-- Parameters and branch arguments are vregs below `nv`. -/
theorem spillPlan_mem_args (hf : FnOk vc fn) {b : Nat} {a : Nat} (ha : a ∈ fn.args b ∨ a ∈ fn.params b) :
    a < fn.nv := by
  rcases h : vc.blocks[b]? with _ | vb
  · rcases ha with ha | ha
    · simp [Fn.args, hf.vc_eq, h] at ha
    · simp [Fn.params, hf.vc_eq, h] at ha
  · rw [hf.args h, hf.params h] at ha
    obtain ⟨r, hr, hv⟩ : ∃ r, r ∈ vb.params.toList ++ vb.branchArgs.toList ∧ vregOf r = some a := by
      rcases ha with ha | ha
      · obtain ⟨r, hr, hv⟩ := List.mem_filterMap.mp ha
        exact ⟨r, List.mem_append_right _ hr, hv⟩
      · obtain ⟨r, hr, hv⟩ := List.mem_filterMap.mp ha
        exact ⟨r, List.mem_append_left _ hr, hv⟩
    obtain ⟨c, rfl⟩ := vreg_of hv
    obtain ⟨n, c', he, hn⟩ := hf.nv_regs b vb h _ hr
    cases he
    exact hn

theorem spillPlan_filterMap_vreg {L : List Reg} (h : ∀ r ∈ L, ∃ n c, r = .vreg n c) :
    L.filterMap vregOf = L.map Reg.homeNum := by
  induction L with
  | nil => rfl
  | cons r L ih =>
    obtain ⟨n, c, rfl⟩ := h r List.mem_cons_self
    simp [vregOf, Reg.homeNum, ih fun r hr => h r (List.mem_cons_of_mem _ hr)]

end

/-! ## The conditions -/

section
variable {fn : Fn}

private theorem lt_of_mem_blocksUpTo (fn : Fn) (e b t : Nat) (h : t ∈ fn.blocksUpTo e b) :
    t < fn.nblocks := by
  rw [Fn.blocksUpTo] at h
  split at h
  · split at h
    · rcases List.mem_cons.mp h with rfl | h
      · assumption
      · exact lt_of_mem_blocksUpTo fn e (b + 1) t h
    · cases h
  · cases h
termination_by fn.nblocks - b

private theorem regsOk_spill : (LinearScan.Ctx.ofPlan fn fn.spillPlan).regsOk = true := by
  simp only [LinearScan.Ctx.regsOk, LinearScan.Ctx.ofPlan, spillPlan_regOf]
  simp [Fn.spillPlan]

private theorem occOk_spill :
    (LinearScan.Ctx.ofPlan fn fn.spillPlan).occ.all disjointSorted = true := by
  simp only [LinearScan.Ctx.ofPlan, spillPlan_occ_eq, Array.all_eq_true_iff_forall_mem,
    Array.mem_replicate]
  rintro _ ⟨-, rfl⟩
  rfl

private theorem allocatable_idx : ∀ r ∈ aarch64Env.allocatable, (regIdx r).isSome = true := by
  decide

private theorem meetsOther_nil (s e u : Nat) : meetsOther #[] s e u = false := by
  simp [meetsOther, meetsOtherFrom]

private theorem defUseOk_spill : (LinearScan.Ctx.ofPlan fn fn.spillPlan).defUseOk = true := by
  simp [LinearScan.Ctx.defUseOk, LinearScan.Ctx.ofPlan, spillPlan_regOf]

end


section
variable {vc : VCode} {fn : Fn} (hf : FnOk vc fn) (hloc : SpillLocalOk vc)
include hf hloc

private theorem insts_pos : 0 < fn.insts.size := by
  have hE := hloc.2.2 _ _ hf.cfg
  have h0 : 0 < vc.blocks.size := Nat.pos_of_ne_zero hE.entry.1
  have := spillPlan_blockBounds hf h0
  omega

private theorem edgeOk_spill {v t b : Nat} (hv : v < fn.nv) (ht : t < vc.blocks.size)
    (hb : b ∈ (fn.preds.getD t #[]).toList) :
    (LinearScan.Ctx.ofPlan fn fn.spillPlan).edgeOk v t b = true := by
  have hE := hloc.2.2 _ _ hf.cfg
  obtain ⟨hbl, ss, hss, hts⟩ := pred_succ hf ht hb
  have hvb : vc.blocks[b]? = some vc.blocks[b] := Array.getElem?_eq_getElem hbl
  have htb : vc.blocks[t]? = some vc.blocks[t] := Array.getElem?_eq_getElem ht
  have hbb := spillPlan_blockBounds hf hbl
  have hgl : LinearScan.Ctx.lastOf (LinearScan.Ctx.ofPlan fn fn.spillPlan) b < fn.insts.size := by
    simp only [LinearScan.Ctx.lastOf, LinearScan.Ctx.ofPlan]; omega
  unfold LinearScan.Ctx.edgeOk
  generalize LinearScan.Ctx.lastOf (LinearScan.Ctx.ofPlan fn fn.spillPlan) b = gl at hgl
  simp only [LinearScan.Ctx.ofPlan]
  cases hk : (fn.params t).idxOf? v with
  | none =>
    exact spillPlan_cov.mpr ⟨hv, by simp only [pos]; omega⟩
  | some k =>
    obtain ⟨hkl, hkv, -⟩ := List.idxOf?_eq_some_iff.mp hk
    have hne : vc.blocks[b].branchArgs ≠ #[] := by
      intro h
      have := hE.noArgs b _ ss t _ hvb h hss hts htb
      rw [hf.params htb, this] at hkl
      simp at hkl
    obtain ⟨-, t', tb, hss', htb', hsz, -, -⟩ := hE.args b _ hvb hne
    rw [hss] at hss'
    cases hss'
    have htt : t = t' := by simpa using hts
    subst htt
    rw [htb] at htb'
    cases htb'
    have hsucc : (fn.succs.getD b #[]).toList = [t] := by
      rw [Array.getD_eq_getD_getElem?, hss]; rfl
    have hvr : ∀ blk : VBlock, vc.blocks[b]? = some blk ∨ vc.blocks[t]? = some blk →
        ∀ r ∈ blk.params.toList ++ blk.branchArgs.toList, ∃ n c, r = .vreg n c := by
      rintro blk (h | h) r hr <;>
      · obtain ⟨n, c, he, -⟩ := hf.nv_regs _ blk h r hr
        exact ⟨n, c, he⟩
    have hargs : fn.args b = vc.blocks[b].branchArgs.toList.map Reg.homeNum := by
      rw [hf.args hvb]
      exact spillPlan_filterMap_vreg fun r hr => hvr _ (.inl hvb) r (List.mem_append_right _ hr)
    have hpar : fn.params t = vc.blocks[t].params.toList.map Reg.homeNum := by
      rw [hf.params htb]
      exact spillPlan_filterMap_vreg fun r hr => hvr _ (.inr htb) r (List.mem_append_left _ hr)
    have hka : k < (fn.args b).length := by
      rw [hargs, List.length_map, Array.length_toList, ← hsz]
      rw [hpar, List.length_map, Array.length_toList] at hkl
      exact hkl
    dsimp only
    rw [hsucc, List.getElem?_eq_getElem hka]
    simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true]
    exact ⟨spillPlan_cov.mpr ⟨spillPlan_mem_args hf (.inl (List.getElem_mem hka)),
      by simp only [pos]; omega⟩, spillPlan_covI.mpr ⟨hv, by simp only [pos]; omega⟩⟩

private theorem segsOk_spill : (LinearScan.Ctx.ofPlan fn fn.spillPlan).segsOk = true := by
  simp only [LinearScan.Ctx.segsOk, LinearScan.Ctx.ofPlan, List.all_eq_true, List.mem_range]
  intro v hv
  rw [segs_getD, ite_eq_left hv]
  simp only [Array.all_eq_true_iff_forall_mem, Array.mem_singleton]
  rintro _ rfl
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Array.all_eq_true_iff_forall_mem]
  refine ⟨⟨Nat.zero_le _, ?_⟩, fun t ht b hb => ?_⟩
  · have hpos := insts_pos hf hloc
    obtain ⟨b, vb, k, hvb, hk, h0, hblk⟩ := hf.decode hpos
    have hs0 : fn.start.getD b 0 = 0 := by omega
    have hblk' : fn.blk.getD 0 0 = b := by rw [Array.getD_eq_getD_getElem?, hblk]; rfl
    simp [LinearScan.Ctx.birthOk, Fn.isStart, hpos, hblk', hs0]
  · have ht' : t < vc.blocks.size := by
      rw [← hf.nblocks]; exact lt_of_mem_blocksUpTo fn _ _ t ht
    exact edgeOk_spill hf hloc hv ht' (Array.mem_toList_iff.mpr hb)

omit hloc in
private theorem usesOk_spill : (LinearScan.Ctx.ofPlan fn fn.spillPlan).usesOk = true := by
  simp only [LinearScan.Ctx.usesOk, LinearScan.Ctx.ofPlan, List.all_eq_true, List.mem_range,
    Array.all_eq_true_iff_forall_mem]
  intro g hg o ho
  have hg' : g < fn.insts.size := hf.ops_size ▸ hg
  have hos : fn.ops[g]? = some fn.ops[g] := Array.getElem?_eq_getElem hg
  rw [Array.getD_eq_getD_getElem?, hos, Option.getD_some] at ho
  have hv := hf.nv_ops g _ hos o (by simpa using ho)
  have hsl : opSlot o ≤ 3 := by unfold opSlot; split <;> omega
  split <;> exact spillPlan_covI.mpr ⟨hv, by simp only [pos]; omega⟩

private theorem claimsOk_spill : (LinearScan.Ctx.ofPlan fn fn.spillPlan).claimsOk = true := by
  simp only [LinearScan.Ctx.claimsOk, LinearScan.Ctx.ofPlan, List.all_eq_true, List.mem_range,
    Bool.and_eq_true, Array.all_eq_true_iff_forall_mem]
  intro g hg
  have hok := (spillPlan_opsOk hf hloc (hf.ops_size ▸ hg)).1
  refine ⟨fun o ho => ?_, fun r _ => ?_⟩
  · split
    · rename_i p hp
      obtain ⟨hal, -⟩ := hok.fixedReg o (by simpa using ho) p hp
      have hi := allocatable_idx p (List.contains_iff_mem.mp hal)
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hi
      simp only [hi, spillPlan_occ, meetsOther_nil, Bool.not_false]
    · rfl
  · split
    · simp only [spillPlan_occ, spillPlan_segFree_nil]
    · rfl

end

/-! ## Homes -/

section
variable {fn : Fn}

private theorem getD_modify {α : Type} (a : Array (List α)) (j i : Nat) (f : List α → List α) :
    (a.modify j f).getD i [] = if j = i ∧ i < a.size then f (a.getD i []) else a.getD i [] := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hji : j = i
  · subst hji
    by_cases hi : j < a.size <;> simp [hi]
  · simp [hji]

/-- The key of `Plan.homeOcc` for vreg `v` of the all-spill plan. -/
private def hkey (fn : Fn) (v : Nat) : Nat := 2 * v + (if fn.clsOf v == .float then 1 else 0)

private theorem hkey_inj {v w : Nat} (h : hkey fn v = hkey fn w) : v = w := by
  unfold hkey at h
  generalize fn.clsOf v = a at h
  generalize fn.clsOf w = b at h
  cases a <;> cases b <;> simp at h <;> omega

/-- The home fold of the all-spill plan puts at most one segment in each entry. -/
private theorem homeFold :
    ∀ n, n ≤ fn.nv →
      ∀ i, (((List.range n).foldl (fun (acc : Array (List LinearScan.Seg)) v =>
        if (fn.spillPlan.regOf v).isSome then acc else
          acc.modify (2 * fn.spillPlan.home.getD v 0 + (if fn.clsOf v == .float then 1 else 0))
            (fn.spillPlan.segList v ++ ·)) (Array.replicate (2 * fn.spillPlan.nslots) [])).getD i []).length ≤ 1 ∧
        ((((List.range n).foldl (fun (acc : Array (List LinearScan.Seg)) v =>
        if (fn.spillPlan.regOf v).isSome then acc else
          acc.modify (2 * fn.spillPlan.home.getD v 0 + (if fn.clsOf v == .float then 1 else 0))
            (fn.spillPlan.segList v ++ ·)) (Array.replicate (2 * fn.spillPlan.nslots) [])).getD i []) ≠ [] →
          ∃ v < n, hkey fn v = i)
  | 0, _, i => by
    simp only [List.range_zero, List.foldl_nil, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> simp
  | n + 1, hn, i => by
    have ih := homeFold n (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl _ _ = acc at ih ⊢
    simp only [spillPlan_regOf, Option.isSome_none, Bool.false_eq_true, ite_false,
      spillPlan_home (show n < fn.nv by omega)]
    rw [getD_modify]
    have hseg : (fn.spillPlan.segList n).length = 1 := by
      rw [Plan.segList, segs_getD, ite_eq_left (show n < fn.nv by omega)]; rfl
    generalize hK : 2 * n + (if fn.clsOf n == .float then 1 else 0) = K
    have hK' : hkey fn n = K := hK
    by_cases hj : K = i ∧ i < acc.size
    · rw [ite_eq_left hj]
      obtain ⟨hj, -⟩ := hj
      subst hj
      obtain ⟨-, h2⟩ := ih K
      cases hL : acc.getD K [] with
      | nil =>
        rw [List.append_nil, hseg]
        exact ⟨Nat.le_refl _, fun _ => ⟨n, by omega, hK'⟩⟩
      | cons x xs =>
        exfalso
        obtain ⟨w, hw, he⟩ := h2 (by rw [hL]; exact List.cons_ne_nil _ _)
        have := hkey_inj (fn := fn) (he.trans hK'.symm)
        omega
    · rw [ite_eq_right hj]
      obtain ⟨h1, h2⟩ := ih i
      exact ⟨h1, fun h => (h2 h).imp fun w ⟨hw, he⟩ => ⟨by omega, he⟩⟩

private theorem disjointSorted_short {l : List LinearScan.Seg} (h : l.length ≤ 1) :
    disjointSorted (sortSegs l) = true := by
  have hl : (l.mergeSort fun a b => decide (a.s ≤ b.s)).length ≤ 1 := by
    rw [List.length_mergeSort]; exact h
  unfold sortSegs disjointSorted
  generalize (l.mergeSort fun a b => decide (a.s ≤ b.s)) = m at hl
  rcases m with _ | ⟨x, _ | ⟨y, m⟩⟩
  · rfl
  · rfl
  · simp at hl

variable {vc : VCode} (hf : FnOk vc fn) (hloc : SpillLocalOk vc)
include hf hloc

omit hf hloc in
private theorem homesOk_spill : (LinearScan.Ctx.ofPlan fn fn.spillPlan).homesOk = true := by
  simp only [LinearScan.Ctx.homesOk, LinearScan.Ctx.ofPlan, Bool.and_eq_true, List.all_eq_true,
    List.mem_range]
  refine ⟨fun v hv => ?_, ?_⟩
  · simp [Fn.spillPlan, hv]
  · have hall := homeFold (fn := fn) fn.nv (Nat.le_refl _)
    simp only [Plan.homeOcc, Array.all_eq_true_iff_forall_mem, Array.mem_map]
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hl
    refine disjointSorted_short ?_
    have := (hall i).1
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some] at this
    exact this

/-- **The all-spill plan passes the validator.** -/
theorem spillPlan_structOk : (LinearScan.Ctx.ofPlan fn fn.spillPlan).structOk = true := by
  simp only [LinearScan.Ctx.structOk, segsOk_spill hf hloc, usesOk_spill hf,
    regsOk_spill, occOk_spill, homesOk_spill, claimsOk_spill hf hloc,
    defUseOk_spill, Bool.and_self]

end

end Backend.Proof.LS
